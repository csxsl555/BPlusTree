#include "storage/index/b_plus_tree.h"

#include <sstream>
#include <string>

#include "buffer/lru_k_replacer.h"
#include "common/config.h"
#include "common/exception.h"
#include "common/logger.h"
#include "common/macros.h"
#include "common/rid.h"
#include "storage/index/index_iterator.h"
#include "storage/page/b_plus_tree_header_page.h"
#include "storage/page/b_plus_tree_internal_page.h"
#include "storage/page/b_plus_tree_leaf_page.h"
#include "storage/page/b_plus_tree_page.h"
#include "storage/page/page_guard.h"

namespace bustub {

    INDEX_TEMPLATE_ARGUMENTS
    BPLUSTREE_TYPE::BPlusTree(std::string name, page_id_t header_page_id,
                              BufferPoolManager *buffer_pool_manager,
                              const KeyComparator &comparator, int leaf_max_size,
                              int internal_max_size)
        : index_name_(std::move(name)),
          bpm_(buffer_pool_manager),
          comparator_(std::move(comparator)),
          leaf_max_size_(leaf_max_size),
          internal_max_size_(internal_max_size),
          header_page_id_(header_page_id) {
        WritePageGuard guard = bpm_->FetchPageWrite(header_page_id_);
        // In the original bpt, I fetch the header page
        // thus there's at least one page now
        auto root_header_page = guard.template AsMut<BPlusTreeHeaderPage>();
        // reinterprete the data of the page into "HeaderPage"
        root_header_page->root_page_id_ = INVALID_PAGE_ID;
        // set the root_id to INVALID
    }

    /*
     * Helper function to decide whether current b+tree is empty
     */
    INDEX_TEMPLATE_ARGUMENTS
    auto BPLUSTREE_TYPE::IsEmpty() const -> bool {
        ReadPageGuard guard = bpm_->FetchPageRead(header_page_id_);
        auto root_header_page = guard.template As<BPlusTreeHeaderPage>();
        bool is_empty = root_header_page->root_page_id_ == INVALID_PAGE_ID;
        // Just check if the root_page_id is INVALID
        // usage to fetch a page:
        // fetch the page guard   ->   call the "As" function of the page guard
        // to reinterprete the data of the page as "BPlusTreePage"
        return is_empty;
    }
    /*****************************************************************************
     * SEARCH
     *****************************************************************************/
    /*
     * Return the only value that associated with input key
     * This method is used for point query
     * @return : true means key exists
     */
    INDEX_TEMPLATE_ARGUMENTS
    auto BPLUSTREE_TYPE::GetValue(const KeyType &key,
                                  std::vector<ValueType> *result, Transaction *txn)
        -> bool {
        ReadPageGuard head_guard = bpm_->FetchPageRead(header_page_id_);
        auto header_page = head_guard.template As<BPlusTreeHeaderPage>()->root_page_id_;

        if (header_page == INVALID_PAGE_ID) {
            return false;
        }

        ReadPageGuard guard = bpm_->FetchPageRead(header_page);
        head_guard.Drop();

        auto tmp_page = guard.template As<BPlusTreePage>();
        while (!tmp_page->IsLeafPage()) {
            auto internal = reinterpret_cast<const InternalPage *>(tmp_page);
            int slot_num = BinaryFind(internal, key);
            guard = bpm_->FetchPageRead(internal->ValueAt(slot_num));
            tmp_page = guard.template As<BPlusTreePage>();
        }
        auto *leaf_page = reinterpret_cast<const LeafPage *>(tmp_page);

        int slot_num = BinaryFind(leaf_page, key);
        if (slot_num == -1 || comparator_(leaf_page->KeyAt(slot_num), key) != 0)
            return false;
        result->push_back(leaf_page->ValueAt(slot_num));
        return true;
    }

    /*****************************************************************************
     * INSERTION
     *****************************************************************************/
    /*
     * Insert constant key & value pair into b+ tree
     * if current tree is empty, start new tree, update root page id and insert
     * entry, otherwise insert into leaf page.
     * @return: since we only support unique key, if user try to insert duplicate
     * keys return false, otherwise return true.
     */

    INDEX_TEMPLATE_ARGUMENTS
    auto BPLUSTREE_TYPE::Insert(const KeyType &key, const ValueType &value,
                                Transaction *txn) -> bool {
        if (IsEmpty()) {
            page_id_t new_page_id;
            auto basic_guard = bpm_->NewPageGuarded(&new_page_id);
            auto leaf = basic_guard.template AsMut<LeafPage>();
            leaf->Init(leaf_max_size_);
            leaf->SetKeyAt(0, key);
            leaf->SetValueAt(0, value);
            leaf->IncreaseSize(1);

            auto header_guard = bpm_->FetchPageWrite(header_page_id_);
            header_guard.AsMut<BPlusTreeHeaderPage>()->root_page_id_ = new_page_id;
            // header_guard 析构时自动 Unpin

            return true;
        }

        // find leaf to insert

        WritePageGuard head_guard = bpm_->FetchPageWrite(header_page_id_);
        auto root_page_id = head_guard.As<BPlusTreeHeaderPage>()->root_page_id_;
        std::deque<WritePageGuard> path;

        path.push_back(std::move(head_guard));
        WritePageGuard root_guard = bpm_->FetchPageWrite(root_page_id);
        path.push_back(std::move(root_guard));
        auto tmp_page = path.back().template AsMut<BPlusTreePage>();
        while (!tmp_page->IsLeafPage()) {
            auto internal = reinterpret_cast<const InternalPage *>(tmp_page);
            int slot_num = BinaryFind(internal, key);
            WritePageGuard child_guard = bpm_->FetchPageWrite(internal->ValueAt(slot_num));
            path.push_back(std::move(child_guard));
            tmp_page = path.back().template AsMut<BPlusTreePage>();
        }

        // insert leaf

        auto *leaf_page = reinterpret_cast<LeafPage *>(tmp_page);
        int slot_num = BinaryFind(leaf_page, key);

        if (slot_num != -1 && comparator_(leaf_page->KeyAt(slot_num), key) == 0) {
            return false;
        }

        int idx = slot_num + 1;
        int old_size = leaf_page->GetSize();
        leaf_page->IncreaseSize(1);

        for (int i = old_size; i > idx; --i) {
            leaf_page->SetKeyAt(i, leaf_page->KeyAt(i - 1));
            leaf_page->SetValueAt(i, leaf_page->ValueAt(i - 1));
        }

        leaf_page->SetKeyAt(idx, key);
        leaf_page->SetValueAt(idx, value);

        if (old_size + 1 <= leaf_max_size_)
            return true;

        // split leaf

        page_id_t new_page_id;
        auto basic_guard = bpm_->NewPageGuarded(&new_page_id);
        auto new_leaf = basic_guard.template AsMut<LeafPage>();
        new_leaf->Init(leaf_max_size_);

        int new_size = (old_size + 1) >> 1;
        old_size = old_size + 1 - new_size;
        leaf_page->SetSize(old_size);
        new_leaf->SetSize(new_size);

        for (int i = 0; i < new_size; ++i) {
            new_leaf->SetKeyAt(i, leaf_page->KeyAt(old_size + i));
            new_leaf->SetValueAt(i, leaf_page->ValueAt(old_size + i));
        }

        new_leaf->SetNextPageId(leaf_page->GetNextPageId());
        leaf_page->SetNextPageId(new_page_id);

        KeyType split_key = new_leaf->KeyAt(0);
        page_id_t right_page_id = new_page_id;

        path.pop_back();

        while (true) {
            if (path.size() == 1) {
                auto header_page = path[0].AsMut<BPlusTreeHeaderPage>();
                page_id_t old_root_id = header_page->root_page_id_;

                page_id_t new_root_id;
                auto root_guard = bpm_->NewPageGuarded(&new_root_id);
                auto new_root = root_guard.template AsMut<InternalPage>();
                new_root->Init(internal_max_size_);
                new_root->SetValueAt(0, old_root_id);
                new_root->SetKeyAt(1, split_key);
                new_root->SetValueAt(1, right_page_id);
                new_root->SetSize(2);

                header_page->root_page_id_ = new_root_id;
                break;
            }

            auto parent = reinterpret_cast<InternalPage *>(path.back().AsMut<BPlusTreePage>());

            int insert_pos = BinaryFind(parent, split_key) + 1;

            int parent_size = parent->GetSize();
            parent->IncreaseSize(1);
            for (int i = parent_size; i > insert_pos; --i) {
                parent->SetKeyAt(i, parent->KeyAt(i - 1));
                parent->SetValueAt(i, parent->ValueAt(i - 1));
            }
            parent->SetKeyAt(insert_pos, split_key);
            parent->SetValueAt(insert_pos, right_page_id);

            if (parent_size + 1 <= internal_max_size_) {
                break;
            }

            // split internal page
            page_id_t new_internal_id;
            auto internal_guard = bpm_->NewPageGuarded(&new_internal_id);
            auto new_internal = internal_guard.template AsMut<InternalPage>();
            new_internal->Init(internal_max_size_);

            int total = parent_size + 1;
            int mid = total / 2;

            parent->SetSize(mid);

            split_key = parent->KeyAt(mid);

            int right_entries = total - mid - 1;
            new_internal->SetSize(right_entries + 1);
            new_internal->SetValueAt(0, parent->ValueAt(mid));
            for (int i = 1; i <= right_entries; i++) {
                new_internal->SetKeyAt(i, parent->KeyAt(mid + i));
                new_internal->SetValueAt(i, parent->ValueAt(mid + i));
            }

            right_page_id = new_internal_id;
            path.pop_back();
        }

        return true;
    }

    /*****************************************************************************
     * REMOVE
     *****************************************************************************/
    /*
     * Delete key & value pair associated with input key
     * If current tree is empty, return immediately.
     * If not, User needs to first find the right leaf page as deletion target, then
     * delete entry from leaf page. Remember to deal with redistribute or merge if
     * necessary.
     */

    INDEX_TEMPLATE_ARGUMENTS
    void BPLUSTREE_TYPE::Remove(const KeyType &key, Transaction *txn) {
        if (IsEmpty())
            return;

        // find leaf to delete
        WritePageGuard head_guard = bpm_->FetchPageWrite(header_page_id_);
        auto root_page_id = head_guard.As<BPlusTreeHeaderPage>()->root_page_id_;
        std::deque<WritePageGuard> path;

        path.push_back(std::move(head_guard));
        WritePageGuard root_guard = bpm_->FetchPageWrite(root_page_id);
        path.push_back(std::move(root_guard));
        auto tmp_page = path.back().template AsMut<BPlusTreePage>();
        while (!tmp_page->IsLeafPage()) {
            auto internal = reinterpret_cast<const InternalPage *>(tmp_page);
            int slot_num = BinaryFind(internal, key);
            WritePageGuard child_guard = bpm_->FetchPageWrite(internal->ValueAt(slot_num));
            path.push_back(std::move(child_guard));
            tmp_page = path.back().template AsMut<BPlusTreePage>();
        }

        // delete leaf

        auto *leaf_page = reinterpret_cast<LeafPage *>(tmp_page);
        int slot_num = BinaryFind(leaf_page, key);

        if (slot_num == -1 || comparator_(leaf_page->KeyAt(slot_num), key) != 0)
            return;

        int idx = slot_num;
        int old_size = leaf_page->GetSize();

        for (int i = idx; i < old_size - 1; ++i) {
            leaf_page->SetKeyAt(i, leaf_page->KeyAt(i + 1));
            leaf_page->SetValueAt(i, leaf_page->ValueAt(i + 1));
        }

        leaf_page->IncreaseSize(-1);

        if (old_size - 1 >= leaf_page->GetMinSize())
            return;

        // Union

        page_id_t child_page_id = path.back().PageId();
        path.pop_back();

        auto ShiftRight = [](auto *page, int size) {
            for (int i = size; i > 0; --i) {
                page->SetKeyAt(i, page->KeyAt(i - 1));
                page->SetValueAt(i, page->ValueAt(i - 1));
            }
        };
        auto ShiftLeft = [](auto *page, int size) {
            for (int i = 0; i < size - 1; ++i) {
                page->SetKeyAt(i, page->KeyAt(i + 1));
                page->SetValueAt(i, page->ValueAt(i + 1));
            }
        };
        auto RemoveFromParent = [](InternalPage *p, int idx) {
            int sz = p->GetSize();
            for (int i = idx; i < sz - 1; ++i) {
                p->SetKeyAt(i, p->KeyAt(i + 1));
                p->SetValueAt(i, p->ValueAt(i + 1));
            }
            p->IncreaseSize(-1);
        };

        while (true) {
            if (path.size() == 1) {
                auto header_page = path[0].AsMut<BPlusTreeHeaderPage>();
                page_id_t old_root_id = header_page->root_page_id_;

                auto root_guard = bpm_->FetchPageWrite(old_root_id);
                auto root_page = root_guard.template AsMut<BPlusTreePage>();

                if (root_page->IsLeafPage()) {
                    if (root_page->GetSize() == 0) {
                        header_page->root_page_id_ = INVALID_PAGE_ID;
                    }
                } else {
                    auto root_internal = reinterpret_cast<InternalPage *>(root_page);
                    if (root_internal->GetSize() == 1) {
                        header_page->root_page_id_ = root_internal->ValueAt(0);
                    }
                }
                break;
            }

            auto parent = reinterpret_cast<InternalPage *>(path.back().template AsMut<BPlusTreePage>());
            int slot_num = BinaryFind(parent, key);
            int left_brother_num = slot_num - 1, right_brother_num = slot_num + 1;

            // borrow from left sibling
            if (left_brother_num >= 0) {
                WritePageGuard brother_guard = bpm_->FetchPageWrite(parent->ValueAt(left_brother_num));
                auto left_page = brother_guard.template AsMut<BPlusTreePage>();
                if (left_page->GetSize() > left_page->GetMinSize()) {
                    WritePageGuard child_guard = bpm_->FetchPageWrite(child_page_id);
                    auto child_page = child_guard.template AsMut<BPlusTreePage>();
                    int left_last = left_page->GetSize() - 1;

                    if (child_page->IsLeafPage()) {
                        auto child_leaf = reinterpret_cast<LeafPage *>(child_page);
                        auto left_leaf = reinterpret_cast<LeafPage *>(left_page);
                        ShiftRight(child_leaf, child_leaf->GetSize());
                        child_leaf->SetKeyAt(0, left_leaf->KeyAt(left_last));
                        child_leaf->SetValueAt(0, left_leaf->ValueAt(left_last));
                        child_leaf->IncreaseSize(1);
                        left_leaf->IncreaseSize(-1);
                        parent->SetKeyAt(slot_num, child_leaf->KeyAt(0));
                    } else {
                        auto child_internal = reinterpret_cast<InternalPage *>(child_page);
                        auto left_internal = reinterpret_cast<InternalPage *>(left_page);
                        ShiftRight(child_internal, child_internal->GetSize());
                        child_internal->SetValueAt(0, left_internal->ValueAt(left_last));
                        child_internal->SetKeyAt(1, parent->KeyAt(slot_num));
                        child_internal->IncreaseSize(1);
                        left_internal->IncreaseSize(-1);
                        parent->SetKeyAt(slot_num, left_internal->KeyAt(left_last));
                    }
                    break;
                }
            }

            // borrow from right sibling
            if (right_brother_num < parent->GetSize()) {
                WritePageGuard brother_guard = bpm_->FetchPageWrite(parent->ValueAt(right_brother_num));
                auto right_page = brother_guard.template AsMut<BPlusTreePage>();
                if (right_page->GetSize() > right_page->GetMinSize()) {
                    WritePageGuard child_guard = bpm_->FetchPageWrite(child_page_id);
                    auto child_page = child_guard.template AsMut<BPlusTreePage>();

                    if (child_page->IsLeafPage()) {
                        auto child_leaf = reinterpret_cast<LeafPage *>(child_page);
                        auto right_leaf = reinterpret_cast<LeafPage *>(right_page);
                        int child_sz = child_leaf->GetSize();
                        child_leaf->SetKeyAt(child_sz, right_leaf->KeyAt(0));
                        child_leaf->SetValueAt(child_sz, right_leaf->ValueAt(0));
                        child_leaf->IncreaseSize(1);
                        ShiftLeft(right_leaf, right_leaf->GetSize());
                        right_leaf->IncreaseSize(-1);
                        parent->SetKeyAt(right_brother_num, right_leaf->KeyAt(0));
                    } else {
                        auto child_internal = reinterpret_cast<InternalPage *>(child_page);
                        auto right_internal = reinterpret_cast<InternalPage *>(right_page);
                        int child_sz = child_internal->GetSize();
                        child_internal->SetKeyAt(child_sz, parent->KeyAt(right_brother_num));
                        child_internal->SetValueAt(child_sz, right_internal->ValueAt(0));
                        child_internal->IncreaseSize(1);
                        parent->SetKeyAt(right_brother_num, right_internal->KeyAt(1));
                        ShiftLeft(right_internal, right_internal->GetSize());
                        right_internal->IncreaseSize(-1);
                    }
                    break;
                }
            }

            // merge with a sibling
            if (left_brother_num >= 0) {
                WritePageGuard brother_guard = bpm_->FetchPageWrite(parent->ValueAt(left_brother_num));
                auto left_page = brother_guard.template AsMut<BPlusTreePage>();
                WritePageGuard child_guard = bpm_->FetchPageWrite(child_page_id);
                auto child_page = child_guard.template AsMut<BPlusTreePage>();

                if (child_page->IsLeafPage()) {
                    auto child_leaf = reinterpret_cast<LeafPage *>(child_page);
                    auto left_leaf = reinterpret_cast<LeafPage *>(left_page);
                    int left_sz = left_leaf->GetSize();
                    int child_sz = child_leaf->GetSize();
                    for (int i = 0; i < child_sz; ++i) {
                        left_leaf->SetKeyAt(left_sz + i, child_leaf->KeyAt(i));
                        left_leaf->SetValueAt(left_sz + i, child_leaf->ValueAt(i));
                    }
                    left_leaf->SetSize(left_sz + child_sz);
                    left_leaf->SetNextPageId(child_leaf->GetNextPageId());
                } else {
                    auto child_internal = reinterpret_cast<InternalPage *>(child_page);
                    auto left_internal = reinterpret_cast<InternalPage *>(left_page);
                    int left_sz = left_internal->GetSize();
                    int child_sz = child_internal->GetSize();
                    left_internal->SetKeyAt(left_sz, parent->KeyAt(slot_num));
                    left_internal->SetValueAt(left_sz, child_internal->ValueAt(0));
                    for (int i = 1; i < child_sz; ++i) {
                        left_internal->SetKeyAt(left_sz + i, child_internal->KeyAt(i));
                        left_internal->SetValueAt(left_sz + i, child_internal->ValueAt(i));
                    }
                    left_internal->SetSize(left_sz + child_sz);
                }
                RemoveFromParent(parent, slot_num);
            } else {
                WritePageGuard child_guard = bpm_->FetchPageWrite(child_page_id);
                auto child_page = child_guard.template AsMut<BPlusTreePage>();
                WritePageGuard brother_guard = bpm_->FetchPageWrite(parent->ValueAt(right_brother_num));
                auto right_page = brother_guard.template AsMut<BPlusTreePage>();

                if (child_page->IsLeafPage()) {
                    auto child_leaf = reinterpret_cast<LeafPage *>(child_page);
                    auto right_leaf = reinterpret_cast<LeafPage *>(right_page);
                    int child_sz = child_leaf->GetSize();
                    int right_sz = right_leaf->GetSize();
                    for (int i = 0; i < right_sz; ++i) {
                        child_leaf->SetKeyAt(child_sz + i, right_leaf->KeyAt(i));
                        child_leaf->SetValueAt(child_sz + i, right_leaf->ValueAt(i));
                    }
                    child_leaf->SetSize(child_sz + right_sz);
                    child_leaf->SetNextPageId(right_leaf->GetNextPageId());
                } else {
                    auto child_internal = reinterpret_cast<InternalPage *>(child_page);
                    auto right_internal = reinterpret_cast<InternalPage *>(right_page);
                    int child_sz = child_internal->GetSize();
                    int right_sz = right_internal->GetSize();
                    child_internal->SetKeyAt(child_sz, parent->KeyAt(right_brother_num));
                    child_internal->SetValueAt(child_sz, right_internal->ValueAt(0));
                    for (int i = 1; i < right_sz; ++i) {
                        child_internal->SetKeyAt(child_sz + i, right_internal->KeyAt(i));
                        child_internal->SetValueAt(child_sz + i, right_internal->ValueAt(i));
                    }
                    child_internal->SetSize(child_sz + right_sz);
                }
                RemoveFromParent(parent, right_brother_num);
            }

            if (parent->GetSize() >= parent->GetMinSize())
                break;

            child_page_id = path.back().PageId();
            path.pop_back();
        }
    }

    /*****************************************************************************
     * INDEX ITERATOR
     *****************************************************************************/

    // return the max value that is <= key
    INDEX_TEMPLATE_ARGUMENTS
    auto BPLUSTREE_TYPE::BinaryFind(const LeafPage *leaf_page, const KeyType &key)
        -> int {
        int l = 0;
        int r = leaf_page->GetSize() - 1;
        while (l < r) {
            int mid = (l + r + 1) >> 1;
            if (comparator_(leaf_page->KeyAt(mid), key) != 1) {
                l = mid;
            } else {
                r = mid - 1;
            }
        }

        if (r >= 0 && comparator_(leaf_page->KeyAt(r), key) == 1) {
            r = -1;
        }

        return r;
    }

    // return the max value that is <= key
    INDEX_TEMPLATE_ARGUMENTS
    auto BPLUSTREE_TYPE::BinaryFind(const InternalPage *internal_page,
                                    const KeyType &key) -> int {
        int l = 1;
        int r = internal_page->GetSize() - 1;
        while (l < r) {
            int mid = (l + r + 1) >> 1;
            if (comparator_(internal_page->KeyAt(mid), key) != 1) {
                l = mid;
            } else {
                r = mid - 1;
            }
        }

        if (r == -1 || comparator_(internal_page->KeyAt(r), key) == 1) {
            r = 0;
        }

        return r;
    }

    /*
     * Input parameter is void, find the leftmost leaf page first, then construct
     * index iterator
     * @return : index iterator
     */
    INDEX_TEMPLATE_ARGUMENTS
    auto BPLUSTREE_TYPE::Begin() -> INDEXITERATOR_TYPE
    // Just go left forever
    {
        ReadPageGuard head_guard = bpm_->FetchPageRead(header_page_id_);
        if (head_guard.template As<BPlusTreeHeaderPage>()->root_page_id_ == INVALID_PAGE_ID) {
            return End();
        }
        ReadPageGuard guard = bpm_->FetchPageRead(head_guard.As<BPlusTreeHeaderPage>()->root_page_id_);
        head_guard.Drop();

        auto tmp_page = guard.template As<BPlusTreePage>();
        while (!tmp_page->IsLeafPage()) {
            int slot_num = 0;
            guard = bpm_->FetchPageRead(reinterpret_cast<const InternalPage *>(tmp_page)->ValueAt(slot_num));
            tmp_page = guard.template As<BPlusTreePage>();
        }
        int slot_num = 0;
        if (slot_num != -1) {
            return INDEXITERATOR_TYPE(bpm_, guard.PageId(), 0);
        }
        return End();
    }

    /*
     * Input parameter is low key, find the leaf page that contains the input key
     * first, then construct index iterator
     * @return : index iterator
     */
    INDEX_TEMPLATE_ARGUMENTS
    auto BPLUSTREE_TYPE::Begin(const KeyType &key) -> INDEXITERATOR_TYPE {
        ReadPageGuard head_guard = bpm_->FetchPageRead(header_page_id_);

        if (head_guard.template As<BPlusTreeHeaderPage>()->root_page_id_ == INVALID_PAGE_ID) {
            return End();
        }
        ReadPageGuard guard = bpm_->FetchPageRead(head_guard.As<BPlusTreeHeaderPage>()->root_page_id_);
        head_guard.Drop();
        auto tmp_page = guard.template As<BPlusTreePage>();
        while (!tmp_page->IsLeafPage()) {
            auto internal = reinterpret_cast<const InternalPage *>(tmp_page);
            int slot_num = BinaryFind(internal, key);
            if (slot_num == -1) {
                return End();
            }
            guard = bpm_->FetchPageRead(reinterpret_cast<const InternalPage *>(tmp_page)->ValueAt(slot_num));
            tmp_page = guard.template As<BPlusTreePage>();
        }
        auto *leaf_page = reinterpret_cast<const LeafPage *>(tmp_page);

        int slot_num = BinaryFind(leaf_page, key);
        if (slot_num != -1) {
            return INDEXITERATOR_TYPE(bpm_, guard.PageId(), slot_num);
        }
        return End();
    }

    /*
     * Input parameter is void, construct an index iterator representing the end
     * of the key/value pair in the leaf node
     * @return : index iterator
     */
    INDEX_TEMPLATE_ARGUMENTS
    auto BPLUSTREE_TYPE::End() -> INDEXITERATOR_TYPE {
        return INDEXITERATOR_TYPE(bpm_, -1, -1);
    }

    /**
     * @return Page id of the root of this tree
     */
    INDEX_TEMPLATE_ARGUMENTS
    auto BPLUSTREE_TYPE::GetRootPageId() -> page_id_t {
        ReadPageGuard guard = bpm_->FetchPageRead(header_page_id_);
        auto root_header_page = guard.template As<BPlusTreeHeaderPage>();
        page_id_t root_page_id = root_header_page->root_page_id_;
        return root_page_id;
    }

    /*****************************************************************************
     * UTILITIES AND DEBUG
     *****************************************************************************/

    /*
     * This method is used for test only
     * Read data from file and insert one by one
     */
    INDEX_TEMPLATE_ARGUMENTS
    void BPLUSTREE_TYPE::InsertFromFile(const std::string &file_name,
                                        Transaction *txn) {
        int64_t key;
        std::ifstream input(file_name);
        while (input >> key) {
            KeyType index_key;
            index_key.SetFromInteger(key);
            RID rid(key);
            Insert(index_key, rid, txn);
        }
    }
    /*
     * This method is used for test only
     * Read data from file and remove one by one
     */
    INDEX_TEMPLATE_ARGUMENTS
    void BPLUSTREE_TYPE::RemoveFromFile(const std::string &file_name,
                                        Transaction *txn) {
        int64_t key;
        std::ifstream input(file_name);
        while (input >> key) {
            KeyType index_key;
            index_key.SetFromInteger(key);
            Remove(index_key, txn);
        }
    }

    /*
     * This method is used for test only
     * Read data from file and insert/remove one by one
     */
    INDEX_TEMPLATE_ARGUMENTS
    void BPLUSTREE_TYPE::BatchOpsFromFile(const std::string &file_name,
                                          Transaction *txn) {
        int64_t key;
        char instruction;
        std::ifstream input(file_name);
        while (input) {
            input >> instruction >> key;
            RID rid(key);
            KeyType index_key;
            index_key.SetFromInteger(key);
            switch (instruction) {
            case 'i':
                Insert(index_key, rid, txn);
                break;
            case 'd':
                Remove(index_key, txn);
                break;
            default:
                break;
            }
        }
    }

    INDEX_TEMPLATE_ARGUMENTS
    void BPLUSTREE_TYPE::Print(BufferPoolManager *bpm) {
        auto root_page_id = GetRootPageId();
        auto guard = bpm->FetchPageBasic(root_page_id);
        PrintTree(guard.PageId(), guard.template As<BPlusTreePage>());
    }

    INDEX_TEMPLATE_ARGUMENTS
    void BPLUSTREE_TYPE::PrintTree(page_id_t page_id, const BPlusTreePage *page) {
        if (page->IsLeafPage()) {
            auto *leaf = reinterpret_cast<const LeafPage *>(page);
            std::cout << "Leaf Page: " << page_id << "\tNext: " << leaf->GetNextPageId() << std::endl;

            // Print the contents of the leaf page.
            std::cout << "Contents: ";
            for (int i = 0; i < leaf->GetSize(); i++) {
                std::cout << leaf->KeyAt(i);
                if ((i + 1) < leaf->GetSize()) {
                    std::cout << ", ";
                }
            }
            std::cout << std::endl;
            std::cout << std::endl;
        } else {
            auto *internal = reinterpret_cast<const InternalPage *>(page);
            std::cout << "Internal Page: " << page_id << std::endl;

            // Print the contents of the internal page.
            std::cout << "Contents: ";
            for (int i = 0; i < internal->GetSize(); i++) {
                std::cout << internal->KeyAt(i) << ": " << internal->ValueAt(i);
                if ((i + 1) < internal->GetSize()) {
                    std::cout << ", ";
                }
            }
            std::cout << std::endl;
            std::cout << std::endl;
            for (int i = 0; i < internal->GetSize(); i++) {
                auto guard = bpm_->FetchPageBasic(internal->ValueAt(i));
                PrintTree(guard.PageId(), guard.template As<BPlusTreePage>());
            }
        }
    }

    /**
     * This method is used for debug only, You don't need to modify
     */
    INDEX_TEMPLATE_ARGUMENTS
    void BPLUSTREE_TYPE::Draw(BufferPoolManager *bpm, const std::string &outf) {
        if (IsEmpty()) {
            LOG_WARN("Drawing an empty tree");
            return;
        }

        std::ofstream out(outf);
        out << "digraph G {" << std::endl;
        auto root_page_id = GetRootPageId();
        auto guard = bpm->FetchPageBasic(root_page_id);
        ToGraph(guard.PageId(), guard.template As<BPlusTreePage>(), out);
        out << "}" << std::endl;
        out.close();
    }

    /**
     * This method is used for debug only, You don't need to modify
     */
    INDEX_TEMPLATE_ARGUMENTS
    void BPLUSTREE_TYPE::ToGraph(page_id_t page_id, const BPlusTreePage *page,
                                 std::ofstream &out) {
        std::string leaf_prefix("LEAF_");
        std::string internal_prefix("INT_");
        if (page->IsLeafPage()) {
            auto *leaf = reinterpret_cast<const LeafPage *>(page);
            // Print node name
            out << leaf_prefix << page_id;
            // Print node properties
            out << "[shape=plain color=green ";
            // Print data of the node
            out << "label=<<TABLE BORDER=\"0\" CELLBORDER=\"1\" CELLSPACING=\"0\" "
                   "CELLPADDING=\"4\">\n";
            // Print data
            out << "<TR><TD COLSPAN=\"" << leaf->GetSize() << "\">P=" << page_id
                << "</TD></TR>\n";
            out << "<TR><TD COLSPAN=\"" << leaf->GetSize() << "\">"
                << "max_size=" << leaf->GetMaxSize()
                << ",min_size=" << leaf->GetMinSize() << ",size=" << leaf->GetSize()
                << "</TD></TR>\n";
            out << "<TR>";
            for (int i = 0; i < leaf->GetSize(); i++) {
                out << "<TD>" << leaf->KeyAt(i) << "</TD>\n";
            }
            out << "</TR>";
            // Print table end
            out << "</TABLE>>];\n";
            // Print Leaf node link if there is a next page
            if (leaf->GetNextPageId() != INVALID_PAGE_ID) {
                out << leaf_prefix << page_id << "   ->   " << leaf_prefix
                    << leaf->GetNextPageId() << ";\n";
                out << "{rank=same " << leaf_prefix << page_id << " " << leaf_prefix
                    << leaf->GetNextPageId() << "};\n";
            }
        } else {
            auto *inner = reinterpret_cast<const InternalPage *>(page);
            // Print node name
            out << internal_prefix << page_id;
            // Print node properties
            out << "[shape=plain color=pink "; // why not?
            // Print data of the node
            out << "label=<<TABLE BORDER=\"0\" CELLBORDER=\"1\" CELLSPACING=\"0\" "
                   "CELLPADDING=\"4\">\n";
            // Print data
            out << "<TR><TD COLSPAN=\"" << inner->GetSize() << "\">P=" << page_id
                << "</TD></TR>\n";
            out << "<TR><TD COLSPAN=\"" << inner->GetSize() << "\">"
                << "max_size=" << inner->GetMaxSize()
                << ",min_size=" << inner->GetMinSize() << ",size=" << inner->GetSize()
                << "</TD></TR>\n";
            out << "<TR>";
            for (int i = 0; i < inner->GetSize(); i++) {
                out << "<TD PORT=\"p" << inner->ValueAt(i) << "\">";
                // if (i > 0) {
                out << inner->KeyAt(i) << "  " << inner->ValueAt(i);
                // } else {
                // out << inner  ->  ValueAt(0);
                // }
                out << "</TD>\n";
            }
            out << "</TR>";
            // Print table end
            out << "</TABLE>>];\n";
            // Print leaves
            for (int i = 0; i < inner->GetSize(); i++) {
                auto child_guard = bpm_->FetchPageBasic(inner->ValueAt(i));
                auto child_page = child_guard.template As<BPlusTreePage>();
                ToGraph(child_guard.PageId(), child_page, out);
                if (i > 0) {
                    auto sibling_guard = bpm_->FetchPageBasic(inner->ValueAt(i - 1));
                    auto sibling_page = sibling_guard.template As<BPlusTreePage>();
                    if (!sibling_page->IsLeafPage() && !child_page->IsLeafPage()) {
                        out << "{rank=same " << internal_prefix << sibling_guard.PageId()
                            << " " << internal_prefix << child_guard.PageId() << "};\n";
                    }
                }
                out << internal_prefix << page_id << ":p" << child_guard.PageId()
                    << "   ->   ";
                if (child_page->IsLeafPage()) {
                    out << leaf_prefix << child_guard.PageId() << ";\n";
                } else {
                    out << internal_prefix << child_guard.PageId() << ";\n";
                }
            }
        }
    }

    INDEX_TEMPLATE_ARGUMENTS
    auto BPLUSTREE_TYPE::DrawBPlusTree() -> std::string {
        if (IsEmpty()) {
            return "()";
        }

        PrintableBPlusTree p_root = ToPrintableBPlusTree(GetRootPageId());
        std::ostringstream out_buf;
        p_root.Print(out_buf);

        return out_buf.str();
    }

    INDEX_TEMPLATE_ARGUMENTS
    auto BPLUSTREE_TYPE::ToPrintableBPlusTree(page_id_t root_id)
        -> PrintableBPlusTree {
        auto root_page_guard = bpm_->FetchPageBasic(root_id);
        auto root_page = root_page_guard.template As<BPlusTreePage>();
        PrintableBPlusTree proot;

        if (root_page->IsLeafPage()) {
            auto leaf_page = root_page_guard.template As<LeafPage>();
            proot.keys_ = leaf_page->ToString();
            proot.size_ = proot.keys_.size() + 4; // 4 more spaces for indent

            return proot;
        }

        // draw internal page
        auto internal_page = root_page_guard.template As<InternalPage>();
        proot.keys_ = internal_page->ToString();
        proot.size_ = 0;
        for (int i = 0; i < internal_page->GetSize(); i++) {
            page_id_t child_id = internal_page->ValueAt(i);
            PrintableBPlusTree child_node = ToPrintableBPlusTree(child_id);
            proot.size_ += child_node.size_;
            proot.children_.push_back(child_node);
        }

        return proot;
    }

    template class BPlusTree<GenericKey<4>, RID, GenericComparator<4>>;

    template class BPlusTree<GenericKey<8>, RID, GenericComparator<8>>;

    template class BPlusTree<GenericKey<16>, RID, GenericComparator<16>>;

    template class BPlusTree<GenericKey<32>, RID, GenericComparator<32>>;

    template class BPlusTree<GenericKey<64>, RID, GenericComparator<64>>;

} // namespace bustub
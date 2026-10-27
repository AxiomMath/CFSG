module

public import CFSG.Blueprint.NativeSporadic
public import CFSG.Open.LocalVocabulary

public section

namespace CFSG.SectionRank

open CFSG.Blueprint
open scoped commutatorElement

@[expose] def mathieuWord {G : Type*} [Group G] (a b : G) : List Char → G
  | [] => 1
  | c :: w => (if c = 'a' then a else if c = 'b' then b else b⁻¹) * mathieuWord a b w

abbrev m12LocA : NativeSporadic.M12 :=
  ⟨List.formPerm [0, 3] * List.formPerm [2, 9] * List.formPerm [4, 10] * List.formPerm [5, 11],
    Subgroup.subset_closure (Set.mem_insert _ _)⟩

abbrev m12LocB : NativeSporadic.M12 :=
  ⟨List.formPerm [0, 7, 8] * List.formPerm [1, 2, 3] * List.formPerm [4, 11, 10] *
      List.formPerm [5, 9, 6],
    Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)⟩

@[expose] def m12WordX : String :=
    "abaBabaBaBaBaBabababababababa"

@[expose] def m12WordY : String :=
    "baBabababaBaBaaBababaBabababab"

@[expose] def m12WordH : String :=
    "aBabaBaBabababababababababab"

abbrev m24LocA : NativeSporadic.M24 :=
  ⟨List.formPerm [0, 3] * List.formPerm [1, 6] * List.formPerm [2, 16] * List.formPerm [4, 12] *
      List.formPerm [5, 8] * List.formPerm [7, 14] * List.formPerm [9, 18] *
      List.formPerm [10, 17] * List.formPerm [11, 20] * List.formPerm [13, 15] *
      List.formPerm [19, 23] * List.formPerm [21, 22],
    Subgroup.subset_closure (Set.mem_insert _ _)⟩

abbrev m24LocB : NativeSporadic.M24 :=
  ⟨List.formPerm [0, 3, 5] * List.formPerm [1, 20, 13] * List.formPerm [2, 8, 14] *
      List.formPerm [4, 17, 9] * List.formPerm [12, 16, 15] * List.formPerm [18, 23, 22],
    Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)⟩

@[expose] def m24WordX : String :=
    "BaBabaBababaBaBaBaBaBababababababaBbaBabaBaBabaBaBaBabaBabaBaBbaBaBababaBaBababa" ++
    "babababaBababaBaBabaaBaBaBababaBaBabaBaBababaBaBaba"

@[expose] def m24WordY : String :=
    "BababababababaBaBaBabaBaBabababababbaBaBaBabababababaBaBaBaBabaBabababa"

@[expose] def m24WordH : String :=
    "BababaBaBabaBababaBaBababaBaBabababaBaBabaBaBaBababaBaBaBab"

end CFSG.SectionRank

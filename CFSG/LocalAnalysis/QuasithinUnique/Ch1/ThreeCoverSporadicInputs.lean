
module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.LocalAnalysis.SectionRank.LargeRee.Weyl

public section

namespace CFSG.QuasithinUnique.Ch1
open CFSG.Blueprint CFSG.SectionRank

abbrev m11LocA : NativeSporadic.M11 :=
  ⟨List.formPerm [1, 9] * List.formPerm [3, 10] * List.formPerm [4, 6] * List.formPerm [7, 8],
    Subgroup.subset_closure (Set.mem_insert _ _)⟩

abbrev m11LocB : NativeSporadic.M11 :=
  ⟨List.formPerm [0, 3, 2, 7] * List.formPerm [1, 4, 5, 8],
    Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)⟩

@[expose] def m11WordX : String := "abbabb"

@[expose] def m11WordY : String := "BaBaBabbabbabababa"

@[expose] def m11WordH : String := "bb"

abbrev m23LocA : NativeSporadic.M23 :=
  ⟨List.formPerm [0, 1] * List.formPerm [2, 3] * List.formPerm [6, 7] * List.formPerm [8, 9] *
      List.formPerm [12, 13] * List.formPerm [14, 15] * List.formPerm [18, 19] *
      List.formPerm [20, 21],
    Subgroup.subset_closure (Set.mem_insert _ _)⟩

abbrev m23LocB : NativeSporadic.M23 :=
  ⟨List.formPerm [0, 15, 10, 2] * List.formPerm [1, 8, 20, 11] * List.formPerm [3, 4, 7, 22] *
      List.formPerm [5, 21, 13, 17] * List.formPerm [12, 19] * List.formPerm [14, 16],
    Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)⟩

@[expose] def m23WordX : String := "abbabb"

@[expose] def m23WordY : String := "BababbaBabbababbaBaB"

@[expose] def m23WordH : String := "bababbaBaB"

end CFSG.QuasithinUnique.Ch1

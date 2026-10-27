module

public import CFSG.GH74.GLS.Stage1.Thm6.Glue.L2K1
public import CFSG.GH74.GLS.C3.Statements

public section

namespace CFSG.GH74.GLS.Stage1.Thm6.Glue

open Subgroup CFSG CFSG.GH74.GLS CFSG.GH74.GLS.Stage1.Thm6 CFSG.GH74.GLS.Stage1.Thm6.Sec12
  CFSG.GH74.GLS.Stage1.Thm6.Sec12b

@[expose] def IV3K1LeafC3 : Prop :=
  ∀ (G : Type) [Group G] [Finite G], C3Hyp G →
    ∀ (x : G) (Kb : Subgroup (CentralizerBar x)), IV3K1Leaf x Kb

theorem IV3K1LeafC3.sylowC3 (h : IV3K1LeafC3) :
    ∀ (G : Type) [Group G] [Finite G], C3Hyp G →
      ∀ (x : G) (Kb : Subgroup (CentralizerBar x)), IV3SylowLeaf x Kb :=
  fun G _ _ hG x Kb => (h G hG x Kb).sylowLeaf

end CFSG.GH74.GLS.Stage1.Thm6.Glue

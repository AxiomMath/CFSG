module

public import CFSG.GH74.GLS.Stage1.Thm6.Glue.L2K1
public import CFSG.GH74.GLS.Stage12.Interface

public section

namespace CFSG.GH74.GLS.Stage1.Thm6.Glue

open Subgroup CFSG CFSG.GH74.GLS CFSG.GH74.GLS.Stage1.Thm6 CFSG.GH74.GLS.Stage1.Thm6.Sec12
  CFSG.GH74.GLS.Stage1.Thm6.Sec12b

@[expose] def IV3K1LeafStd : Prop :=
  ∀ (G : Type) [Group G] [Finite G], Stage12.Std G → pRank 2 G = 3 →
    ∀ (x : G) (Kb : Subgroup (CentralizerBar x)), IV3K1Leaf x Kb

theorem IV3K1LeafStd.sylowStd (h : IV3K1LeafStd) :
    ∀ (G : Type) [Group G] [Finite G], Stage12.Std G → pRank 2 G = 3 →
      ∀ (x : G) (Kb : Subgroup (CentralizerBar x)), IV3SylowLeaf x Kb :=
  fun G _ _ hStd h3 x Kb => (h G hStd h3 x Kb).sylowLeaf

variable {G : Type} [Group G] [Finite G]

end CFSG.GH74.GLS.Stage1.Thm6.Glue

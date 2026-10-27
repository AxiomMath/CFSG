module

public import CFSG.GH74.GLS.C3.Layer2.L5B14
public import CFSG.GH74.GLS.C3.Layer2.L45Final

public section

namespace CFSG.GH74.GLS

open Equiv Perm Subgroup CFSG CFSG.ABGLocalTools CFSG.GH74.GLS.C3.Prop121
  CFSG.GH74.GLS.C3.Layer2 CFSG.GH74.GLS.C3.Layer2.Model CFSG.GH74.GLS.C3.Layer2.L5

@[expose] def S_Case48 : Prop :=
  ∀ (G : Type) [Group G] [Finite G], C3Hyp G → ∀ (x : G) (K T Q S : Subgroup G) (a : G)
    (h : IsAConfig 5 x K T Q S a) (c : Coord5 h),
    ¬ ((∀ V ∈ FamQ (c.lift Rm) Q, V ⊓ (T ⊓ K) = ⊥) ∧ (FamQ (c.lift Rm) Q).ncard = 4)

theorem S_Prop46_of_case48
    (h48 : S_Case48) : S_Prop46 := by
  intro G _ _ hG x K T Q S a h
  obtain ⟨hs, hnab, -⟩ := isKProperSimple_iff.1 hG.kproper
  obtain ⟨c⟩ := exists_coord5 hG.pRank_eq_four.le h
  rcases fam_dichotomy h c hG.pRank_eq_four.le with h47 | h48'
  · exact case47_pattern hs hnab h47
  · exact absurd h48' (h48 G hG x K T Q S a h c)

theorem s_layerII_of_case48
    (h48 : S_Case48) : S_layerII :=
  s_layerII_of_prop46 (S_Prop46_of_case48 h48)

end CFSG.GH74.GLS

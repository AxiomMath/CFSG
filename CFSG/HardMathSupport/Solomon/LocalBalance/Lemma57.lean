module

public import CFSG.HardMathSupport.Solomon.LocalBalance.Sec5Statements
public import CFSG.HardMathSupport.Solomon.Proving.Basic
public import CFSG.HardMathSupport.Solomon.LocalBalance.Sec2Statements

public section

namespace CFSG.HardMathSupport.Solomon.LocalBalance

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.HardMathSupport.Solomon.Coordinator

theorem not_le_normalizer_of_relIndex_eq_three {G : Type*} [Group G] {B L : Subgroup G}
    (h : (Subgroup.normalizer (L : Set G)).relIndex B = 3) : ¬ B ≤ Subgroup.normalizer (L : Set G) := by
  intro hle
  have : (Subgroup.normalizer (L : Set G)).relIndex B = 1 := Subgroup.relIndex_eq_one.2 hle
  omega

theorem IsSLThreeExc.isSLThree {X : Type*} [Group X] (h : IsSLThreeExc X) : IsSLThree X := by
  obtain ⟨K, hK, hf, -, he⟩ := h
  exact ⟨K, hK, hf, he⟩

theorem IsSUThreeExc.isSUThree {X : Type*} [Group X] (h : IsSUThreeExc X) : IsSUThree X := by
  obtain ⟨K, hK, hf, q, hq, -, he⟩ := h
  exact ⟨K, hK, hf, q, hq, he⟩

theorem lemma57_of_lemma24_lemma56 (h24 : Lemma24) (h56 : Lemma56) : Lemma57 := by
  intro G _ _ m hS hC B hB
  have hB1 : IsBOneMax 3 B :=
    CFSG.HardMathSupport.Solomon.Proving.isBOneMax_of_isBZeroMax (le_refl 3) hB
  by_contra hnot
  have hex : ∃ D : Subgroup G, IsEkIn 3 2 B D ∧ ∃ b ∈ B, b ≠ 1 ∧
      ¬ delta2At 3 B D b ≤ GLAPPrimeCoreOf 3 (Subgroup.centralizer ({b} : Set G)) := by
    by_contra hcon
    push Not at hcon
    exact hnot fun D hD b hb hb1 => hcon D hD b hb hb1
  obtain ⟨D, hD, b, hb, hb1, hX⟩ := hex
  obtain ⟨-, ⟨L, hL, hXL⟩, hall⟩ := h24 G m 3 hS B hB1 hnot D hD b hb hb1 hX
  obtain ⟨hi, hii, -⟩ := hall L ⟨hB1, hD, hb, hb1, hX, hL, hXL⟩
  have hnorm := ((h56 G m hS hC B hB b hb hb1).1 L hL
    (hii.imp IsSLThreeExc.isSLThree IsSUThreeExc.isSUThree))
  exact not_le_normalizer_of_relIndex_eq_three hi hnorm

end CFSG.HardMathSupport.Solomon.LocalBalance

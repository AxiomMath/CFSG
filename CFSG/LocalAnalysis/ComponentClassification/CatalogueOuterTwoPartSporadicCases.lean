module

public import CFSG.LocalAnalysis.ComponentClassification.CatalogueOuterTwoPartSporadic
public import CFSG.Sporadic.Schreier.M11
public import CFSG.Sporadic.Schreier.M12
public import CFSG.Sporadic.Schreier.M22
public import CFSG.Sporadic.Schreier.M23
public import CFSG.Sporadic.Schreier.M24
public import CFSG.Sporadic.Schreier.J1Outer
public import CFSG.Sporadic.Schreier.PairJ2Pairs
public import CFSG.Sporadic.Schreier.PairJ3Pairs
public import CFSG.Sporadic.Schreier.PairHSPairs
public import CFSG.Sporadic.Schreier.PairMcLPairs
public import CFSG.Sporadic.Schreier.PairHePairs
public import CFSG.Sporadic.Schreier.Fi24Schreier
public import CFSG.Sporadic.SuzOddCore.Outer
public import CFSG.Monster.B.Fischer.Fi22Model

public section

namespace CFSG.ComponentClassification.CatalogueOuterTwoPart

open CFSG.Blueprint
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)

theorem outerTwoPartBound_of_card_outer_le {T : Type} [Group T] {m k : ℕ} (hm : 2 ≤ m)
    (hT : Nat.card T ≠ 0) (hdvd : 2 ^ m ∣ Nat.card T) (hout : Nat.card (Outer T) ≤ k)
    (hk : k < 2 ^ m) : OuterTwoPartBound T := by
  have h1 : 2 ^ m ≤ ordProj[2] (Nat.card T) :=
    Nat.le_of_dvd (Nat.ordProj_pos _ _)
      ((Nat.Prime.pow_dvd_iff_dvd_ordProj Nat.prime_two hT).mp hdvd)
  have h4 : (4 : ℕ) ≤ 2 ^ m := by
    calc (4 : ℕ) = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hm
  refine ⟨h4.trans h1, lt_of_lt_of_le ?_ h1⟩
  by_cases h0 : Nat.card (Outer T) = 0
  · rw [h0, Nat.factorization_zero, Finsupp.zero_apply, pow_zero]
    exact lt_of_lt_of_le (by norm_num) h4
  · exact lt_of_le_of_lt ((Nat.ordProj_le 2 h0).trans hout) hk

theorem sporadicOuterTwoPart_M11 : SporadicOuterTwoPart .M11 :=
  outerTwoPartBound_of_card_outer_le (T := NativeSporadic.M11) (m := 2) le_rfl
    (by rw [Sporadic.Mathieu.card_M11]; norm_num)
    (by rw [Sporadic.Mathieu.card_M11]; norm_num) Sporadic.Schreier.at_m11_schreier.1 (by norm_num)

theorem sporadicOuterTwoPart_M12 : SporadicOuterTwoPart .M12 :=
  outerTwoPartBound_of_card_outer_le (T := NativeSporadic.M12) (m := 3) (by norm_num)
    (by rw [Sporadic.Mathieu.card_M12]; norm_num) (by rw [Sporadic.Mathieu.card_M12]; norm_num)
    Sporadic.Schreier.at_m12_schreier.1 (by norm_num)

theorem sporadicOuterTwoPart_M22 : SporadicOuterTwoPart .M22 :=
  outerTwoPartBound_of_card_outer_le (T := NativeSporadic.M22) (m := 3) (by norm_num)
    (by rw [Sporadic.Mathieu.card_M22]; norm_num) (by rw [Sporadic.Mathieu.card_M22]; norm_num)
    Sporadic.Schreier.at_m22_schreier.1 (by norm_num)

theorem sporadicOuterTwoPart_M23 : SporadicOuterTwoPart .M23 :=
  outerTwoPartBound_of_card_outer_le (T := NativeSporadic.M23) (m := 2) le_rfl
    (by rw [Sporadic.Schreier.m23_card]; norm_num) (by rw [Sporadic.Schreier.m23_card]; norm_num)
    Sporadic.Schreier.at_m23_schreier.1 (by norm_num)

theorem sporadicOuterTwoPart_M24 : SporadicOuterTwoPart .M24 :=
  outerTwoPartBound_of_card_outer_le (T := NativeSporadic.M24) (m := 3) (by norm_num)
    (by rw [Sporadic.Mathieu.card_M24]; norm_num) (by rw [Sporadic.Mathieu.card_M24]; norm_num)
    Sporadic.Schreier.at_m24_schreier.1 (by norm_num)

theorem sporadicOuterTwoPart_J1 : SporadicOuterTwoPart .J1 :=
  outerTwoPartBound_of_card_outer_le (T := NativeSporadic.J1) (m := 2) le_rfl
    (by rw [Sporadic.J1.card_J1]; norm_num)
    (by rw [Sporadic.J1.card_J1]; norm_num) Sporadic.Schreier.at_j1_schreier.1.le (by norm_num)

theorem sporadicOuterTwoPart_J2 : SporadicOuterTwoPart .J2 :=
  outerTwoPartBound_of_card_outer_le (T := NativeSporadic.J2) (m := 2) le_rfl
    (by rw [Sporadic.J2.card_J2]; norm_num)
    (by rw [Sporadic.J2.card_J2]; norm_num) Sporadic.Schreier.AT_J2_Schreier.1 (by norm_num)

theorem sporadicOuterTwoPart_J3 : SporadicOuterTwoPart .J3 :=
  outerTwoPartBound_of_card_outer_le (T := NativeSporadic.J3) (m := 3) (by norm_num)
    (by rw [Sporadic.J3.card_J3]; norm_num)
    (by rw [Sporadic.J3.card_J3]; norm_num) Sporadic.Schreier.AT_J3_Schreier.1 (by norm_num)

theorem sporadicOuterTwoPart_HS : SporadicOuterTwoPart .HS :=
  outerTwoPartBound_of_card_outer_le (T := NativeSporadic.HS) (m := 5) (by norm_num)
    (by rw [Sporadic.HS.card_HS]; norm_num)
    (by rw [Sporadic.HS.card_HS]; norm_num) Sporadic.Schreier.AT_HS_Schreier.1 (by norm_num)

theorem sporadicOuterTwoPart_McL : SporadicOuterTwoPart .McL :=
  outerTwoPartBound_of_card_outer_le (T := NativeSporadic.McL) (m := 6) (by norm_num)
    (by rw [Sporadic.McL.card_McL]; norm_num) (by rw [Sporadic.McL.card_McL]; norm_num)
    Sporadic.Schreier.AT_McL_Schreier.1 (by norm_num)

theorem sporadicOuterTwoPart_He : SporadicOuterTwoPart .He :=
  outerTwoPartBound_of_card_outer_le (T := NativeSporadic.He) (m := 2) le_rfl
    (by rw [Sporadic.He.card_He]; norm_num)
    (by rw [Sporadic.He.card_He]; norm_num) Sporadic.Schreier.AT_He_Schreier.1 (by norm_num)

theorem card_outer_fi22 : Nat.card (Outer NativeSporadic.Fi22) = 2 := by
  obtain ⟨⟨e, -⟩, -⟩ := @CFSG.LocalAnalysis.ComponentInitial.outer_isomorphism
    NativeSporadic.Fi22 Monster.B.Fischer.fi22P Units.instGroup _ Monster.B.Fischer.fi22PermEquiv
  obtain ⟨f⟩ := Monster.B.Fischer.CTUC_Fi22_full_automorphism_permutation_model.2.2.2.2.2.2.2
  rw [Nat.card_congr e.toEquiv]
  change Nat.card (MulAut Monster.B.Fischer.fi22P ⧸
    (MulAut.conj : Monster.B.Fischer.fi22P →* MulAut Monster.B.Fischer.fi22P).range) = 2
  rw [Nat.card_congr f.toEquiv]
  simp

theorem sporadicOuterTwoPart_Fi22 : SporadicOuterTwoPart .Fi22 :=
  outerTwoPartBound_of_card_outer_le (T := NativeSporadic.Fi22) (m := 2) le_rfl
    (by rw [Sporadic.Fi22.card_Fi22]; norm_num)
    (by rw [Sporadic.Fi22.card_Fi22]; norm_num) card_outer_fi22.le (by norm_num)

theorem sporadicOuterTwoPart_Fi24 : SporadicOuterTwoPart .Fi24Prime :=
  outerTwoPartBound_of_card_outer_le (T := NativeSporadic.Fi24prime) (m := 2) le_rfl
    (by rw [Sporadic.Fi24.card_Fi24prime]; norm_num)
    (by rw [Sporadic.Fi24.card_Fi24prime]; norm_num)
    Sporadic.Schreier.Fi24.card_outer_fi24prime.le (by norm_num)

theorem sporadicOuterTwoPart_Suz : SporadicOuterTwoPart .Suz :=
  outerTwoPartBound_of_card_outer_le (T := NativeSporadic.Carrier .Suz) (m := 2) le_rfl
    (by show Nat.card NativeSporadic.Suz ≠ 0; rw [Sporadic.Suz.card_Suz]; norm_num)
    (by show 2 ^ 2 ∣ Nat.card NativeSporadic.Suz; rw [Sporadic.Suz.card_Suz]; norm_num)
    Sporadic.SuzOddCore.outer_carrier_suz.1.le (by norm_num)

end CFSG.ComponentClassification.CatalogueOuterTwoPart

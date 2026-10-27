module

public import CFSG.GH74.GLS.IVK.Proofs2.Ivk93CovCfg
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsSp4TypeOne

public section

namespace CFSG.GH74.GLS.IVK.Proofs2

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.GLS.IVK CFSG.Blueprint CFSG.ComponentClassification
open scoped MatrixGroups

theorem ivk93cov_sl2_ne_factorial {Q n : ℕ} (hn8 : 8 ≤ n) (hn11 : n ≤ 11) :
    Q * (Q ^ 2 - 1) ≠ n.factorial := by
  intro h
  have key : ∀ Q₀ : ℕ, Q₀ * (Q₀ ^ 2 - 1) < n.factorial →
      n.factorial < (Q₀ + 1) * ((Q₀ + 1) ^ 2 - 1) → False := by
    intro Q₀ h1 h2
    rcases le_or_gt Q Q₀ with hq | hq
    · have := sl2_card_mono hq
      omega
    · have := sl2_card_mono (show Q₀ + 1 ≤ Q by omega)
      omega
  interval_cases n
  · exact key 34 (by decide) (by decide)
  · exact key 71 (by decide) (by decide)
  · exact key 153 (by decide) (by decide)
  · exact key 341 (by decide) (by decide)

namespace Ivk93Cov

variable {J : Type} [Group J] [Finite J] {x : J} {n : ℕ} {B : Subgroup J}

theorem false_of_equiv_sl2 (h : Ivk93Cov x n B) {F : Type} [Field F] [Finite F]
    (hodd : Odd (Nat.card F)) (h5 : 5 ≤ Nat.card F) (e : SL(2, F) ≃* ↥B) : False := by
  have h2 : (2 : F) ≠ 0 := CFSG.ABGLocalTools.two_ne_zero_of_odd_card hodd
  have hO : pPrimeCore 2 ↥B = ⊥ := by
    rw [← CFSG.pPrimeCore_map_iso 2 e, CatFactsSp4.pPrimeCore_SL2 h2 (by omega), Subgroup.map_bot]
  have hc1 := Subgroup.card_eq_card_quotient_mul_card_subgroup (pPrimeCore 2 ↥B)
  rw [h.card_quot, hO, Subgroup.card_bot, mul_one] at hc1
  rw [← Nat.card_congr e.toEquiv, CFSG.SL2MinimalFaithful.card_specialLinearGroup_fin_two F] at hc1
  exact ivk93cov_sl2_ne_factorial h.eight h.le_eleven hc1

theorem false_of_isSimpleGroup (h : Ivk93Cov x n B) (hs : IsSimpleGroup ↥B) : False := by
  have hbig := h.card_ge_big
  have hperf := h.perfect
  have hnt := h.nontrivial
  have hnab : ¬ ∀ a b : ↥B, a * b = b * a := by
    intro hcomm
    have : IsMulCommutative ↥B := ⟨⟨hcomm⟩⟩
    have hsol : Group.IsSolvable ↥B := inferInstance
    exact Group.IsPerfect.not_isSolvable ↥B hsol
  have hZ : center ↥B = ⊥ := by
    rcases (inferInstance : (center ↥B).Normal).eq_bot_or_eq_top with h0 | h0
    · exact h0
    · exfalso
      apply hnab
      intro a b
      have : a ∈ center ↥B := h0 ▸ Subgroup.mem_top a
      exact (Subgroup.mem_center_iff.1 this b).symm
  have hO : pPrimeCore 2 ↥B = ⊥ := by
    rcases (inferInstance : (pPrimeCore 2 ↥B).Normal).eq_bot_or_eq_top with h0 | h0
    · exact h0
    · exfalso
      have hc := h.card_quot
      have : Nat.card (↥B ⧸ pPrimeCore 2 ↥B) = 1 := by
        rw [h0]
        exact Subgroup.index_top
      rw [this] at hc
      have := Nat.factorial_le h.eight
      have h8 : Nat.factorial 8 = 40320 := by decide
      omega
  obtain ⟨-, hc, -⟩ := h.cover
  let e : (↥B ⧸ pPrimeCore 2 ↥B) ≃* ↥B :=
    (QuotientGroup.quotientMulEquivOfEq hO).trans QuotientGroup.quotientBot
  rw [Nat.card_congr (Subgroup.centerCongr e).toEquiv, hZ, Subgroup.card_bot] at hc
  omega

theorem false_of_card_sl2 (h : Ivk93Cov x n B) {Q : ℕ} (hO : pPrimeCore 2 ↥B = ⊥)
    (hc : Nat.card ↥B = Q * (Q ^ 2 - 1)) : False := by
  have hc1 := Subgroup.card_eq_card_quotient_mul_card_subgroup (pPrimeCore 2 ↥B)
  rw [h.card_quot, hO, Subgroup.card_bot, mul_one] at hc1
  exact ivk93cov_sl2_ne_factorial (Q := Q) h.eight h.le_eleven (hc.symm.trans hc1)

end Ivk93Cov

end CFSG.GH74.GLS.IVK.Proofs2

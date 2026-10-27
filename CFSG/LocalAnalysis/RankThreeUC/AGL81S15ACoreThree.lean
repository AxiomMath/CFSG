module

public import CFSG.Open.StatedDefs
public import CFSG.Open.LocalVocabulary
import CFSG.LocalAnalysis.RankThreeUC.AGL81S15ACoreThreeHeis
import CFSG.LocalAnalysis.RankThreeUC.AGL81S15RankChevToral
import CFSG.LocalAnalysis.SectionRank.OddCover.ScalarCover
import CFSG.LinearAlgebra.LinearGroups.UnitaryScalarKernel
import CFSG.LocalAnalysis.SectionRank.ClassicalOdd

public section

namespace CFSG.LocalAnalysis.RankThreeUC.S15.ACore

open CFSG.Open CFSG.SectionRank.OddCover

theorem eq_bot_or_eq_of_le_of_card_eq_three {G : Type*} [Group G] {Z D : Subgroup G}
    (hZD : Z ≤ D) (hD : Nat.card D = 3) : Z = ⊥ ∨ Z = D := by
  have : Finite D := Nat.finite_of_card_ne_zero (by rw [hD]; norm_num)
  have hdvd : Nat.card Z ∣ 3 := hD ▸ Subgroup.card_dvd_of_le hZD
  rcases (Nat.dvd_prime Nat.prime_three).1 hdvd with h | h
  · exact Or.inl (Subgroup.eq_bot_of_card_eq Z h)
  · exact Or.inr (Subgroup.eq_of_le_of_card_ge hZD (by rw [hD, h]))

theorem natCast_three_ne_zero_of_dvd_card_sub_one {F : Type} [Field F] [Fintype F]
    (h3 : 3 ∣ Fintype.card F - 1) : ((3 : ℕ) : F) ≠ 0 := by
  intro h0
  obtain ⟨k, hk⟩ := h3
  have hc : ((Fintype.card F : ℕ) : F) = 0 := FiniteField.cast_card_eq_zero F
  have hpos : 0 < Fintype.card F := Fintype.card_pos
  rw [show Fintype.card F = 3 * k + 1 by omega, Nat.cast_add, Nat.cast_mul, h0, zero_mul,
    zero_add, Nat.cast_one] at hc
  exact one_ne_zero hc

theorem natCast_three_ne_zero_of_card_eq_sq {F : Type} [Field F] [Fintype F] {q : ℕ}
    (hF : Fintype.card F = q ^ 2) (h3 : 3 ∣ q + 1) : ((3 : ℕ) : F) ≠ 0 := by
  intro h0
  have hc : ((Fintype.card F : ℕ) : F) = 0 := FiniteField.cast_card_eq_zero F
  rw [hF, Nat.cast_pow] at hc
  have hq0 : (q : F) = 0 := (pow_eq_zero_iff (by norm_num)).1 hc
  obtain ⟨k, hk⟩ := h3
  have h1 : ((q + 1 : ℕ) : F) = ((3 * k : ℕ) : F) := by rw [hk]
  rw [Nat.cast_add, Nat.cast_mul, hq0, h0, zero_mul, zero_add, Nat.cast_one] at h1
  exact one_ne_zero h1

theorem card_scalars_statedSL_three_of_dvd {F : Type} [Field F] [Finite F]
    (h3 : 3 ∣ Nat.card F - 1) :
    Nat.card ((StatedScalars (Fin 3) F).subgroupOf (StatedSL 3 F)) = 3 := by
  have hdvd : Nat.card ((StatedScalars (Fin 3) F).subgroupOf (StatedSL 3 F)) ∣ 3 :=
    card_scalars_dvd (by norm_num) _ fun x c hc => by
      have hdet := det_of_mem_statedSL x.1.2
      rw [hc, Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, Matrix.det_diagonal,
        Finset.prod_const, Finset.card_univ, Fintype.card_fin] at hdet
      exact Units.ext (by rw [Units.val_pow_eq_pow_val, hdet, Units.val_one])
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨c, hc⟩ := exists_prime_orderOf_dvd_card' (G := Fˣ) 3 (by rw [card_units_eq]; exact h3)
  have hcS : Matrix.GeneralLinearGroup.scalar (Fin 3) c ∈ StatedSL 3 F := by
    refine Subgroup.subset_closure ?_
    change ((Matrix.GeneralLinearGroup.scalar (Fin 3) c : GL (Fin 3) F) :
      Matrix (Fin 3) (Fin 3) F).det = 1
    rw [Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, Matrix.det_diagonal,
      Finset.prod_const, Finset.card_univ, Fintype.card_fin, ← Units.val_pow_eq_pow_val,
      ← hc, pow_orderOf_eq_one, Units.val_one]
  have hx : (⟨_, hcS⟩ : StatedSL 3 F) ∈ (StatedScalars (Fin 3) F).subgroupOf (StatedSL 3 F) :=
    Subgroup.mem_subgroupOf.2 ⟨c, rfl⟩
  have hord : orderOf (⟨_, hx⟩ : (StatedScalars (Fin 3) F).subgroupOf (StatedSL 3 F)) = 3 := by
    rw [Subgroup.orderOf_mk, Subgroup.orderOf_mk,
      orderOf_injective _ (scalar_injective (by norm_num)) c, hc]
  have h3D := orderOf_dvd_natCard
    (⟨_, hx⟩ : (StatedScalars (Fin 3) F).subgroupOf (StatedSL 3 F))
  rw [hord] at h3D
  exact Nat.dvd_antisymm hdvd h3D

theorem factorization_three_card_statedSL_three {q : ℕ} (hq : 2 ≤ q) (h3 : 3 ∣ q - 1) :
    (q ^ 3 * (q ^ 2 - 1) * (q ^ 3 - 1)).factorization 3 = (3 * (q - 1) ^ 2).factorization 3 := by
  have hq1 : 1 ≤ q := by omega
  have e1 : q ^ 2 - 1 = (q - 1) * (q + 1) := by zify [hq1, Nat.one_le_pow 2 _ hq1]; ring
  have e2 : q ^ 3 - 1 = (q - 1) * (q ^ 2 + q + 1) := by zify [hq1, Nat.one_le_pow 3 _ hq1]; ring
  rw [e1, e2, ← factorization_six_mul_three (pow_ne_zero 2 (by omega : q - 1 ≠ 0))]
  exact factorization_order_eq Nat.prime_three (by norm_num) (by omega) (by omega) (by omega)
    (by positivity) (by omega) (by omega) (factorization_sq_add_add_one Nat.prime_three hq1 h3)

theorem factorization_three_card_statedSU_three {q : ℕ} (h3 : 3 ∣ q + 1) :
    (q ^ 3 * (q ^ 2 - 1) * (q ^ 3 + 1)).factorization 3 = (3 * (q + 1) ^ 2).factorization 3 := by
  have hq1 : 1 ≤ q := by omega
  have hqq : q ≤ q ^ 2 := Nat.le_self_pow (by norm_num) q
  have e1 : q ^ 2 - 1 = (q + 1) * (q - 1) := by zify [hq1, Nat.one_le_pow 2 _ hq1]; ring
  have e2 : q ^ 3 + 1 = (q + 1) * (q ^ 2 - q + 1) := by zify [hqq]; ring
  rw [e1, e2, ← factorization_six_mul_three (pow_ne_zero 2 (by omega : q + 1 ≠ 0))]
  exact factorization_order_eq Nat.prime_three (by norm_num) (by omega) (by omega) (by omega)
    (by omega) (by omega) (by omega) (factorization_sq_sub_add_one Nat.prime_three h3)

theorem pRank_statedSL_three {F : Type} [Field F] [Fintype F] (h3 : 3 ∣ Fintype.card F - 1)
    (Z₀ : Subgroup (StatedSL 3 F)) [Z₀.Normal]
    (hZ₀ : Z₀ ≤ (StatedScalars (Fin 3) F).subgroupOf (StatedSL 3 F)) :
    CFSG.Open.pRank 3 (⊤ : Subgroup (↥(StatedSL 3 F) ⧸ Z₀)) = 2 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have h3' : 3 ∣ Nat.card F - 1 := by rwa [Nat.card_eq_fintype_card]
  have hD := card_scalars_statedSL_three_of_dvd h3'
  rcases eq_bot_or_eq_of_le_of_card_eq_three hZ₀ hD with rfl | rfl
  · rw [CFSG.SectionRank.pRank_quotient_eq ⊥ (by rw [Subgroup.card_bot]; norm_num)]
    exact pRank_top_statedSL_eq_pred (by norm_num)
      (natCast_three_ne_zero_of_dvd_card_sub_one h3) h3'
  · obtain ⟨ω, hω⟩ := exists_prime_orderOf_dvd_card' (G := Fˣ) 3
      (by rw [card_units_eq]; exact h3')
    refine le_antisymm (three_pRank_statedProj_le_two monomialData_statedSL ?_ hD)
      (two_le_pRank_statedProj_of_monomialData monomialData_statedSL (Subgroup.mem_top ω) hω)
    rw [card_statedSL_three, Subgroup.card_top, card_units_eq]
    exact factorization_three_card_statedSL_three Finite.one_lt_card h3'

theorem pRank_statedSU_three {F : Type} [Field F] [Fintype F] {q : ℕ}
    (hF : Fintype.card F = q ^ 2) (hq : 3 ≤ q) (h3 : 3 ∣ q + 1)
    (Z₀ : Subgroup (StatedSU 3 q F)) [Z₀.Normal]
    (hZ₀ : Z₀ ≤ (StatedScalars (Fin 3) F).subgroupOf (StatedSU 3 q F)) :
    CFSG.Open.pRank 3 (⊤ : Subgroup (↥(StatedSU 3 q F) ⧸ Z₀)) = 2 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hq1 : 1 ≤ q := le_trans (by norm_num) hq
  have hF' : Nat.card F = q ^ 2 := by rw [Nat.card_eq_fintype_card, hF]
  obtain ⟨p, _, n, hp, hn⟩ := FiniteField.card' F
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨f, -, rfl⟩ : ∃ f ≤ (n : ℕ), q = p ^ f :=
    (Nat.dvd_prime_pow hp).1 ⟨q, by rw [← hn, hF, sq]⟩
  have hD : Nat.card ((StatedScalars (Fin 3) F).subgroupOf (StatedSU 3 (p ^ f) F)) = 3 := by
    rw [(CFSG.LinearGroups.unitary_scalar_kernel hp hF' (by norm_num)).2.2]
    exact Nat.gcd_eq_left h3
  rcases eq_bot_or_eq_of_le_of_card_eq_three hZ₀ hD with rfl | rfl
  · rw [CFSG.SectionRank.pRank_quotient_eq ⊥ (by rw [Subgroup.card_bot]; norm_num)]
    exact pRank_top_statedSU_eq_pred (by norm_num) (natCast_three_ne_zero_of_card_eq_sq hF h3)
      hF' h3
  · have h3u : 3 ∣ Nat.card Fˣ := by
      rw [card_units_eq, hF', show (p ^ f) ^ 2 - 1 = (p ^ f + 1) * (p ^ f - 1) by
        zify [hq1, Nat.one_le_pow 2 _ hq1]; ring]
      exact Dvd.dvd.mul_right h3 _
    obtain ⟨ω, hω⟩ := exists_prime_orderOf_dvd_card' (G := Fˣ) 3 h3u
    have hωM : ω ∈ normOne F (p ^ f) := by
      rw [mem_normOne]
      obtain ⟨c, hc⟩ := h3
      rw [hc, pow_mul, ← hω, pow_orderOf_eq_one, one_pow]
    refine le_antisymm (three_pRank_statedProj_le_two monomialData_statedSU ?_ hD)
      (two_le_pRank_statedProj_of_monomialData monomialData_statedSU hωM hω)
    rw [card_statedSU_three hF', card_normOne hF']
    exact factorization_three_card_statedSU_three h3

end CFSG.LocalAnalysis.RankThreeUC.S15.ACore

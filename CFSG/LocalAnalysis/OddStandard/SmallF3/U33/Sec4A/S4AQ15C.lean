module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4A.S4AQ14G
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4A.S4AQ15A

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33.S4A

open Subgroup
open scoped Pointwise commutatorElement

section Q15C0

variable {G : Type} [Group G] [Finite G] {t : G} {L S : Subgroup G} {x₁ x₂ lam rho : G}

theorem q15_rho_cube (h : L41GPh1 t L S x₁ x₂ lam rho) : rho ^ 3 = 1 := by
  rw [← h.ord_rho]
  exact pow_orderOf_eq_one rho

theorem q15_R_le (h : L41GPh8 t L S x₁ x₂ lam rho) :
    l41R t x₁ x₂ rho ≤ l41Q1 t x₁ x₂ rho := by
  unfold l41R l41Q1
  refine Subgroup.commutator_mono ?_ le_rfl
  rw [← m13_F_eq h]
  exact q14_F_le_Q h

theorem q15_Y_le (h : L41GPh10 t L S x₁ x₂ lam rho) :
    l41Y t x₁ x₂ rho ≤ l41Q1 t x₁ x₂ rho :=
  (m13_Y_le_R t x₁ x₂ rho).trans (q15_R_le h.toL41GPh8)

theorem q15_Q1_le_Q (h : L41GPh8 t L S x₁ x₂ lam rho) :
    l41Q1 t x₁ x₂ rho ≤ l41Q t x₁ x₂ rho := by
  unfold l41Q1
  exact q15_commutator_le (q14_mem_normalizer_Q (q14_rho_mem_M h))

end Q15C0

section Q15C1

variable {G : Type} [Group G] [Finite G] {t : G} {L S : Subgroup G} {x₁ x₂ lam rho : G}
variable [((l41Y t x₁ x₂ rho).subgroupOf (l41Q t x₁ x₂ rho)).Normal]

abbrev q15T (t x₁ x₂ rho : G) [((l41Y t x₁ x₂ rho).subgroupOf (l41Q t x₁ x₂ rho)).Normal] : Type :=
  ↥(l41Q t x₁ x₂ rho) ⧸ (l41Y t x₁ x₂ rho).subgroupOf (l41Q t x₁ x₂ rho)

@[expose] def q15Tbar (h : L41GPh8 t L S x₁ x₂ lam rho) : q15T t x₁ x₂ rho :=
  QuotientGroup.mk (⟨t, q14_t_mem_Q h⟩ : ↥(l41Q t x₁ x₂ rho))

@[expose] noncomputable def q15Alpha (h : L41GPh10 t L S x₁ x₂ lam rho) :
    MulAut (q15T t x₁ x₂ rho) :=
  quotConj (l41Q t x₁ x₂ rho) (l41Y t x₁ x₂ rho) rho
    (q14_mem_normalizer_Q (q14_rho_mem_M h.toL41GPh8))
    (q14_mem_normalizer_Y h (q14_rho_mem_M h.toL41GPh8))

theorem q15_card_quot (h : L41GPh10 t L S x₁ x₂ lam rho) : Nat.card (q15T t x₁ x₂ rho) = 32 := by
  have hcard := Subgroup.card_eq_card_quotient_mul_card_subgroup
    ((l41Y t x₁ x₂ rho).subgroupOf (l41Q t x₁ x₂ rho))
  have hY : Nat.card ((l41Y t x₁ x₂ rho).subgroupOf (l41Q t x₁ x₂ rho)) = 16 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (q14_Y_le_Q h)).toEquiv, m11_card_Y h]
  rw [q14_card_Q h, hY] at hcard
  change 512 = Nat.card (q15T t x₁ x₂ rho) * 16 at hcard
  omega

theorem q15_quot_isPGroup : IsPGroup 2 (q15T t x₁ x₂ rho) :=
  (q14_Q_isPGroup t x₁ x₂ rho).to_quotient
    ((l41Y t x₁ x₂ rho).subgroupOf (l41Q t x₁ x₂ rho))

theorem q15_orderOf_tbar (h : L41GPh10 t L S x₁ x₂ lam rho) :
    orderOf (q15Tbar h.toL41GPh8) = 2 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine orderOf_eq_prime ?_ ?_
  · have ht2 : (⟨t, q14_t_mem_Q h.toL41GPh8⟩ : ↥(l41Q t x₁ x₂ rho)) ^ 2 = 1 := by
      apply Subtype.ext
      simp [pow_two, t_mul_self h.hyp]
    unfold q15Tbar
    rw [← QuotientGroup.mk_pow, ht2]
    simp
  · intro h1
    unfold q15Tbar at h1
    rw [QuotientGroup.eq_one_iff] at h1
    rw [Subgroup.mem_subgroupOf] at h1
    exact h.rfacts.t_not_mem ((m13_Y_le_R t x₁ x₂ rho) h1)

theorem q15_alpha_cube (h : L41GPh10 t L S x₁ x₂ lam rho) : q15Alpha h ^ 3 = 1 := by
  unfold q15Alpha
  exact quotConj_pow_three (q14_mem_normalizer_Q (q14_rho_mem_M h.toL41GPh8))
    (q14_mem_normalizer_Y h (q14_rho_mem_M h.toL41GPh8)) (q15_rho_cube h.toL41GPh1)

theorem q15_alpha_tbar (h : L41GPh10 t L S x₁ x₂ lam rho) :
    q15Alpha h (q15Tbar h.toL41GPh8) = q15Tbar h.toL41GPh8 := by
  have hfix : rho * t * rho⁻¹ = t :=
    n4_K_fix_t h.toCtx0
      (Subgroup.subset_closure (show rho ∈ ({rho, lam} : Set G) by simp))
  unfold q15Alpha q15Tbar
  rw [quotConj_fix_iff, hfix]
  simp

theorem q15_alpha_ne_one (h : L41GPh10 t L S x₁ x₂ lam rho) : q15Alpha h ≠ 1 := by
  intro hα
  apply not_le_of_gt (q14_F_lt_Q h)
  intro q hq
  have hρQ : rho ∈ normalizer ((l41Q t x₁ x₂ rho : Subgroup G) : Set G) :=
    q14_mem_normalizer_Q (q14_rho_mem_M h.toL41GPh8)
  have hρY : rho ∈ normalizer ((l41Y t x₁ x₂ rho : Subgroup G) : Set G) :=
    q14_mem_normalizer_Y h (q14_rho_mem_M h.toL41GPh8)
  have hfix : q15Alpha h (QuotientGroup.mk (⟨q, hq⟩ : ↥(l41Q t x₁ x₂ rho))) =
      QuotientGroup.mk (⟨q, hq⟩ : ↥(l41Q t x₁ x₂ rho)) := by
    rw [hα]
    rfl
  have hfix' : quotConj (l41Q t x₁ x₂ rho) (l41Y t x₁ x₂ rho) rho hρQ hρY
      (QuotientGroup.mk (⟨q, hq⟩ : ↥(l41Q t x₁ x₂ rho))) =
      QuotientGroup.mk (⟨q, hq⟩ : ↥(l41Q t x₁ x₂ rho)) := by
    simpa [q15Alpha] using hfix
  have hmem : rho * q * rho⁻¹ * q⁻¹ ∈ l41Y t x₁ x₂ rho :=
    (quotConj_fix_iff hρQ hρY (⟨q, hq⟩ : ↥(l41Q t x₁ x₂ rho))).mp hfix'
  have hcomm : ⁅q, rho⁆ ∈ l41Y t x₁ x₂ rho := by
    have hinv : (rho * q * rho⁻¹ * q⁻¹)⁻¹ ∈ l41Y t x₁ x₂ rho :=
      Subgroup.inv_mem _ hmem
    have heq : (rho * q * rho⁻¹ * q⁻¹)⁻¹ = ⁅q, rho⁆ := by
      rw [commutatorElement_def]
      group
    rwa [heq] at hinv
  have hqsup : q ∈ (zpowers t ⊔ l41Y t x₁ x₂ rho : Subgroup G) := by
    change q ∈ ((zpowers t ⊔ l41Y t x₁ x₂ rho : Subgroup G) : Set G)
    rw [← q14_cent_Qbar_rho h]
    exact ⟨hq, hcomm⟩
  have hle : (zpowers t ⊔ l41Y t x₁ x₂ rho : Subgroup G) ≤ l41F t x₁ x₂ rho := by
    rw [l41F]
    exact sup_le le_sup_right ((m13_Y_le_R t x₁ x₂ rho).trans le_sup_left)
  exact hle hqsup

theorem q15_alpha_order (h : L41GPh10 t L S x₁ x₂ lam rho) :
    ∃ n : ℕ, orderOf (q15Alpha h) = 3 ^ n := by
  haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  refine ⟨1, ?_⟩
  have h3 : orderOf (q15Alpha h) = 3 :=
    orderOf_eq_prime (q15_alpha_cube h) (q15_alpha_ne_one h)
  rw [h3, pow_one]

end Q15C1

end CFSG.OddStandard.SmallF3.HarrisU33.S4A

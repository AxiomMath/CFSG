module

public import CFSG.LocalAnalysis.SeitzReduction.EPilotEndOddBasic
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotEndField
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotInnerField

public section

namespace CFSG.SeitzReduction.F4Pilot

open Subgroup CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Ree


section Ambient

variable {G : Type*} [Group G] {G₀ : Subgroup G}

theorem even_F4_isConj_of_not_mem_of_odd (hZ : Odd (Nat.card (centralizer (G₀ : Set G))))
    {f : ℕ} (hf : 1 ≤ f) (K : Type) [Field K] (hK : Nat.card K = 2 ^ f)
    (e : G₀ ≃* adjointGroup .F4 K) {y t : G} (hyN : y ∈ normalizer (G₀ : Set G))
    (htN : t ∈ normalizer (G₀ : Set G)) (hy : y ^ 2 = 1) (ht : t ^ 2 = 1) (hyG : y ∉ G₀)
    (htG : t ∉ G₀) : IsConj y t := by
  have hyo := EPilot.normalizerMulAut_not_mem_range_of_odd hZ e hyN hy hyG
  have hto := EPilot.normalizerMulAut_not_mem_range_of_odd hZ e htN ht htG
  obtain ⟨h, hh⟩ := even_F4_outer_involutions_inner_conj hf K hK _ _
    (EPilot.action_sq_eq_one _ hyN hy) (EPilot.action_sq_eq_one _ htN ht) hyo hto
  set c : normalizer (G₀ : Set G) := ⟨(e.symm h : G), le_normalizer (e.symm h).2⟩ with hcdef
  have hc : normalizerMulAut e c = MulAut.conj h := by
    rw [hcdef, normalizerMulAut_of_mem e (e.symm h).2]
    exact congrArg MulAut.conj (e.apply_symm_apply h)
  have h1 : normalizerMulAut e (c * ⟨y, hyN⟩ * c⁻¹) = normalizerMulAut e ⟨t, htN⟩ := by
    rw [map_mul, map_mul, map_inv, hc, hh]
  have hker : Odd (Nat.card (normalizerMulAut e).ker) := by
    rw [EPilot.card_ker_normalizerMulAut]
    exact hZ
  have hs2 : (((c * ⟨y, hyN⟩ * c⁻¹ : normalizer (G₀ : Set G))) : G) ^ 2 = 1 := by
    have e2 : ((c : G) * y * (c : G)⁻¹) ^ 2 = (c : G) * y ^ 2 * (c : G)⁻¹ := by
      rw [sq, sq]; group
    simp only [coe_mul, coe_inv, e2, hy, mul_one, mul_inv_cancel]
  have h2 : IsConj (((c * ⟨y, hyN⟩ * c⁻¹ : normalizer (G₀ : Set G))) : G) t :=
    EPilot.isConj_of_action_eq (normalizerMulAut e) hker (c * ⟨y, hyN⟩ * c⁻¹).2 htN hs2 ht
      (by rw [Subtype.coe_eta, h1])
  have h3 : IsConj y (((c * ⟨y, hyN⟩ * c⁻¹ : normalizer (G₀ : Set G))) : G) :=
    isConj_iff.2 ⟨(c : G), by simp only [coe_mul, coe_inv]⟩
  exact h3.trans h2

variable [Finite G]

theorem exists_normal_index_two_of_F4_odd (hZ : Odd (Nat.card (centralizer (G₀ : Set G))))
    {n : ℕ} {K : Type} [Field K] (hK : Nat.card K = 2 ^ n) (e : G₀ ≃* adjointGroup .F4 K)
    {t : G} (htN : t ∈ normalizer (G₀ : Set G)) (ht : orderOf t = 2) (htG : t ∉ G₀)
    (huniq : ∀ g : G, g⁻¹ * t * g ∈ normalizer (G₀ : Set G) → g ∈ normalizer (G₀ : Set G)) :
    ∃ N : Subgroup G, N.Normal ∧ N.index = 2 := by
  have : Finite K := Nat.finite_of_card_ne_zero (by rw [hK]; positivity)
  have hn : 1 ≤ n := by
    rcases Nat.eq_zero_or_pos n with rfl | h
    · have h1 := Finite.one_lt_card (α := K)
      rw [hK, pow_zero] at h1
      exact absurd h1 (lt_irrefl 1)
    · exact h
  have : CharP K 2 :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic Nat.prime_two hn hK
  have : CharP K ReeTag.F4.prime := ‹CharP K 2›
  obtain ⟨hCInn, hNF, -⟩ := even_F4_zpowers_finiteExceptionalAut_complement hn K hK
  have ht2 : t ^ 2 = 1 := by rw [← ht]; exact pow_orderOf_eq_one t
  let e' : G₀ ≃* adjointGroup ReeTag.F4.tag K := e
  have hker : Odd (Nat.card (normalizerMulAut e').ker) := by
    rw [EPilot.card_ker_normalizerMulAut]
    exact hZ
  refine EPilot.exists_normal_index_two_of_action_complement (normalizerMulAut e') hker hCInn hNF
    (EPilot.exists_normalizerMulAut_eq_conj e') htN ht
    (EPilot.normalizerMulAut_not_mem_range_of_odd hZ e' htN ht2 htG) huniq
    fun y hyN hy hyout _ => ?_
  have hyG : y ∉ G₀ := EPilot.not_mem_of_normalizerMulAut_not_mem_range e' hyN hyout
  exact (even_F4_isConj_of_not_mem_of_odd hZ hn K hK e hyN htN
    (by rw [← hy]; exact pow_orderOf_eq_one y) ht2 hyG htG).symm

theorem false_of_simple_of_F4_odd [IsSimpleGroup G]
    (hZ : Odd (Nat.card (centralizer (G₀ : Set G)))) {n : ℕ} {K : Type} [Field K]
    (hK : Nat.card K = 2 ^ n) (e : G₀ ≃* adjointGroup .F4 K) {t : G}
    (htN : t ∈ normalizer (G₀ : Set G)) (ht : orderOf t = 2) (htG : t ∉ G₀)
    (huniq : ∀ g : G, g⁻¹ * t * g ∈ normalizer (G₀ : Set G) → g ∈ normalizer (G₀ : Set G)) :
    False :=
  CFSG.SeitzReduction.not_exists_normal_index_two_of_simple
    (EPilot.two_lt_card_of_odd_centralizer hZ ht htG)
    (exists_normal_index_two_of_F4_odd hZ hK e htN ht htG huniq)

theorem false_of_simple_of_F4_field_odd [IsSimpleGroup G]
    (hZ : Odd (Nat.card (centralizer (G₀ : Set G)))) {f : ℕ} {K₂ : Type} [Field K₂]
    (hK₂ : Nat.card K₂ = 2 ^ (2 * f)) (e : G₀ ≃* adjointGroup .F4 K₂) {t : G}
    (htN : t ∈ normalizer (G₀ : Set G)) (ht : orderOf t = 2) (htG : t ∉ G₀)
    (huniq : ∀ g : G, g⁻¹ * t * g ∈ normalizer (G₀ : Set G) → g ∈ normalizer (G₀ : Set G)) :
    False :=
  false_of_simple_of_F4_odd hZ hK₂ e htN ht htG huniq

end Ambient

end CFSG.SeitzReduction.F4Pilot

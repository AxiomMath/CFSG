module

public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogEvenSymplectic

public noncomputable section

namespace CFSG.ComponentClassification.UnbalancedCatalog

open CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial
open CFSG.ComponentClassification.CatalogueBAlternatingIsometry
open LinearMap (BilinForm)

theorem oddCore_statedSp_eq_bot {r f : ℕ} (hr : 1 ≤ r) (hf : 1 ≤ f) {K : Type} [Field K]
    (hK : Nat.card K = 2 ^ f) (h : 2 ≤ r ∨ 4 ≤ Nat.card K) :
    CFSG.oddCore (StatedSp r K) = ⊥ := by
  rcases h with h2 | h4
  · exact (even_symplectic_odd_core_including_field_two_rank_two h2 hf hK).1
  · have : CharP K 2 := finite_field_prime_power_characteristic Nat.prime_two hf hK
    have : Finite K := Nat.finite_of_card_ne_zero (by rw [hK]; positivity)
    have : NeZero r := ⟨by omega⟩
    have hbij := (UnitaryHigher.even_symplectic_semilinear_normal_form (r := r) hf hK).1
    let e : StatedSp r K ≃* StatedProj (StatedSp r K) := MulEquiv.ofBijective _ hbij
    have : IsSimpleGroup (StatedProj (StatedSp r K)) :=
      CFSG.ClassicalGroups.Symplectic.isSimpleGroup_statedProj_statedSp K r hr
        (Or.inl (Or.inr h4))
    have hcard := (SymplecticFlag.symplectic_higher_order_and_Sylow 2 (2 ^ f) hK
      (r := r) hr).1
    have heven : Even (Nat.card (StatedProj (StatedSp r K))) := by
      rw [← Nat.card_congr e.toEquiv, hcard]
      refine Even.mul_right ?_ _
      rw [Nat.even_pow]
      refine ⟨?_, by positivity⟩
      rw [Nat.even_pow]
      exact ⟨even_two, by omega⟩
    exact EvenCatalog.oddCore_eq_bot_of_mulEquiv e.symm
      (EvenCatalog.oddCore_eq_bot_of_isSimpleGroup heven)

theorem oddCore_isometryGroup_eq_bot_of_isAlt {f r : ℕ} (hf : 1 ≤ f) {K : Type} [Field K]
    (hK : Nat.card K = 2 ^ f) {V : Type*} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    (B : BilinForm K V) (hB : B.IsAlt) (hnd : B.Nondegenerate)
    (hdim : Module.finrank K V = 2 * r) (hr : 1 ≤ r) (h : 2 ≤ r ∨ 4 ≤ Nat.card K) :
    CFSG.oddCore (isometryGroup B) = ⊥ := by
  obtain ⟨e⟩ := exists_form_isometry B (pairedSympForm K r) hB hnd
    SymplecticFlag.pairedSympForm_isAlt SymplecticFlag.pairedSympForm_nondegenerate
    (by rw [hdim, SymplecticFlag.finrank_standard])
  have hcongr : LinearMap.BilinForm.congr (e : V ≃ₗ[K] (Fin r ⊕ Fin r → K)) B =
      pairedSympForm K r := by
    refine LinearMap.ext₂ fun x y => ?_
    rw [LinearMap.BilinForm.congr_apply]
    have h1 := e.map_app ((e : V ≃ₗ[K] (Fin r ⊕ Fin r → K)).symm y)
      ((e : V ≃ₗ[K] (Fin r ⊕ Fin r → K)).symm x)
    rw [← h1, ← LinearMap.BilinForm.IsometryEquiv.coe_toLinearEquiv,
      LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]
  let φ : isometryGroup B ≃* isometryGroup (pairedSympForm K r) :=
    (TauCeti.BilinForm.isometryGroupCongr B (e : V ≃ₗ[K] (Fin r ⊕ Fin r → K))).trans
      (MulEquiv.subgroupCongr (by rw [hcongr]))
  exact EvenCatalog.oddCore_eq_bot_of_mulEquiv
    (φ.trans CatalogueBSymplecticB.statedSpIsometryEquiv.symm).symm
    (oddCore_statedSp_eq_bot hr hf hK h)

theorem oddCore_eq_bot_of_normal_of_centralizer {Y : Type*} [Group Y] [Finite Y]
    {N : Subgroup Y} (hN : N.Normal) (hNodd : CFSG.oddCore N = ⊥)
    (hcent : ∀ y ∈ Subgroup.centralizer (N : Set Y), y ^ 2 = 1) :
    CFSG.oddCore Y = ⊥ := by
  set Q := CFSG.oddCore Y with hQ
  have hQnormal : Q.Normal := CFSG.oddCore_normal Y
  have hQN : Q.subgroupOf N ≤ CFSG.oddCore N := by
    apply EvenCatalog.le_oddCore_of_normal (hQnormal.subgroupOf N)
    have hdvd : Nat.card (Q.subgroupOf N) ∣ Nat.card Q := by
      rw [← Subgroup.card_map_of_injective N.subtype_injective, Subgroup.subgroupOf_map_subtype]
      exact Subgroup.card_dvd_of_le inf_le_left
    exact Odd.of_dvd_nat EvenCatalog.odd_card_oddCore hdvd
  rw [hNodd, le_bot_iff] at hQN
  rw [eq_bot_iff]
  intro q hq
  have hqc : q ∈ Subgroup.centralizer (N : Set Y) := by
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    have h1 : q * x * q⁻¹ * x⁻¹ ∈ Q := by
      have h2 : x * q⁻¹ * x⁻¹ ∈ Q := hQnormal.conj_mem _ (inv_mem hq) x
      have h3 := mul_mem hq h2
      rwa [show q * (x * q⁻¹ * x⁻¹) = q * x * q⁻¹ * x⁻¹ by group] at h3
    have h2 : q * x * q⁻¹ * x⁻¹ ∈ N := mul_mem (hN.conj_mem x hx q) (inv_mem hx)
    have h3 : (⟨_, h2⟩ : N) ∈ Q.subgroupOf N := h1
    rw [hQN, Subgroup.mem_bot] at h3
    have h4 : q * x * q⁻¹ * x⁻¹ = 1 := congrArg Subtype.val h3
    have h5 : q * x = x * q := by
      rw [mul_inv_eq_one, mul_inv_eq_iff_eq_mul] at h4
      exact h4
    exact h5.symm
  rw [Subgroup.mem_bot]
  by_contra hq1
  exact EvenCatalog.not_mem_oddCore_of_sq_eq_one hq1 (hcent q hqc) hq

end CFSG.ComponentClassification.UnbalancedCatalog

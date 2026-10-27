module

public import CFSG.HardMathSupport.Malle.Coordinator.CoverThreeNoInner.Normal
public import CFSG.HardMathSupport.Malle.Coordinator.CoverThreeNoInner.NormalizingLiftCore

public section

namespace CFSG.HardMathSupport.Malle.Coordinator.CoverThreeNoInner

open CFSG.Open CFSG.ComponentClassification.PerfectAutomorphisms

section Action

variable {Y : Type*} [Group Y] (K : Subgroup Y) [K.Normal] {M : Type*} [Group M]
  (e : K ⧸ Subgroup.center K ≃* M)

omit [K.Normal] in
theorem center_threeElement_pow_three [Finite Y]
    (hZ : (Nat.card (Subgroup.center K)).factorization 3 = 1) :
    ∀ z ∈ Subgroup.center K, (∃ m : ℕ, z ^ 3 ^ m = 1) → z ^ 3 = 1 := by
  intro z hz ⟨m, hm⟩
  have hdvd : orderOf z ∣ 3 ^ m := orderOf_dvd_of_pow_eq_one hm
  obtain ⟨a, ha, hord⟩ := (Nat.dvd_prime_pow Nat.prime_three).1 hdvd
  have hZd : orderOf (⟨z, hz⟩ : Subgroup.center K) ∣ Nat.card (Subgroup.center K) :=
    orderOf_dvd_natCard _
  rw [Subgroup.orderOf_mk, hord] at hZd
  have hpos : Nat.card (Subgroup.center K) ≠ 0 := Nat.card_pos.ne'
  have h1 : a ≤ (Nat.card (Subgroup.center K)).factorization 3 :=
    (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_three hpos).1 hZd
  rw [hZ] at h1
  have h2 : orderOf z ∣ 3 := by
    rw [hord]
    exact (pow_dvd_pow 3 h1).trans (by simp)
  exact orderOf_dvd_iff_pow_eq_one.1 h2

theorem exists_normalizing_lift [Finite Y]
    (hZ : (Nat.card (Subgroup.center K)).factorization 3 = 1) {y : Y} (hy : y ^ 3 = 1) {x : M}
    (hx : modelAct K e y x = x) :
    ∃ k : K, e (QuotientGroup.mk k) = x ∧
      ∃ z ∈ (Subgroup.center K).map K.subtype, z ^ 3 = 1 ∧ (k : Y) * y * (k : Y)⁻¹ = z * y := by
  have hZ3 := center_threeElement_pow_three K hZ
  set σ : MulAut K := MulAut.conjNormal (H := K) y with hσ
  have hσ3 : σ ^ 3 = 1 := by rw [hσ, ← map_pow, hy, map_one]
  obtain ⟨ℓ, hℓ⟩ := QuotientGroup.mk_surjective (e.symm x)
  have hxℓ : e (QuotientGroup.mk ℓ) = x := by rw [hℓ, MulEquiv.apply_symm_apply]
  have hfix : (QuotientGroup.mk (σ ℓ) : K ⧸ Subgroup.center K) = QuotientGroup.mk ℓ := by
    have h1 := modelAct_apply_mk K e y ℓ
    rw [hxℓ, hx] at h1
    exact e.injective (h1.symm.trans hxℓ.symm)
  have hu : (σ ℓ)⁻¹ * ℓ ∈ Subgroup.center K := QuotientGroup.eq.mp hfix
  have hσℓ : σ ℓ = ((σ ℓ)⁻¹ * ℓ)⁻¹ * ℓ := by
    have h3 := Subgroup.mem_center_iff.mp (Subgroup.inv_mem _ hu) ℓ
    calc σ ℓ = ℓ * ((σ ℓ)⁻¹ * ℓ)⁻¹ := by group
      _ = ((σ ℓ)⁻¹ * ℓ)⁻¹ * ℓ := h3
  obtain ⟨k, hkZ, w, hw, hw3, hkσ⟩ := exists_sigma_normalizing_lift σ hσ3 hZ3
    (Subgroup.inv_mem _ hu) hσℓ
  refine ⟨k, ?_, ((w⁻¹ : K) : Y), ⟨w⁻¹, Subgroup.inv_mem _ hw, rfl⟩, ?_, ?_⟩
  · rw [← hxℓ]
    congr 1
    apply QuotientGroup.eq.mpr
    have hz'' := Subgroup.inv_mem _ hkZ
    have h2 := Subgroup.mem_center_iff.mp hz'' ℓ⁻¹
    have h3 : k⁻¹ * ℓ = (k * ℓ⁻¹)⁻¹ := by
      calc k⁻¹ * ℓ = ℓ⁻¹ * (k * ℓ⁻¹)⁻¹ * ℓ := by group
        _ = (k * ℓ⁻¹)⁻¹ * ℓ⁻¹ * ℓ := by rw [h2]
        _ = (k * ℓ⁻¹)⁻¹ := by group
    rw [h3]
    exact hz''
  · rw [← Subgroup.coe_pow, inv_pow, hw3, inv_one]
    rfl
  · have h : y * (k : Y) * y⁻¹ = (w : Y) * k := by
      have := congrArg (fun a : K => (a : Y)) hkσ
      simpa [hσ, MulAut.conjNormal_apply] using this
    have h' : y * (k : Y) = (w : Y) * k * y := by
      calc y * (k : Y) = (y * (k : Y) * y⁻¹) * y := by group
        _ = (w : Y) * k * y := by rw [h]
    calc (k : Y) * y * (k : Y)⁻¹ = ((w : Y)⁻¹ * ((w : Y) * k * y)) * (k : Y)⁻¹ := by group
      _ = ((w : Y)⁻¹ * (y * (k : Y))) * (k : Y)⁻¹ := by rw [h']
      _ = ((w⁻¹ : K) : Y) * y := by simp only [Subgroup.coe_inv]; group

end Action

end CFSG.HardMathSupport.Malle.Coordinator.CoverThreeNoInner

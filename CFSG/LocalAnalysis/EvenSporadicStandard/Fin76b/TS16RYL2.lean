module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.RootFacts
public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.TS16RYT2

public section

namespace CFSG.EvenSporadicStandard.Fin76b

open Subgroup Pointwise

section Tools

variable {X : Type*} [Group X]

theorem rootGroup_stable {t : X} (r : MulAut X) (hrt : r t = t) :
    ∀ y ∈ rootGroup X t, r y ∈ rootGroup X t := by
  intro y hy
  induction hy using Subgroup.closure_induction with
  | mem x hx =>
    apply Subgroup.subset_closure
    show r x * r x = t
    rw [← map_mul, show x * x = t from hx, hrt]
  | one => rw [map_one]; exact one_mem _
  | mul a b _ _ ha hb => rw [map_mul]; exact mul_mem ha hb
  | inv a _ ha => rw [map_inv]; exact inv_mem ha

end Tools

variable {G : Type} [Group G] {L : Subgroup G} {z : G}

theorem conj_injective_of_center (hTD : ThetaData G L z) :
    Function.Injective (MulAut.conj : ↥L →* MulAut ↥L) := by
  intro a b hab
  have h : b⁻¹ * a = 1 := by
    apply hTD.center_triv
    intro m
    have h1 : MulAut.conj (b⁻¹ * a) = 1 := by rw [map_mul, map_inv, hab, inv_mul_cancel]
    have h2 := congrArg (fun φ : MulAut ↥L => φ m) h1
    simp only [MulAut.conj_apply, MulAut.one_apply] at h2
    have h3 : (b⁻¹ * a) * m = m * (b⁻¹ * a) := by
      calc (b⁻¹ * a) * m = (b⁻¹ * a * m * (b⁻¹ * a)⁻¹) * (b⁻¹ * a) := by group
        _ = m * (b⁻¹ * a) := by rw [h2]
    exact h3.symm
  exact (inv_mul_eq_one.1 h).symm

theorem exists_mul_of_mem_sup_sigma (hTD : ThetaData G L z) {σ : G}
    (hσH : σ ∈ centralizer ({z} : Set G)) (hσ2 : σ * σ = 1) {x : G} (hx : x ∈ L ⊔ zpowers σ) :
    ∃ ℓ ∈ L, x = ℓ ∨ x = ℓ * σ := by
  have hle : zpowers σ ≤ normalizer (L : Set G) := zpowers_le.2 (hTD.le_normalizer hσH)
  have h := Subgroup.coe_mul_of_right_le_normalizer_left L (zpowers σ) hle
  have hx' : x ∈ ((L : Set G) * (zpowers σ : Set G)) := by
    rw [← h]; exact hx
  obtain ⟨a, ha, b, hb, rfl⟩ := hx'
  rcases mem_zpowers_sq_eq_one hσ2 hb with rfl | rfl
  · exact ⟨a, ha, Or.inl (mul_one a)⟩
  · exact ⟨a, ha, Or.inr rfl⟩

theorem ThetaData.theta_injOn (hTD : ThetaData G L z) (hz2 : z * z = 1) (hzL : z ∉ L) {σ : G}
    (hσH : σ ∈ centralizer ({z} : Set G)) (hσ2 : σ * σ = 1) (hσL : σ ∉ L ⊔ zpowers z)
    {g : ↥(centralizer ({z} : Set G))} (hg : (g : G) ∈ L ⊔ zpowers σ) (h1 : hTD.theta g = 1) :
    (g : G) = 1 := by
  rcases mem_zpowers_sq_eq_one hz2 (hTD.theta_eq_one h1) with h | h
  · exact h
  · exfalso
    obtain ⟨ℓ, hℓ, hge | hge⟩ := exists_mul_of_mem_sup_sigma hTD hσH hσ2 hg
    · rw [h] at hge
      exact hzL (hge ▸ hℓ)
    · rw [h] at hge
      apply hσL
      have : σ = ℓ⁻¹ * z := by rw [hge]; group
      rw [this]
      exact mul_mem (mem_sup_left (inv_mem hℓ)) (mem_sup_right (mem_zpowers z))

end CFSG.EvenSporadicStandard.Fin76b

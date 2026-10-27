module

public import Mathlib.Algebra.Group.End
import Mathlib.Tactic.Group

public section

namespace CFSG.LocalAnalysis.RankThreeUC.S15.KFactF2Proof

variable {M : Type*} [CommGroup M]

structure A4Rel (σ τ α : MulAut M) : Prop where
  sq_σ : ∀ x, σ (σ x) = x
  sq_τ : ∀ x, τ (τ x) = x
  comm : ∀ x, σ (τ x) = τ (σ x)
  cube : ∀ x, α (α (α x)) = x
  ασ : ∀ x, α (σ x) = τ (α x)
  ατ : ∀ x, α (τ x) = σ (τ (α x))

variable {σ τ α : MulAut M}

theorem A4Rel.σα (h : A4Rel σ τ α) (x : M) : σ (α x) = α (σ (τ x)) := by
  rw [h.ασ (τ x), h.ατ x, ← h.comm, h.sq_τ]

theorem A4Rel.step_a (h : A4Rel σ τ α) {z : M} (hs : σ z = z) (ht : τ z = z⁻¹) :
    τ (α z) = α z ∧ σ (α z) = (α z)⁻¹ := by
  refine ⟨?_, ?_⟩
  · rw [← h.ασ, hs]
  · rw [h.σα, ht, map_inv, hs, map_inv]

theorem A4Rel.step_b (h : A4Rel σ τ α) {z : M} (hs : σ z = z⁻¹) (ht : τ z = z) :
    σ (α z) = (α z)⁻¹ ∧ τ (α z) = (α z)⁻¹ := by
  refine ⟨?_, ?_⟩
  · rw [h.σα, ht, hs, map_inv]
  · rw [← h.ασ, hs, map_inv]

@[expose] def proj (σ τ : MulAut M) (z : M) : M := z * σ z * (τ z)⁻¹ * (σ (τ z))⁻¹

theorem proj_mul (σ τ : MulAut M) (x y : M) : proj σ τ (x * y) = proj σ τ x * proj σ τ y := by
  simp only [proj, map_mul, mul_inv]
  ac_rfl

theorem proj_one (σ τ : MulAut M) : proj σ τ 1 = 1 := by simp [proj]

theorem proj_σ {z : M} (hs : σ z = z) (ht : τ z = z⁻¹) : proj σ τ z = z * z * z * z := by
  simp only [proj, ht, hs, map_inv, inv_inv]

theorem proj_τ {z : M} (hs : σ z = z⁻¹) (ht : τ z = z) : proj σ τ z = 1 := by
  simp only [proj, ht, hs, inv_inv]
  group

theorem proj_ρ {z : M} (hs : σ z = z⁻¹) (ht : τ z = z⁻¹) : proj σ τ z = 1 := by
  simp only [proj, ht, hs, map_inv, inv_inv]
  group

theorem A4Rel.proj_prop (h : A4Rel σ τ α) (u : M) :
    σ (proj σ τ u) = proj σ τ u ∧ τ (proj σ τ u) = (proj σ τ u)⁻¹ := by
  refine ⟨?_, ?_⟩
  · simp only [proj, map_mul, map_inv, h.sq_σ]
    ac_rfl
  · simp only [proj, map_mul, map_inv, ← h.comm, h.sq_τ, mul_inv, inv_inv]
    ac_rfl

theorem A4Rel.proj_eq_one (h : A4Rel σ τ α) (hodd : ∀ x : M, x * x = 1 → x = 1)
    (hfix : ∀ x : M, α x = x → x = 1) (u : M) : proj σ τ u = 1 := by
  set v := proj σ τ u with hv
  obtain ⟨hs, ht⟩ := h.proj_prop u
  obtain ⟨ht1, hs1⟩ := h.step_a hs ht
  obtain ⟨hs2, ht2⟩ := h.step_b hs1 ht1
  have hw : α (v * α v * α (α v)) = v * α v * α (α v) := by
    rw [map_mul, map_mul, h.cube]
    ac_rfl
  have hw1 : v * α v * α (α v) = 1 := hfix _ hw
  have hp : proj σ τ (v * α v * α (α v)) = 1 := by rw [hw1, proj_one]
  rw [proj_mul, proj_mul, proj_σ hs ht, proj_τ hs1 ht1, proj_ρ hs2 ht2, mul_one, mul_one] at hp
  exact hodd v (hodd (v * v) (by rw [← hp]; ac_rfl))

theorem A4Rel.eσ (h : A4Rel σ τ α) (hodd : ∀ x : M, x * x = 1 → x = 1)
    (hfix : ∀ x : M, α x = x → x = 1) (u : M) : u * σ u = τ u * σ (τ u) := by
  have e := h.proj_eq_one hodd hfix u
  simp only [proj] at e
  have e1 := mul_inv_eq_one.1 e
  rw [mul_inv_eq_iff_eq_mul] at e1
  rw [e1, mul_comm]

theorem A4Rel.eρ (h : A4Rel σ τ α) (hodd : ∀ x : M, x * x = 1 → x = 1)
    (hfix : ∀ x : M, α x = x → x = 1) (u : M) : u * σ (τ u) = σ u * τ u := by
  have e := h.eσ hodd hfix (α u)
  rw [h.σα, ← h.ατ, ← h.ασ, ← map_mul α, ← map_mul α] at e
  exact α.injective e

theorem A4Rel.eτ (h : A4Rel σ τ α) (hodd : ∀ x : M, x * x = 1 → x = 1)
    (hfix : ∀ x : M, α x = x → x = 1) (u : M) : u * τ u = σ (τ u) * σ u := by
  have e := h.eρ hodd hfix (α u)
  rw [← h.ατ, h.σα, ← h.ασ, ← map_mul α, ← map_mul α] at e
  exact α.injective e

theorem A4Rel.apply_eq (h : A4Rel σ τ α) (hodd : ∀ x : M, x * x = 1 → x = 1)
    (hfix : ∀ x : M, α x = x → x = 1) (u : M) : σ u = u := by
  have e2 := h.eτ hodd hfix u
  have e3 := h.eρ hodd hfix u
  have e4 : (u * u) * (τ u * σ (τ u)) = (σ u * σ u) * (τ u * σ (τ u)) := by
    calc u * u * (τ u * σ (τ u)) = (u * τ u) * (u * σ (τ u)) := by ac_rfl
      _ = (σ (τ u) * σ u) * (σ u * τ u) := by rw [e2, e3]
      _ = σ u * σ u * (τ u * σ (τ u)) := by ac_rfl
  have e5 : u * u = σ u * σ u := mul_right_cancel e4
  have e6 : (u * (σ u)⁻¹) * (u * (σ u)⁻¹) = 1 := by
    calc (u * (σ u)⁻¹) * (u * (σ u)⁻¹) = (u * u) * ((σ u)⁻¹ * (σ u)⁻¹) := by ac_rfl
      _ = (σ u * σ u) * ((σ u)⁻¹ * (σ u)⁻¹) := by rw [e5]
      _ = 1 := by group
  exact (mul_inv_eq_one.1 (hodd _ e6)).symm

end CFSG.LocalAnalysis.RankThreeUC.S15.KFactF2Proof

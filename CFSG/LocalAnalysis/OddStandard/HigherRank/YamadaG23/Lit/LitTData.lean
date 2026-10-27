module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Lit.LitDefs
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Lit.LitInputs

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

open Subgroup

structure LitTData {X G : Type*} [Group X] [Group G] (π : X →* G) (Z : Subgroup X) [Z.Normal]
    (τ : X ≃* X) (σ : G ≃* G) : Prop where
  surj : Function.Surjective π
  ker : π.ker = litP Z
  invol : ∀ x, τ (τ x) = x
  Z_inv : ∀ x ∈ Z, τ x ∈ Z
  comm : ∀ x, σ (π x) = π (τ x)

variable {X G : Type*} [Group X] [Group G] {π : X →* G} {Z : Subgroup X} [Z.Normal]
  {τ : X ≃* X} {σ : G ≃* G}

theorem LitTData.invol_G (d : LitTData π Z τ σ) (y : G) : σ (σ y) = y := by
  obtain ⟨x, rfl⟩ := d.surj y
  rw [d.comm, d.comm, d.invol]

theorem LitTData.fix_of_mem_tsub (d : LitTData π Z τ σ) {x : X} (hx : x ∈ litTSub τ Z) :
    σ (π x) = π x := by
  rw [d.comm]
  have h : τ x * x⁻¹ ∈ π.ker := by
    rw [d.ker]
    exact (le_sup_left : Z ≤ Z ⊔ CFSG.oddCore X) hx
  have h1 : π (τ x * x⁻¹) = 1 := h
  rw [map_mul, map_inv, mul_inv_eq_one] at h1
  exact h1

@[expose] def litRestrict (τ : X ≃* X) (H : Subgroup X) (hH : ∀ x, x ∈ H ↔ τ x ∈ H) :
    ↥H ≃* ↥H where
  toFun x := ⟨τ x, (hH x).mp x.2⟩
  invFun x := ⟨τ.symm x, (hH (τ.symm x)).mpr (by simpa using x.2)⟩
  left_inv x := by ext; simp
  right_inv x := by ext; simp
  map_mul' x y := by ext; simp

theorem litRestrict_coe (H : Subgroup X) (hH : ∀ x, x ∈ H ↔ τ x ∈ H) (x : ↥H) :
    ((litRestrict τ H hH x : ↥H) : X) = τ x := rfl

end CFSG.OddStandard.HigherRank.YamadaG23

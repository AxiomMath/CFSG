module

public import CFSG.LargeExtraspecial.S13TwoA

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.S13

open Subgroup Module QuadraticMap CFSG.RankThree.OrthogonalInvolutions
open CFSG.LargeExtraspecial.S4 CFSG.LargeExtraspecial.S6 CFSG.LargeExtraspecial.S10

variable {G : Type*} [Group G] [Finite G] {S : Setting G} {g g₁ : G} {K : Subgroup S.O}

variable (S) in
@[expose] noncomputable def perp (W : Submodule (ZMod 2) S.Qt) : Submodule (ZMod 2) S.Qt where
  carrier := {v | ∀ w ∈ W, polar S.q w v = 0}
  add_mem' := fun {u v} hu hv w hw => by rw [polar_add_right, hu w hw, hv w hw, add_zero]
  zero_mem' := fun w _ => polar_zero_right S.q w
  smul_mem' := fun c v hv w hw => by rw [polar_smul_right, hv w hw, smul_zero]

theorem mem_perp {W : Submodule (ZMod 2) S.Qt} {v : S.Qt} :
    v ∈ perp S W ↔ ∀ w ∈ W, polar S.q w v = 0 := Iff.rfl

theorem apply_mem_perp {D : Submodule (ZMod 2) S.Qt} {x : S.O}
    (hx' : ∀ d ∈ D, ((x⁻¹ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) d ∈ D) {v : S.Qt} (hv : v ∈ perp S D) :
    (x : S.Qt ≃ₗ[ZMod 2] S.Qt) v ∈ perp S D := by
  rw [mem_perp] at hv ⊢
  intro d hd
  have h1 := hv _ (hx' d hd)
  rw [← TauCeti.QuadraticMap.polar_apply_of_mem_orthogonalGroup x.2] at h1
  simpa [apply_inv_apply_O] using h1

variable (S) in
@[expose] noncomputable def stab2 (D : Submodule (ZMod 2) S.Qt) : Subgroup S.O where
  carrier := {x | (∀ d ∈ D, (x : S.Qt ≃ₗ[ZMod 2] S.Qt) d ∈ D) ∧
    (∀ d ∈ D, ((x⁻¹ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) d ∈ D) ∧
    ∀ w ∈ perp S D, (x : S.Qt ≃ₗ[ZMod 2] S.Qt) w - w ∈ D}
  mul_mem' := by
    rintro x y ⟨hx1, hx2, hx3⟩ ⟨hy1, hy2, hy3⟩
    refine ⟨fun d hd => ?_, fun d hd => ?_, fun w hw => ?_⟩
    · rw [Subgroup.coe_mul, LinearEquiv.mul_apply]
      exact hx1 _ (hy1 d hd)
    · rw [mul_inv_rev, Subgroup.coe_mul, LinearEquiv.mul_apply]
      exact hy2 _ (hx2 d hd)
    · rw [Subgroup.coe_mul, LinearEquiv.mul_apply]
      have h1 := hx3 _ (apply_mem_perp hy2 hw)
      have h2 := hx1 _ (hy3 w hw)
      rw [map_sub] at h2
      have e : (x : S.Qt ≃ₗ[ZMod 2] S.Qt) ((y : S.Qt ≃ₗ[ZMod 2] S.Qt) w) - w =
          ((x : S.Qt ≃ₗ[ZMod 2] S.Qt) ((y : S.Qt ≃ₗ[ZMod 2] S.Qt) w) -
            (y : S.Qt ≃ₗ[ZMod 2] S.Qt) w) + ((y : S.Qt ≃ₗ[ZMod 2] S.Qt) w - w) := by abel
      rw [e]
      exact add_mem h1 (hy3 w hw)
  one_mem' := ⟨fun d hd => hd, fun d hd => by simpa using hd, fun w _ => by simp⟩
  inv_mem' := by
    rintro x ⟨hx1, hx2, hx3⟩
    refine ⟨hx2, fun d hd => by simpa using hx1 d hd, fun w hw => ?_⟩
    have hw' := apply_mem_perp (x := x⁻¹) (fun d hd => by simpa using hx1 d hd) hw
    have h1 := hx3 _ hw'
    rw [show (x : S.Qt ≃ₗ[ZMod 2] S.Qt) (((x⁻¹ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) w) = w from
      apply_inv_apply_O x w] at h1
    rw [← neg_sub]
    exact neg_mem h1

theorem mem_stab2 {D : Submodule (ZMod 2) S.Qt} {x : S.O} :
    x ∈ stab2 S D ↔ (∀ d ∈ D, (x : S.Qt ≃ₗ[ZMod 2] S.Qt) d ∈ D) ∧
      (∀ d ∈ D, ((x⁻¹ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) d ∈ D) ∧
      ∀ w ∈ perp S D, (x : S.Qt ≃ₗ[ZMod 2] S.Qt) w - w ∈ D := Iff.rfl

theorem Ebar_le_stab2 (Y : Hyp13 S g K) {F₁ : Submodule (ZMod 2) S.Qt}
    (hperp : ∀ u ∈ Fbar S g K, ∀ v ∈ F₁, polar S.q u v = 0) :
    Ebar S g K ≤ stab2 S (Fbar S g K ⊔ F₁) := by
  intro e he
  have key : ∀ e ∈ Ebar S g K, ∀ d ∈ (Fbar S g K ⊔ F₁ : Submodule (ZMod 2) S.Qt),
      (e : S.Qt ≃ₗ[ZMod 2] S.Qt) d ∈ (Fbar S g K ⊔ F₁ : Submodule (ZMod 2) S.Qt) := by
    intro e he d hd
    have h1 := Ebar_apply_sub_mem_Fbar_of_perp Y hperp he hd
    have e1 : (e : S.Qt ≃ₗ[ZMod 2] S.Qt) d = ((e : S.Qt ≃ₗ[ZMod 2] S.Qt) d - d) + d := by abel
    rw [e1]
    exact add_mem (Submodule.mem_sup_left h1) hd
  refine ⟨key e he, key e⁻¹ (inv_mem he), fun w hw => ?_⟩
  refine Submodule.mem_sup_left (Y.Ebar_apply_sub_mem_Fbar (fun f hf => ?_) he)
  rw [QuadraticMap.polar_comm]
  exact (mem_perp.mp hw) f (Submodule.mem_sup_left hf)

end CFSG.LargeExtraspecial.S13

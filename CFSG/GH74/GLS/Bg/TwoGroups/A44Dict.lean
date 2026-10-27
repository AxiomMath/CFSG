module

public import CFSG.GH74.GLS.Bg.TwoGroups.A44Model
public import CFSG.GH74.GLS.Bg.TwoGroups.Statements

public section

namespace CFSG.GH74.GLS.Bg.TwoGroups

namespace A44

open Multiplicative

variable {B : Type} [CommGroup B] (e : B ≃* Z4Z4)

@[expose] def vec (b : B) : ZMod 4 × ZMod 4 := toAdd (e b)

theorem vec_mul (b b' : B) : vec e (b * b') = vec e b + vec e b' := by
  simp [vec, toAdd_mul]

theorem vec_one : vec e (1 : B) = 0 := by simp [vec]

theorem vec_inv (b : B) : vec e b⁻¹ = - vec e b := by simp [vec]

theorem vec_pow_two (b : B) : vec e (b ^ 2) = vec e b + vec e b := by
  rw [pow_two, vec_mul]

theorem vec_injective : Function.Injective (vec e) := by
  intro b b' h
  exact e.injective (Multiplicative.toAdd.injective h)

theorem vec_surjective : Function.Surjective (vec e) := by
  intro w
  exact ⟨e.symm (ofAdd w), by simp [vec]⟩

theorem vec_eq_zero_iff (b : B) : vec e b = 0 ↔ b = 1 := by
  constructor
  · intro h
    apply vec_injective e
    rw [h, vec_one]
  · rintro rfl; exact vec_one e

theorem sq_eq_one_iff (b : B) : b ^ 2 = 1 ↔ vec e b + vec e b = 0 := by
  rw [← vec_pow_two, vec_eq_zero_iff]

theorem mem_ZB_iff (b : B) : b ∈ ZB B ↔ vec e b + vec e b = 0 := by
  rw [mem_ZB, sq_eq_one_iff]

theorem vec_phi (φ : MulAut B) (b : B) : vec e (φ b) = (phiB e φ).1.act (vec e b) :=
  toAdd_phiB e φ b

theorem mem_CB_iff (φ : MulAut B) (b : B) :
    b ∈ CB B φ ↔ (phiB e φ).1.act (vec e b) = vec e b := by
  show φ b = b ↔ _
  rw [← vec_phi, ← (vec_injective e).eq_iff]

theorem vec_quot (φ : MulAut B) (b : B) :
    vec e (b⁻¹ * φ b) = (phiB e φ).1.act (vec e b) - vec e b := by
  rw [vec_mul, vec_inv, vec_phi]; abel

theorem vec_quot' (φ : MulAut B) (b : B) :
    vec e (φ b * b⁻¹) = (phiB e φ).1.act (vec e b) - vec e b := by
  rw [vec_mul, vec_inv, vec_phi]; abel

theorem mem_A0_iff (φ : MulAut B) :
    φ ∈ A0 B ↔ ∀ w : ZMod 4 × ZMod 4,
      ((phiB e φ).1.act w - w) + ((phiB e φ).1.act w - w) = 0 := by
  show (∀ b : B, φ b * b⁻¹ ∈ ZB B) ↔ _
  constructor
  · intro h w
    obtain ⟨b, rfl⟩ := vec_surjective e w
    have := (mem_ZB_iff e _).mp (h b)
    rwa [vec_quot'] at this
  · intro h b
    rw [mem_ZB_iff, vec_quot']
    exact h _

end A44

end CFSG.GH74.GLS.Bg.TwoGroups

module

public import Mathlib.Algebra.Module.ZMod
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.FieldTheory.Finiteness
public import Mathlib.Algebra.Field.ZMod

public section

namespace CFSG.GF2Type.Smith1980Orth.W4Sigma

open Subgroup Module

variable {G : Type*} [Group G]

structure ElemAb (G : Type*) [Group G] where
  E : Subgroup G
  comm : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a
  two : ∀ a ∈ E, a * a = 1

namespace ElemAb

variable (e : ElemAb G)

instance instCommGroup : CommGroup e.E :=
  { (inferInstance : Group e.E) with mul_comm := fun a b => Subtype.ext (e.comm a a.2 b b.2) }

instance instModule : Module (ZMod 2) (Additive e.E) :=
  AddCommGroup.zmodModule fun a => by
    show (Additive.toMul a) ^ 2 = 1
    rw [pow_two]
    exact Subtype.ext (e.two _ (Additive.toMul a).2)

variable {e}

@[expose] def vec (a : e.E) : Additive e.E := Additive.ofMul a

theorem vec_mul (a b : e.E) : vec (a * b) = vec a + vec b := rfl

theorem vec_one : vec (1 : e.E) = 0 := rfl

theorem vec_injective : Function.Injective (vec : e.E → Additive e.E) :=
  Additive.ofMul.injective

variable (e)

@[expose] def conjMulEquiv (g : normalizer (e.E : Set G)) : e.E ≃* e.E where
  toFun a := ⟨(g : G) * a * (g : G)⁻¹, (mem_normalizer_iff.mp g.2 a).mp a.2⟩
  invFun a := ⟨(g : G)⁻¹ * a * (g : G), by
    have h := (mem_normalizer_iff.mp g.2 ((g : G)⁻¹ * a * (g : G))).mpr
    apply h
    simpa [mul_assoc] using a.2⟩
  left_inv a := Subtype.ext (by simp [mul_assoc])
  right_inv a := Subtype.ext (by simp [mul_assoc])
  map_mul' a b := Subtype.ext (by simp [mul_assoc])

@[expose] noncomputable def conjLin (g : normalizer (e.E : Set G)) :
    Additive e.E ≃ₗ[ZMod 2] Additive e.E :=
  (MulEquiv.toAdditive (e.conjMulEquiv g)).toLinearEquiv fun c x =>
    ZMod.map_smul (MulEquiv.toAdditive (e.conjMulEquiv g)) c x

theorem conjLin_vec (g : normalizer (e.E : Set G)) (a : e.E) :
    e.conjLin g (vec a) = vec (e.conjMulEquiv g a) := rfl

theorem coe_conjMulEquiv (g : normalizer (e.E : Set G)) (a : e.E) :
    ((e.conjMulEquiv g a : e.E) : G) = (g : G) * a * (g : G)⁻¹ := rfl

@[expose] noncomputable def conjHom :
    normalizer (e.E : Set G) →* (Additive e.E ≃ₗ[ZMod 2] Additive e.E) where
  toFun := e.conjLin
  map_one' := LinearEquiv.ext fun a => by
    obtain ⟨b, rfl⟩ : ∃ b : e.E, vec b = a := ⟨Additive.toMul a, rfl⟩
    rw [conjLin_vec]
    show vec _ = vec b
    exact congrArg vec (Subtype.ext (by simp [coe_conjMulEquiv]))
  map_mul' g h := LinearEquiv.ext fun a => by
    obtain ⟨b, rfl⟩ : ∃ b : e.E, vec b = a := ⟨Additive.toMul a, rfl⟩
    rw [LinearEquiv.mul_apply, conjLin_vec, conjLin_vec, conjLin_vec]
    exact congrArg vec (Subtype.ext (by simp [coe_conjMulEquiv, mul_assoc]))

theorem conjHom_vec (g : normalizer (e.E : Set G)) (a : e.E) :
    e.conjHom g (vec a) = vec (e.conjMulEquiv g a) := rfl

theorem conjHom_eq_one_iff (g : normalizer (e.E : Set G)) :
    e.conjHom g = 1 ↔ ∀ a ∈ e.E, (g : G) * a = a * g := by
  constructor
  · intro h a ha
    have h1 : vec (e.conjMulEquiv g ⟨a, ha⟩) = vec ⟨a, ha⟩ :=
      congrArg (fun f => f (vec (⟨a, ha⟩ : e.E))) h
    have h2 : (g : G) * a * (g : G)⁻¹ = a := congrArg Subtype.val (vec_injective h1)
    calc (g : G) * a = (g : G) * a * (g : G)⁻¹ * g := by group
      _ = a * g := by rw [h2]
  · intro h
    refine LinearEquiv.ext fun x => ?_
    obtain ⟨b, rfl⟩ : ∃ b : e.E, vec b = x := ⟨Additive.toMul x, rfl⟩
    rw [conjHom_vec]
    show vec _ = vec b
    refine congrArg vec (Subtype.ext ?_)
    rw [coe_conjMulEquiv, h b b.2, mul_inv_cancel_right]

variable [Finite G]

instance : Finite (Additive e.E) := inferInstanceAs (Finite e.E)

instance : FiniteDimensional (ZMod 2) (Additive e.E) := Module.Finite.of_finite

theorem card_eq_two_pow_finrank : Nat.card e.E = 2 ^ finrank (ZMod 2) (Additive e.E) := by
  have : Fintype (Additive e.E) := Fintype.ofFinite _
  have h := Module.card_eq_pow_finrank (K := ZMod 2) (V := Additive e.E)
  rw [ZMod.card] at h
  rw [← h, ← Nat.card_eq_fintype_card]
  exact Nat.card_congr (Equiv.refl _)

end ElemAb

end CFSG.GF2Type.Smith1980Orth.W4Sigma

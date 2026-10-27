module

public import CFSG.Blueprint.NativeSporadic
public import CFSG.Open.LocalVocabulary

public section

namespace CFSG.EvenSporadicStandard.Wong77

open Subgroup CFSG.Blueprint.NativeSporadic
open scoped IsMulCommutative

section Vector

variable {G : Type*} [Group G] {E : Subgroup G} [IsMulCommutative E]

abbrev vecModule (hE : ∀ x ∈ E, x ^ 2 = 1) : Module (ZMod 2) (Additive E) :=
  AddCommGroup.zmodModule fun x => by
    have hx : x.toMul ^ 2 = 1 := Subtype.ext (by simpa using hE _ x.toMul.2)
    rw [← ofMul_toMul x, ← ofMul_pow, hx, ofMul_one]

end Vector

theorem finrank_zmod_two_eq_of_natCard {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] {n : ℕ}
    (h : Nat.card V = 2 ^ n) : Module.finrank (ZMod 2) V = n := by
  have : Finite V := Nat.finite_of_card_ne_zero (by rw [h]; positivity)
  have : Module.Finite (ZMod 2) V := Module.Finite.of_finite
  have h2 := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := V)
  rw [h, Nat.card_zmod] at h2
  exact (Nat.pow_right_injective le_rfl h2).symm

section Conjugation

variable {G : Type*} [Group G] (E : Subgroup G) [IsMulCommutative E]
  [Module (ZMod 2) (Additive E)]

@[expose] def linearAut : MulAut E →* (Additive E ≃ₗ[ZMod 2] Additive E) where
  toFun σ := (MulEquiv.toAdditive σ).toLinearEquiv fun c x =>
    ZMod.map_smul (MulEquiv.toAdditive σ) c x
  map_one' := by ext; rfl
  map_mul' _ _ := by ext; rfl

variable {E}

theorem linearAut_apply (σ : MulAut E) (e : E) :
    linearAut E σ (Additive.ofMul e) = Additive.ofMul (σ e) := rfl

theorem linearAut_injective : Function.Injective (linearAut E) := fun _ _ h =>
  MulEquiv.ext fun e => Additive.ofMul.injective (congrArg (· (Additive.ofMul e)) h)

end Conjugation

end CFSG.EvenSporadicStandard.Wong77

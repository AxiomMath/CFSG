module

public import CFSG.Open.LocalVocabulary

public section

namespace CFSG.EvenSporadicStandard.HNRecog.Harada

open Subgroup CFSG.Open

variable {X : Type} [Group X]

theorem L28_exists_action {A : Subgroup X} (hA : IsElemAbelian 2 A) (hcard : Nat.card A = 2 ^ 8) :
    ∃ (V : Type) (_ : AddCommGroup V) (_ : Module (ZMod 2) V) (_ : Finite V)
      (e : ↥A ≃* Multiplicative V) (act : ↥(normalizer (A : Set X)) →* (V ≃ₗ[ZMod 2] V)),
      Module.finrank (ZMod 2) V = 8 ∧
      ∀ (n : ↥(normalizer (A : Set X))) (a : ↥A),
        ((e.symm (Multiplicative.ofAdd (act n (Multiplicative.toAdd (e a)))) : ↥A) : X) =
          (n : X) * (a : X) * (n : X)⁻¹ := by
  letI : CommGroup ↥A :=
    { (inferInstance : Group ↥A) with mul_comm := fun a b => hA.1.is_comm.comm a b }
  have hsq : ∀ a : ↥A, a * a = 1 := by
    intro a
    apply Subtype.ext
    simpa [pow_two] using hA.2 a a.2
  have hsmul : ∀ x : Additive ↥A, (2 : ℕ) • x = 0 := by
    intro x
    apply (Additive.toMul (α := ↥A)).injective
    simp [pow_two, hsq x.toMul]
  letI : Module (ZMod 2) (Additive ↥A) := AddCommGroup.zmodModule (n := 2) hsmul
  haveI : Finite (Additive ↥A) := Nat.finite_of_card_ne_zero (by
    rw [Nat.card_congr Additive.toMul, hcard]
    exact pow_ne_zero 8 (by norm_num))
  haveI : Fintype (Additive ↥A) := Fintype.ofFinite _
  have hfr : Module.finrank (ZMod 2) (Additive ↥A) = 8 := by
    have hcard' : Fintype.card (Additive ↥A) = 2 ^ 8 := by
      rw [← Nat.card_eq_fintype_card, Nat.card_congr Additive.toMul, hcard]
    have h := Module.card_eq_pow_finrank (K := ZMod 2) (V := Additive ↥A)
    rw [hcard', ZMod.card] at h
    exact (Nat.pow_right_injective (by norm_num : 2 ≤ 2) h).symm
  let e : ↥A ≃* Multiplicative (Additive ↥A) :=
    { toFun := fun a => Multiplicative.ofAdd (Additive.ofMul a)
      invFun := fun x => Additive.toMul (Multiplicative.toAdd x)
      left_inv := fun a => rfl
      right_inv := fun x => rfl
      map_mul' := fun a b => rfl }
  let toLin : MulAut ↥A → (Additive ↥A ≃ₗ[ZMod 2] Additive ↥A) := fun f =>
    (MulEquiv.toAdditive f).toLinearEquiv (fun c x => ZMod.map_smul (MulEquiv.toAdditive f) c x)
  have toLin_mul : ∀ f g : MulAut ↥A, toLin (f * g) = toLin f * toLin g := by
    intro f g
    apply LinearEquiv.ext
    intro x
    rfl
  let act : ↥(normalizer (A : Set X)) →* (Additive ↥A ≃ₗ[ZMod 2] Additive ↥A) :=
    MonoidHom.mk' (fun n => toLin ((Subgroup.normalizerMonoidHom A) n)) (by
      intro n m
      rw [map_mul, toLin_mul])
  refine ⟨Additive ↥A, inferInstance, inferInstance, inferInstance, e, act, hfr, ?_⟩
  intro n a
  rfl

end CFSG.EvenSporadicStandard.HNRecog.Harada

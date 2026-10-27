module

public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoFi22.DS81.S44Spec
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.Algebra.Module.ZMod
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Card

public section

namespace CFSG.EvenSporadicStandard.TwoFi22.DS81.S44

open Module

section Embedding

variable {V : Type} [CommGroup V] [Module (ZMod 2) (Additive V)]

private def linAut (φ : MulAut V) : Additive V ≃ₗ[ZMod 2] Additive V where
  __ := MulEquiv.toAdditive φ
  map_smul' c x := ZMod.map_smul (MulEquiv.toAdditive φ) c x

private def linAutHom : MulAut V →* (Additive V ≃ₗ[ZMod 2] Additive V) where
  toFun := linAut
  map_one' := rfl
  map_mul' _ _ := rfl

private theorem linAutHom_injective : Function.Injective (linAutHom (V := V)) := fun _ _ h =>
  MulEquiv.ext fun x => Additive.ofMul.injective (LinearEquiv.congr_fun h (Additive.ofMul x))

end Embedding

theorem exists_injective_mulAut_gl {V : Type} [CommGroup V] [Finite V] (hV : Nat.card V = 2 ^ 11)
    (h2 : ∀ v : V, v ^ 2 = 1) :
    ∃ e : MulAut V →* Matrix.GeneralLinearGroup (Fin 11) (ZMod 2), Function.Injective e := by
  have h2' : ∀ x : Additive V, 2 • x = 0 := fun x => by
    apply Additive.toMul.injective
    simpa using h2 (Additive.toMul x)
  let _ : Module (ZMod 2) (Additive V) := AddCommGroup.zmodModule h2'
  have : Module.Finite (ZMod 2) (Additive V) := Module.Finite.of_finite
  have hrank : finrank (ZMod 2) (Additive V) = 11 := by
    have h := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := Additive V)
    rw [Nat.card_zmod, show Nat.card (Additive V) = 2 ^ 11 from hV] at h
    exact (Nat.pow_right_injective le_rfl h).symm
  let b : Module.Basis (Fin 11) (ZMod 2) (Additive V) :=
    Module.finBasisOfFinrankEq (ZMod 2) (Additive V) hrank
  let g := LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod 2) (Additive V)
  exact ⟨(Matrix.GeneralLinearGroup.toLin' b).symm.toMonoidHom.comp
      (g.symm.toMonoidHom.comp linAutHom),
    (Matrix.GeneralLinearGroup.toLin' b).symm.injective.comp
      (g.symm.injective.comp linAutHom_injective)⟩

private theorem prod_gl_eleven :
    ∏ i : Fin 11, (2 ^ 11 - 2 ^ (i : ℕ)) =
      2 ^ 55 * 3 ^ 6 * 5 ^ 2 * 7 ^ 3 * 11 * 17 * 23 * 31 ^ 2 * 73 * 89 * 127 := by
  simp only [Fin.prod_univ_succ, Fin.prod_univ_zero]
  norm_num

theorem glDvd : GLDvdStmt := by
  intro V _ _ hV h2 X
  obtain ⟨e, he⟩ := exists_injective_mulAut_gl hV h2
  have h1 := Subgroup.card_dvd_of_injective e he
  rw [Matrix.card_GL_field, ZMod.card, prod_gl_eleven] at h1
  exact (Subgroup.card_subgroup_dvd_card X).trans h1

end CFSG.EvenSporadicStandard.TwoFi22.DS81.S44

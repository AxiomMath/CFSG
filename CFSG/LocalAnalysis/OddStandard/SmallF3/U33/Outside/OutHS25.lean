module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Outside.OutDefs
public import Mathlib.Algebra.Module.ZMod
public import Mathlib.LinearAlgebra.Determinant

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33.Outside

noncomputable section

private def toAddHom {B : Type} [Group B] (e : B ≃* Z4pow 3) (φ : MulAut B) :
    (Fin 3 → ZMod 4) →+ (Fin 3 → ZMod 4) where
  toFun v := (e (φ (e.symm (Multiplicative.ofAdd v)))).toAdd
  map_zero' := by simp
  map_add' v w := by
    simp only [ofAdd_add, map_mul, toAdd_mul]

private theorem toAddHom_mul {B : Type} [Group B] (e : B ≃* Z4pow 3) (φ ψ : MulAut B) :
    toAddHom e (φ * ψ) = (toAddHom e φ).comp (toAddHom e ψ) := by
  ext v
  simp [toAddHom, MulAut.mul_apply]

private theorem toAddHom_apply_inv {B : Type} [Group B] (e : B ≃* Z4pow 3) (t : MulAut B)
    (ht : ∀ b : B, t b = b⁻¹) (v : Fin 3 → ZMod 4) : toAddHom e t v = -v := by
  simp [toAddHom, ht]

theorem HS25 {B : Type} [Group B] (e : B ≃* Z4pow 3) (t τ : MulAut B)
    (ht : ∀ b : B, t b = b⁻¹) : τ * τ ≠ t := by
  haveI : Fact (1 < 4) := ⟨by norm_num⟩
  intro h
  let f : (Fin 3 → ZMod 4) →+ (Fin 3 → ZMod 4) := toAddHom e τ
  have hff : f.comp f = toAddHom e t := by
    dsimp only [f]
    rw [← toAddHom_mul, h]
  let g : (Fin 3 → ZMod 4) →ₗ[ZMod 4] (Fin 3 → ZMod 4) := f.toZModLinearMap 4
  have h1 : g.comp g = (toAddHom e t).toZModLinearMap 4 := by
    rw [← hff]
    ext v
    rfl
  have h2 : (toAddHom e t).toZModLinearMap 4 =
      (-1 : ZMod 4) • (LinearMap.id : (Fin 3 → ZMod 4) →ₗ[ZMod 4] (Fin 3 → ZMod 4)) := by
    ext v
    simp [toAddHom_apply_inv e t ht]
  have hcomp : g.comp g =
      (-1 : ZMod 4) • (LinearMap.id : (Fin 3 → ZMod 4) →ₗ[ZMod 4] (Fin 3 → ZMod 4)) :=
    h1.trans h2
  have hd : LinearMap.det g * LinearMap.det g = 3 := by
    have hh := congrArg LinearMap.det hcomp
    rw [LinearMap.det_comp, LinearMap.det_smul, LinearMap.det_id, mul_one,
      Module.finrank_fin_fun] at hh
    have hnum : (-1 : ZMod 4) ^ 3 = 3 := by decide
    rwa [hnum] at hh
  have hsq : ∀ d : ZMod 4, d * d ≠ 3 := by decide
  exact hsq (LinearMap.det g) hd

end

end CFSG.OddStandard.SmallF3.HarrisU33.Outside

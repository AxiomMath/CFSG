module

public import CFSG.LieType.AlgebraicGroups.GLFrobeniusLang
public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Diagonal.Basic

public noncomputable section

namespace CFSG.LieType.AlgebraicGroups

open Matrix TauCeti

theorem sl2_frobenius_lang {k : Type} [Field k] [IsAlgClosed k]
    (p f : ℕ) [Fact p.Prime] [CharP k p] (hf : 1 ≤ f)
    (X : Matrix.SpecialLinearGroup (Fin 2) k) :
    ∃ Y : Matrix.SpecialLinearGroup (Fin 2) k,
      X = Y⁻¹ * Matrix.SpecialLinearGroup.map (iterateFrobenius k p f) Y := by
  let Fr := iterateFrobenius k p f
  let F : GL (Fin 2) k →* GL (Fin 2) k := Matrix.GeneralLinearGroup.map Fr
  obtain ⟨h, hh⟩ := gl_frobenius_lang p f hf (X : GL (Fin 2) k)
  have hh' : F h = h * (X : GL (Fin 2) k) := by
    change Units.map (Fr.mapMatrix.toMonoidHom) h = h * (X : GL (Fin 2) k)
    rw [hh]
    group
    rfl
  have hxdet : Matrix.GeneralLinearGroup.det (X : GL (Fin 2) k) = 1 := by
    apply Units.ext
    exact X.property
  have hdetfix : Units.map (Fr : k →* k) (Matrix.GeneralLinearGroup.det h) =
      Matrix.GeneralLinearGroup.det h := by
    rw [← Matrix.GeneralLinearGroup.map_det]
    change Matrix.GeneralLinearGroup.det (F h) = Matrix.GeneralLinearGroup.det h
    rw [hh', map_mul, hxdet, mul_one]
  let t : Fin 2 → kˣ := fun i => if i = 0 then (Matrix.GeneralLinearGroup.det h)⁻¹ else 1
  let D : GL (Fin 2) k := TauCeti.diagGL t
  have hDfix : F D = D := by
    change Matrix.GeneralLinearGroup.map Fr (TauCeti.diagGL t) = TauCeti.diagGL t
    rw [TauCeti.map_diagGL]
    congr 1
    funext i
    dsimp only [t]
    split_ifs <;> simp only [map_inv, hdetfix, map_one]
  have hDdet : Matrix.GeneralLinearGroup.det D = (Matrix.GeneralLinearGroup.det h)⁻¹ := by
    change Matrix.GeneralLinearGroup.det (TauCeti.diagGL t) = _
    rw [TauCeti.det_diagGL]
    simp [t, Fin.prod_univ_two]
  let YGL := D * h
  have hYdet : Matrix.GeneralLinearGroup.det YGL = 1 := by
    change Matrix.GeneralLinearGroup.det (D * h) = 1
    rw [map_mul, hDdet, inv_mul_cancel]
  let Y : Matrix.SpecialLinearGroup (Fin 2) k :=
    ⟨(YGL : Matrix (Fin 2) (Fin 2) k), by
      simpa only [Matrix.GeneralLinearGroup.val_det_apply, Units.val_one] using
        congrArg Units.val hYdet⟩
  have hY : (Y : GL (Fin 2) k) = YGL := by
    apply Units.ext
    rfl
  have hmap : (Matrix.SpecialLinearGroup.map Fr Y : GL (Fin 2) k) = F (Y : GL (Fin 2) k) := by
    apply Units.ext
    rfl
  have hLang : (X : GL (Fin 2) k) = YGL⁻¹ * F YGL := by
    change (X : GL (Fin 2) k) = (D * h)⁻¹ * F (D * h)
    rw [map_mul, hDfix]
    calc
      (X : GL (Fin 2) k) = h⁻¹ * F h := hh
      _ = (D * h)⁻¹ * (D * F h) := by group
  refine ⟨Y, ?_⟩
  apply (Matrix.SpecialLinearGroup.toGL_inj _ _).mp
  rw [map_mul, map_inv]
  change (X : GL (Fin 2) k) = (Y : GL (Fin 2) k)⁻¹ *
    (Matrix.SpecialLinearGroup.map Fr Y : GL (Fin 2) k)
  rw [hmap, hY]
  exact hLang

end CFSG.LieType.AlgebraicGroups

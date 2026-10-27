module

public import CFSG.Fischer.F4
public import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.YamadaParD

public section

namespace CFSG.EvenSmallLie.UnitarySix.YamadaPar

open Matrix CFSG.Fischer

@[expose] def mF4 (α : F4) : Matrix (Fin 2) (Fin 2) (ZMod 2) :=
  !![((α.code : ℕ) % 2 : ℕ), ((α.code : ℕ) / 2 : ℕ);
    ((α.code : ℕ) / 2 : ℕ), ((α.code : ℕ) % 2 + (α.code : ℕ) / 2 : ℕ)]

theorem mF4_one : mF4 1 = 1 := by decide

theorem mF4_zero : mF4 0 = 0 := by decide

theorem mF4_add : ∀ x y : F4, mF4 (x + y) = mF4 x + mF4 y := by decide

theorem mF4_mul : ∀ x y : F4, mF4 (x * y) = mF4 x * mF4 y := by decide

@[expose] def codeOfM (M : Matrix (Fin 2) (Fin 2) (ZMod 2)) : ℕ := (M 0 0).val + 2 * (M 0 1).val

theorem codeOfM_mF4 : ∀ c : Fin 4, codeOfM (mF4 ⟨c⟩) = c := by decide

theorem mF4_injective : Function.Injective mF4 := by
  rintro ⟨cx⟩ ⟨cy⟩ h
  have := congrArg codeOfM h
  rw [codeOfM_mF4, codeOfM_mF4] at this
  rw [Fin.ext this]

@[expose] def mF4Hom : F4 →+* Matrix (Fin 2) (Fin 2) (ZMod 2) where
  toFun := mF4
  map_one' := mF4_one
  map_mul' := mF4_mul
  map_zero' := mF4_zero
  map_add' := mF4_add

@[expose] noncomputable def reF4 : Matrix (Fin 4) (Fin 4) F4 →+* Mat8 :=
  ((Matrix.reindexRingEquiv (ZMod 2) (finProdFinEquiv (m := 4) (n := 2))).toRingHom.comp
    (Matrix.compRingEquiv (Fin 4) (Fin 2) (ZMod 2)).toRingHom).comp mF4Hom.mapMatrix

theorem reF4_apply (M : Matrix (Fin 4) (Fin 4) F4) (i j : Fin 4) (b c : Fin 2) :
    reF4 M (finProdFinEquiv (i, b)) (finProdFinEquiv (j, c)) = mF4 (M i j) b c := by
  simp [reF4, Matrix.reindexRingEquiv, Matrix.compRingEquiv, mF4Hom]

theorem reF4_injective : Function.Injective reF4 := by
  intro M N h
  ext i j
  apply mF4_injective
  ext b c
  have := congrFun (congrFun h (finProdFinEquiv (i, b))) (finProdFinEquiv (j, c))
  rwa [reF4_apply, reF4_apply] at this

@[expose] def f4m (c : List (List ℕ)) : Matrix (Fin 4) (Fin 4) F4 :=
  Matrix.of fun i j => ⟨Fin.ofNat 4 ((c.getD i []).getD j 0)⟩

end CFSG.EvenSmallLie.UnitarySix.YamadaPar

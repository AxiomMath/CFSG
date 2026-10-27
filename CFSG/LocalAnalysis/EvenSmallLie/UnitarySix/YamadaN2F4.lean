module

public import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.YamadaParSL4

public section

namespace CFSG.EvenSmallLie.UnitarySix.YamadaN2

open Matrix CFSG.Fischer CFSG.EvenSmallLie.UnitarySix.YamadaPar

abbrev SL3 : Type := Matrix.SpecialLinearGroup (Fin 3) F4

abbrev M3 : Type := Matrix (Fin 3) (Fin 3) F4

abbrev Mat9 : Type := Matrix (Fin 9) (Fin 9) (ZMod 2)

abbrev Mat18 : Type := Matrix (Fin 18) (Fin 18) (ZMod 2)

theorem coe_SL3_mul (g h : SL3) : ((g * h : SL3) : M3) = (g : M3) * (h : M3) := rfl

theorem coe_SL3_one : ((1 : SL3) : M3) = 1 := rfl

theorem f3mat_ext {A B : M3} (h : ∀ i j, (A i j).code = (B i j).code) : A = B :=
  Matrix.ext fun i j => f4_ext (h i j)

@[expose] def kr (A B : M3) : Matrix (Fin 9) (Fin 9) F4 :=
  Matrix.reindex finProdFinEquiv finProdFinEquiv (Matrix.kroneckerMap (· * ·) A B)

theorem kr_mul (A B C D : M3) : kr (A * C) (B * D) = kr A B * kr C D := by
  simp only [kr, Matrix.reindex_apply]
  rw [Matrix.submatrix_mul_equiv, ← Matrix.mul_kronecker_mul]

theorem kr_one : kr 1 1 = 1 := by
  rw [kr, Matrix.one_kronecker_one, Matrix.reindex_apply, Matrix.submatrix_one_equiv]

theorem kr_apply (A B : M3) (i j k l : Fin 3) :
    kr A B (finProdFinEquiv (i, j)) (finProdFinEquiv (k, l)) = A i k * B j l := by
  simp [kr, Matrix.kroneckerMap_apply]

@[expose] noncomputable def reFN (n : ℕ) :
    Matrix (Fin n) (Fin n) F4 →+* Matrix (Fin (n * 2)) (Fin (n * 2)) (ZMod 2) :=
  ((Matrix.reindexRingEquiv (ZMod 2) (finProdFinEquiv (m := n) (n := 2))).toRingHom.comp
    (Matrix.compRingEquiv (Fin n) (Fin 2) (ZMod 2)).toRingHom).comp mF4Hom.mapMatrix

theorem reFN_apply (n : ℕ) (M : Matrix (Fin n) (Fin n) F4) (i j : Fin n) (b c : Fin 2) :
    reFN n M (finProdFinEquiv (i, b)) (finProdFinEquiv (j, c)) = mF4 (M i j) b c := by
  simp [reFN, Matrix.reindexRingEquiv, Matrix.compRingEquiv, mF4Hom]

@[expose] noncomputable def reF9 : Matrix (Fin 9) (Fin 9) F4 →+* Mat18 := reFN 9

theorem reF9_apply (M : Matrix (Fin 9) (Fin 9) F4) (i j : Fin 9) (b c : Fin 2) :
    reF9 M (finProdFinEquiv (i, b)) (finProdFinEquiv (j, c)) = mF4 (M i j) b c :=
  reFN_apply 9 M i j b c

theorem reF9_injective : Function.Injective reF9 := by
  intro M N h
  ext i j
  apply mF4_injective
  ext b c
  have := congrFun (congrFun h (finProdFinEquiv (i, b))) (finProdFinEquiv (j, c))
  rwa [reF9_apply, reF9_apply] at this

@[expose] noncomputable def frob3 : M3 →+* M3 := frobF4.mapMatrix

theorem frob3_apply (A : M3) (i j : Fin 3) : frob3 A i j = frobF4 (A i j) := rfl

@[expose] noncomputable def star3 (A : M3) : M3 := (frob3 A)ᵀ

theorem star3_mul (A B : M3) : star3 (A * B) = star3 B * star3 A := by
  rw [star3, star3, star3, map_mul, transpose_mul]

theorem star3_one : star3 1 = 1 := by rw [star3, map_one, transpose_one]

theorem det_star3 (A : M3) : (star3 A).det = frobF4 A.det := by
  rw [star3, det_transpose, frob3, RingHom.map_det]

theorem star3_star3 (A : M3) : star3 (star3 A) = A := by
  ext i j
  simp only [star3, frob3, transpose_apply, RingHom.mapMatrix_apply, Matrix.map_apply]
  exact frobF4_frobF4 _

@[expose] noncomputable def sigma3 : SL3 →* SL3 where
  toFun g := ⟨star3 ((g⁻¹ : SL3) : M3), by
    rw [det_star3, (g⁻¹ : SL3).2, map_one]⟩
  map_one' := Subtype.ext (by simp only [inv_one, coe_SL3_one, star3_one])
  map_mul' g h := Subtype.ext (by
    change star3 (((g * h)⁻¹ : SL3) : M3) = star3 ((g⁻¹ : SL3) : M3) * star3 ((h⁻¹ : SL3) : M3)
    rw [_root_.mul_inv_rev, coe_SL3_mul, star3_mul])

theorem coe_sigma3 (g : SL3) : ((sigma3 g : SL3) : M3) = star3 ((g⁻¹ : SL3) : M3) := rfl

theorem coe_sigma3_inv (g : SL3) : (((sigma3 g)⁻¹ : SL3) : M3) = star3 (g : M3) := by
  rw [← map_inv, coe_sigma3, inv_inv]

end CFSG.EvenSmallLie.UnitarySix.YamadaN2

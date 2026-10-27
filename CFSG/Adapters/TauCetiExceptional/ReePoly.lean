module

public import CFSG.Adapters.TauCetiExceptional.BigCellNative
public import CFSG.Adapters.TauCetiExceptional.BigCellCore
public import CFSG.Adapters.TauCetiExceptional.ReeAdjoint

public noncomputable section

namespace CFSG.TauCetiBridge.Ree

open CFSG.Blueprint.Chevalley CFSG.Quasithin.G2U CFSG.TauCetiBridge.BigCell MvPolynomial

abbrev PolyRing : Type :=
  MvPolynomial (Fin 7 × Fin 7) ℤ

abbrev genMat : Matrix (Fin 7) (Fin 7) PolyRing :=
  coordMatrix 7

variable {A : Type*} [CommRing A]

theorem mapMatrix_basisMatR {B : Type*} [CommRing B] (f : A →+* B) (t : Fin 14) :
    f.mapMatrix (basisMatR A t) = basisMatR B t := by
  ext r c
  simp [basisMatR]

theorem mapMatrix_labMat {B : Type*} [CommRing B] (f : A →+* B) (b : Label .G2) :
    f.mapMatrix (labMat A b) = labMat B b :=
  mapMatrix_basisMatR f _

theorem mapMatrix_conj_adjugate (M : Matrix (Fin 7) (Fin 7) A) (Y : Matrix (Fin 7) (Fin 7) ℤ) :
    (evalMat M).mapMatrix (genMat * Y.map (Int.cast : ℤ → PolyRing) * genMat.adjugate) =
      M * Y.map (Int.cast : ℤ → A) * M.adjugate := by
  rw [map_mul, map_mul, RingHom.map_adjugate, mapMatrix_evalMat_coordMatrix]
  congr 2
  ext r c
  simp

@[expose] def detPoly : PolyRing :=
  genMat.det - 1

theorem evalMat_detPoly (M : Matrix (Fin 7) (Fin 7) A) : evalMat M detPoly = M.det - 1 := by
  rw [detPoly, map_sub, map_one, RingHom.map_det, mapMatrix_evalMat_coordMatrix]

@[expose] def normPoly (t : Fin 14) (r c : Fin 7) : PolyRing :=
  (genMat * basisMatR PolyRing t * genMat.adjugate -
    ∑ u, coord u (genMat * basisMatR PolyRing t * genMat.adjugate) • basisMatR PolyRing u) r c

theorem evalMat_normPoly (M : Matrix (Fin 7) (Fin 7) A) (t : Fin 14) (r c : Fin 7) :
    evalMat M (normPoly t r c) = (M * basisMatR A t * M.adjugate -
      ∑ u, coord u (M * basisMatR A t * M.adjugate) • basisMatR A u) r c := by
  have key : evalMat M (normPoly t r c) = ((evalMat M).mapMatrix
      (genMat * basisMatR PolyRing t * genMat.adjugate -
        ∑ u, coord u (genMat * basisMatR PolyRing t * genMat.adjugate) •
          basisMatR PolyRing u)) r c := rfl
  have hsum : ∀ u, (evalMat M).mapMatrix
      (coord u (genMat * basisMatR PolyRing t * genMat.adjugate) • basisMatR PolyRing u) =
        coord u (M * basisMatR A t * M.adjugate) • basisMatR A u := fun u => by
    rw [RingHom.mapMatrix_apply, Matrix.map_smul' _ _ _ (map_mul _),
      ← RingHom.mapMatrix_apply, mapMatrix_basisMatR, map_coord, ← RingHom.mapMatrix_apply,
      mapMatrix_conj_adjugate]
  rw [key, map_sub, mapMatrix_conj_adjugate, map_sum]
  simp only [hsum]

@[expose] def adPoly
    (P : MvPolynomial (Fin (nLab .G2) × Fin (nLab .G2)) ℤ) : PolyRing :=
  evalMat (natMat .G2 PolyRing (adOp genMat genMat.adjugate)) P

theorem mapMatrix_natMat_adOp (M : Matrix (Fin 7) (Fin 7) A) :
    (evalMat M).mapMatrix (natMat .G2 PolyRing (adOp genMat genMat.adjugate)) =
      natMat .G2 A (adOp M M.adjugate) := by
  ext i j
  rw [RingHom.mapMatrix_apply, Matrix.map_apply, natMat_apply, natMat_apply, adOp_single_apply,
    adOp_single_apply, map_coord, ← RingHom.mapMatrix_apply, labMat, labMat, basisMatR,
    basisMatR, mapMatrix_conj_adjugate]

theorem evalMat_adPoly (M : Matrix (Fin 7) (Fin 7) A)
    (P : MvPolynomial (Fin (nLab .G2) × Fin (nLab .G2)) ℤ) :
    evalMat M (adPoly P) = evalMat (natMat .G2 A (adOp M M.adjugate)) P := by
  rw [adPoly, ← RingHom.comp_apply, ← evalMat_mapMatrix, mapMatrix_natMat_adOp]

theorem adjugate_eq_inv_of_det_eq_one (g : Matrix.GeneralLinearGroup (Fin 7) A)
    (h : (g : Matrix (Fin 7) (Fin 7) A).det = 1) :
    (g : Matrix (Fin 7) (Fin 7) A).adjugate =
      ((g⁻¹ : Matrix.GeneralLinearGroup (Fin 7) A) : Matrix (Fin 7) (Fin 7) A) := by
  rw [Matrix.coe_units_inv]
  refine (Matrix.inv_eq_right_inv ?_).symm
  rw [Matrix.mul_adjugate, h, one_smul]

end CFSG.TauCetiBridge.Ree

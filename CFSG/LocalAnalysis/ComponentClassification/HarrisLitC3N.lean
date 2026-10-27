module

public import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4InvClassLb
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4DiagUa
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge

public noncomputable section

namespace CFSG.ComponentClassification.HarrisLit.C3

open CFSG Subgroup Matrix CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial
open CFSG.ClassicalGroups.UnitaryFlag
open CFSG.ComponentClassification.CatFactsL4U4 DiagU StabU UnitaryOut UnitaryConj HBlocks
open CFSG.ComponentClassification.CatFactsL4U4.InvClassL
open CFSG.ComponentClassification.CatFactsL4U4.TBlocks

variable {p f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData p f K)

theorem det_two (a : SpecialLinearGroup (Fin 2) K) :
    (a : Matrix (Fin 2) (Fin 2) K) 0 0 * (a : Matrix (Fin 2) (Fin 2) K) 1 1 -
      (a : Matrix (Fin 2) (Fin 2) K) 0 1 * (a : Matrix (Fin 2) (Fin 2) K) 1 0 = 1 := by
  have := a.2
  rwa [Matrix.det_fin_two] at this

@[expose] def starInvMat (a : Matrix (Fin 2) (Fin 2) K) : Matrix (Fin 2) (Fin 2) K :=
  !![h.bar (a 1 1), -h.bar (a 1 0); -h.bar (a 0 1), h.bar (a 0 0)]

theorem starInvMat_mul (a b : Matrix (Fin 2) (Fin 2) K) :
    starInvMat h (a * b) = starInvMat h a * starInvMat h b := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [starInvMat, Matrix.mul_apply, Fin.sum_univ_two] <;> ring

theorem det_starInvMat (a : Matrix (Fin 2) (Fin 2) K) : (starInvMat h a).det = h.bar a.det := by
  rw [starInvMat, Matrix.det_fin_two_of, Matrix.det_fin_two, map_sub, map_mul, map_mul]
  ring

@[expose] def invStar : SpecialLinearGroup (Fin 2) K →* SpecialLinearGroup (Fin 2) K where
  toFun a := ⟨starInvMat h a, by rw [det_starInvMat, a.2, map_one]⟩
  map_one' := Subtype.ext (by
    change starInvMat h 1 = 1
    ext i j
    fin_cases i <;> fin_cases j <;> simp [starInvMat])
  map_mul' a b := Subtype.ext (starInvMat_mul h a b)

theorem coe_invStar (a : SpecialLinearGroup (Fin 2) K) :
    ((invStar h a : SpecialLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) =
      starInvMat h (a : Matrix (Fin 2) (Fin 2) K) :=
  rfl

@[expose] def pairSL : SpecialLinearGroup (Fin 2) K →* SpecialLinearGroup (Fin 4) K :=
  bdSL.comp ((MonoidHom.id _).prod (invStar h))

theorem coe_pairSL (a : SpecialLinearGroup (Fin 2) K) :
    ((pairSL h a : SpecialLinearGroup (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) =
      bd (a : Matrix (Fin 2) (Fin 2) K) (invStar h a : Matrix (Fin 2) (Fin 2) K) := rfl

theorem uStar_pair (a : SpecialLinearGroup (Fin 2) K) :
    uStar h ((pairSL h a : SpecialLinearGroup (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) * stdG *
      ((pairSL h a : SpecialLinearGroup (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) = stdG := by
  have hd := det_two a
  have hdb : h.bar ((a : Matrix (Fin 2) (Fin 2) K) 0 0) * h.bar ((a : Matrix (Fin 2) (Fin 2) K) 1 1)
      - h.bar ((a : Matrix (Fin 2) (Fin 2) K) 0 1) * h.bar ((a : Matrix (Fin 2) (Fin 2) K) 1 0) =
      1 := by
    rw [← map_mul, ← map_mul, ← map_sub, hd, map_one]
  rw [coe_pairSL, coe_invStar]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [bd, stdG, uStar, starInvMat, Matrix.mul_apply, Fin.sum_univ_four,
      Matrix.transpose_apply, h.bar_bar] <;>
    first | ring1 | linear_combination hd | linear_combination hdb

theorem swap_mul_pair (a : SpecialLinearGroup (Fin 2) K) :
    blk (0 : K) 1 1 0 * ((pairSL h a : SpecialLinearGroup (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) =
      ((pairSL h (SpecialLinearGroup.map h.bar a) : SpecialLinearGroup (Fin 4) K) :
        Matrix (Fin 4) (Fin 4) K) * blk 0 1 1 0 := by
  rw [coe_pairSL, coe_pairSL, coe_invStar, coe_invStar, Matrix.SpecialLinearGroup.map_apply_coe]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [bd, blk, starInvMat, Matrix.mul_apply, Fin.sum_univ_four, h.bar_bar]

theorem pair_comm_X1 (a : SpecialLinearGroup (Fin 2) K) (l : K) :
    ((pairSL h a : SpecialLinearGroup (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) * X1 l =
      X1 l * ((pairSL h a : SpecialLinearGroup (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) := by
  rw [coe_pairSL]
  exact bd_comm_X1 _ _ l

end CFSG.ComponentClassification.HarrisLit.C3

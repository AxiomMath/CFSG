module

public import CFSG.LocalAnalysis.ComponentClassification.FixedCommutingProduct
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBHigherLinearFieldAction
public import CFSG.LocalAnalysis.ComponentInitial.LinearFieldFourRoots
public import CFSG.LocalAnalysis.ComponentInitial.LinearFlagOrder

public section

namespace CFSG.LocalAnalysis.ComponentInitial

namespace LinearFlag

open Matrix Subgroup CFSG.ComponentClassification
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)

variable {k : Type*} [Field k]

theorem wMat_one_mul_comm {u : SpecialLinearGroup (Fin 3) k} (hu : u ∈ unitriangular 3 k) :
    LinearFieldFour.wMat 1 * u = u * LinearFieldFour.wMat 1 := by
  obtain ⟨hlow, hdiag⟩ := hu
  have h10 := hlow 1 0 (by decide)
  have h20 := hlow 2 0 (by decide)
  have h21 := hlow 2 1 (by decide)
  have h00 := hdiag 0
  have h11 := hdiag 1
  have h22 := hdiag 2
  apply Subtype.ext
  change LinearFieldFour.wM 1 * (u : Matrix (Fin 3) (Fin 3) k) =
    (u : Matrix (Fin 3) (Fin 3) k) * LinearFieldFour.wM 1
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_three, LinearFieldFour.wM, h10, h20, h21, h00, h11, h22,
      add_comm]

theorem card_projUnitriangular_three [Finite k] (hk : Nat.card k = 4) :
    Nat.card (projUnitriangular 3 k) = 2 ^ 6 := by
  rw [card_projUnitriangular, hk]
  norm_num

end LinearFlag

end CFSG.LocalAnalysis.ComponentInitial

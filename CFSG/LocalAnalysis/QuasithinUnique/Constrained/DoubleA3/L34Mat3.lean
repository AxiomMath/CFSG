module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.BinaryThreeSpaceRegularSylow

public section

namespace CFSG.QuasithinUnique.DoubleA3

open Matrix CFSG.ProperTwoGeneratedCore.BinaryThreeSpace

theorem mat3_symm_eq_mul_transpose :
    ∀ s : Mat3, sᵀ = s → s.det = 1 → ∃ h : Mat3, h.det = 1 ∧ h * hᵀ = s := by
  decide +kernel

theorem card_mat3_orthogonal : (Finset.univ.filter (fun A : Mat3 => A * Aᵀ = 1)).card = 6 := by
  decide +kernel

@[expose] def antiDiag : Mat3 := !![0, 0, 1; 0, 1, 0; 1, 0, 0]

theorem antiDiag_mul_self : antiDiag * antiDiag = 1 := by decide

theorem antiDiag_transpose : antiDiagᵀ = antiDiag := by decide

theorem antiDiag_unitri : ∀ a b c : ZMod 2,
    antiDiag * (unitri a (a * c + b) c)ᵀ * antiDiag = unitri c (a * c + b) a := by
  decide

end CFSG.QuasithinUnique.DoubleA3

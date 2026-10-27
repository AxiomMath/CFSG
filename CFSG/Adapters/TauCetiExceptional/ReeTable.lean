module

public import CFSG.Adapters.TauCetiExceptional.ReeCoeff
public import CFSG.Adapters.TauCetiExceptional.ReeBasis

public section

namespace CFSG.TauCetiBridge.Ree

open CFSG.Blueprint.Chevalley CFSG.Quasithin.G2U

@[expose] def conjCoeff (E E2 X : Matrix (Fin 7) (Fin 7) ℤ) : ℕ → Matrix (Fin 7) (Fin 7) ℤ
  | 0 => X
  | 1 => E * X - X * E
  | 2 => E2 * X - E * X * E + X * E2
  | 3 => E * X * E2 - E2 * X * E
  | _ => E2 * X * E2

theorem conjCoeff_inl_zero : ∀ s : Fin 14, ∀ j : Fin 5,
    conjCoeff (tcE (.inl 0)) (tcE2 (.inl 0)) (basisMat s) j =
      ∑ u : Fin 14, colXc j (nodeMap 0) (lab s) (lab u) • basisMat u := by
  decide +kernel

theorem conjCoeff_inl_one : ∀ s : Fin 14, ∀ j : Fin 5,
    conjCoeff (tcE (.inl 1)) (tcE2 (.inl 1)) (basisMat s) j =
      ∑ u : Fin 14, colXc j (nodeMap 1) (lab s) (lab u) • basisMat u := by
  decide +kernel

theorem conjCoeff_inr_zero : ∀ s : Fin 14, ∀ j : Fin 5,
    conjCoeff (tcE (.inr 0)) (tcE2 (.inr 0)) (basisMat s) j =
      ∑ u : Fin 14, colYc j (nodeMap 0) (lab s) (lab u) • basisMat u := by
  decide +kernel

theorem conjCoeff_inr_one : ∀ s : Fin 14, ∀ j : Fin 5,
    conjCoeff (tcE (.inr 1)) (tcE2 (.inr 1)) (basisMat s) j =
      ∑ u : Fin 14, colYc j (nodeMap 1) (lab s) (lab u) • basisMat u := by
  decide +kernel

theorem conjCoeff_inl (i : Fin 2) (s : Fin 14) (j : Fin 5) :
    conjCoeff (tcE (.inl i)) (tcE2 (.inl i)) (basisMat s) j =
      ∑ u : Fin 14, colXc j (nodeMap i) (lab s) (lab u) • basisMat u := by
  fin_cases i
  · exact conjCoeff_inl_zero s j
  · exact conjCoeff_inl_one s j

theorem conjCoeff_inr (i : Fin 2) (s : Fin 14) (j : Fin 5) :
    conjCoeff (tcE (.inr i)) (tcE2 (.inr i)) (basisMat s) j =
      ∑ u : Fin 14, colYc j (nodeMap i) (lab s) (lab u) • basisMat u := by
  fin_cases i
  · exact conjCoeff_inr_zero s j
  · exact conjCoeff_inr_one s j

end CFSG.TauCetiBridge.Ree

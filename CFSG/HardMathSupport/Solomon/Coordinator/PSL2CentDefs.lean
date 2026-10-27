module

public import Mathlib.LinearAlgebra.Matrix.ProjectiveSpecialLinearGroup
public import Mathlib.GroupTheory.Solvable

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator

@[expose] def PSL2CentSolvable : Prop :=
  ∀ (F : Type) [Field F] [Finite F] (x : Matrix.ProjectiveSpecialLinearGroup (Fin 2) F), x ≠ 1 →
    IsSolvable ↥(Subgroup.centralizer ({x} : Set (Matrix.ProjectiveSpecialLinearGroup (Fin 2) F)))

end CFSG.HardMathSupport.Solomon.Coordinator

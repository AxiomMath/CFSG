module

public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.KS.E8FiveOneVand
public import CFSG.HardMathSupport.Timmesfeld.Torality.CycMonomial

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.ChevQ

namespace KSE8Five

namespace One

open CFSG.HardMathSupport.Timmesfeld.Torality

theorem diagonal_mul_cycEigen5 {K : Type} [Field K] {ω : K} (hω : ω ^ 5 = 1) (a : Fin 5 → K)
    (s : Fin 5) :
    Matrix.diagonal (fun i : Fin 5 => ω ^ ((s : ℕ) * (i : ℕ))) * cycEigen5 ω a =
      cycEigen5 ω a * Matrix.of (fun l k : Fin 5 => if l = k + s then (1 : K) else 0) := by
  unfold cycEigen5
  rw [← Matrix.mul_assoc, (Matrix.commute_diagonal _ _).eq, Matrix.mul_assoc,
    diagonal_mul_vandermonde_five hω s, ← Matrix.mul_assoc]

end One

end KSE8Five

end CFSG.HardMathSupport.Solomon.Coordinator.ChevQ

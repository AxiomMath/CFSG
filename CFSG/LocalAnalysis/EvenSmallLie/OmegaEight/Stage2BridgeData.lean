module

public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.Stage2Bridge
public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.Stage1Data
public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.Stage2Native

public section

namespace CFSG.EvenSmallLie.OmegaEight.Stage2

open CFSG.EvenSmallLie.OmegaEight.Stage1

@[expose] def urRows : Eps → ℕ → Array ℕ
  | .plus, 0 => #[3, 2, 4, 8, 48, 32]
  | .plus, 1 => #[5, 2, 4, 40, 16, 32]
  | .plus, 2 => #[1, 6, 4, 24, 16, 32]
  | .plus, 3 => #[17, 34, 4, 8, 16, 32]
  | .plus, 4 => #[9, 2, 36, 8, 16, 32]
  | .plus, 5 => #[1, 10, 20, 8, 16, 32]
  | .minus, 0 => #[17, 34, 4, 8, 16, 32]
  | .minus, 1 => #[41, 2, 36, 8, 16, 32]
  | .minus, 2 => #[1, 26, 20, 8, 16, 32]
  | .minus, 3 => #[37, 2, 4, 40, 16, 32]
  | .minus, 4 => #[1, 22, 4, 24, 16, 32]
  | .minus, 5 => #[3, 2, 4, 8, 48, 32]
  | _, _ => id6

@[expose] def stage1Gens (ε : Eps) : Array (ℕ × ℕ) :=
  #[(phiK, phiK)] ++ ((List.range 6).map fun i =>
    (kronK (genRows ε i), kronK (genInvRows ε i))).toArray

@[expose] def bridgeCheck (ε : Eps) (cGens tGens : Array (ℕ × ℕ)) (cE tcE sE : Enum) : Bool :=
  ((List.range 6).all fun i => memK cE.keys (kronK (genRows ε i))) &&
    enumOK (stage1Gens ε) sE && gensIn cGens sE &&
    tGens.size == 7 && (tGens.getD 0 (0, 0)).1 == phiK &&
    ((List.range 6).all fun k =>
      (tGens.getD (k + 1) (0, 0)).1 == kronK (urRows ε k) && memK tcE.keys (kronK (urRows ε k)))

end CFSG.EvenSmallLie.OmegaEight.Stage2

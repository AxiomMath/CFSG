module

public import CFSG.CGT.Stroth77.Types

public section

namespace CFSG.CGT.Stroth77

namespace Stroth34T201Levels

open Matrix

@[expose] def omegaMat (k : Fin 3 → ℕ) : IntMat := Matrix.diagonal fun j => 2 ^ (k j - 1)

@[expose] def IsAut1 (k : Fin 3 → ℕ) (M : IntMat) : Prop :=
  MatEq k (M * omegaMat k) (omegaMat k)

@[expose] def conjρ (M : IntMat) : IntMat := Type200.ρM * M * (Type200.ρM * Type200.ρM)

@[expose] def conjU (M : IntMat) : IntMat := Type200.uM * M * Type200.uM

@[expose] def NatCond (k : Fin 3 → ℕ) (M : IntMat) : Prop :=
  MatEq k (conjρ (conjρ M) * conjρ M * M) 1 ∧
    (MatEq k (conjU M) M ∨ MatEq k (conjU M) (conjρ M) ∨ MatEq k (conjU M) (conjρ M * M))

@[expose] def wMat (p : ℕ) : Fin 3 → IntMat :=
  ![ofCols ![1, 0, 0] ![0, 1, 2 ^ (p + 1)] ![0, 2 ^ (p + 1), 1],
    ofCols ![1, 0, 0] ![0, 1 + 2 ^ (p + 1), 2 ^ (p + 1)] ![0, 0, 1 + 2 ^ (p + 1)],
    ofCols ![1, 0, 0] ![0, 1 + 2 ^ (p + 1), 0] ![0, 2 ^ (p + 1), 1 + 2 ^ (p + 1)]]

@[expose] def eMat (m : ℕ) : IntMat :=
  ofCols ![1, 0, 0] ![0, 1 + 2 ^ (m + 1), 0] ![0, 0, 1 + 2 ^ (m + 1)]

end Stroth34T201Levels

end CFSG.CGT.Stroth77

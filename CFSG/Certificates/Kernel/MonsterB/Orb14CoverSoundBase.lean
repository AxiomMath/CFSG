
module

public import CFSG.Monster.B.TwoA.Unitary.Orbit1408SchreierBase

@[expose] public section

namespace CFSG.KC.Orb14

open CFSG.Monster.B.TwoA.Unitary CFSG.Monster.B.TwoA.Census CFSG.KLie.CT CFSG.KC.U6Orb CFSG.KC.Bfs

def TreeBits : Prop :=
  tauPar 1 = 0 ∧ tauLab 1 = 0 ∧ tauPar 2 = 0 ∧ tauLab 2 = 1 ∧ tauPar 4 = 0 ∧ tauLab 4 = 5 ∧
    tauPar 8 = 0 ∧ tauLab 8 = 12 ∧ tauPar 13 = 1 ∧ tauLab 13 = 2

def SelEdges : Prop :=
  tauEdge 0 2 = 2 ∧ tauEdge 0 4 = 0 ∧ tauEdge 0 6 = 0 ∧ tauEdge 0 7 = 0 ∧ tauEdge 0 14 = 8 ∧
    tauEdge 0 16 = 0 ∧ tauEdge 13 3 = 4

def selL : Array (ℕ × ℕ) := #[(0, 2), (0, 4), (0, 6), (0, 7), (0, 14), (0, 16), (13, 3)]

end CFSG.KC.Orb14

end

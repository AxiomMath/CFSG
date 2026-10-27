module

public import CFSG.HardMathSupport.Dickson.Sec6.Up34Chev2Aux.InnExcRDCheck2
public import CFSG.HardMathSupport.Dickson.Sec6.Up34Chev2Aux.InnExcEmb

public section

namespace CFSG.LocalAnalysis.GLTheoremA.I167

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.HardMathSupport.Dickson.Sec6.Up34Exc

@[expose] def exc3core_orthRow (τ : Tag) (k : ℕ) : ℕ :=
  Nat.xor (2 ^ τ.artifactRoots.length - 1) (RD.rowM2 τ (2 ^ k))

@[expose] def exc3core_unionRows (τ : Tag) (V : ℕ) : ℕ :=
  (List.range τ.artifactRoots.length).foldl
    (fun acc δ => if V.testBit δ then Nat.lor acc (RD.rowM2 τ (2 ^ δ)) else acc) 0

@[expose] def exc3core_orthSet (τ : Tag) (V : ℕ) : ℕ :=
  Nat.xor (2 ^ τ.artifactRoots.length - 1) (exc3core_unionRows τ V)

@[expose] def exc3core_k2Obs (τ : Tag) (V : ℕ) : Bool :=
  (List.range τ.artifactRoots.length).any (fun k => V == exc3core_orthRow τ k) &&
    (RD.cnt2 3 (exc3core_orthSet τ V) == 2)

@[expose] def exc3core_k2C (τ : Tag) (cap : ℕ) (u : ℕ → Bool) (V : ℕ) : Bool :=
  !(u (RD.cnt2 cap V)) || exc3core_k2Obs τ V

@[expose] def exc3core_k2Check (τ : Tag) (cap : ℕ) (u : ℕ → Bool) (d : List ℕ) : Bool :=
  RD.compLoop2 (RD.rowM2 τ) (RD.kerMaskFast τ d) (τ.artifactRoots.length + 1)
    (exc3core_k2C τ cap u) τ.artifactRoots.length (RD.kerMaskFast τ d)

@[expose] def exc3core_uD6 (s : ℕ) : Bool := s == 60

end CFSG.LocalAnalysis.GLTheoremA.I167

end

module

public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoCo1.ECoreInputs

public section

namespace CFSG.EvenSporadicStandard.TwoCo1

open CFSG.Sporadic.SmallF2.Native CFSG.Sporadic.Th.Native CFSG.Sporadic.Co1.Cover

@[expose] def colsAa : Array ℕ := transposeRows 11 Aa

@[expose] def colsBa : Array ℕ := transposeRows 11 Ba

@[expose] def orbitOf11 (v n : ℕ) : VOrbit := vOrbitBFS 11 colsAa colsBa v n

@[expose] def orbitCheck11 (v n : ℕ) (others : List ℕ) : Bool :=
  let O := orbitOf11 v n
  let ls : Array Table := #[O.alpha, O.beta]
  let T := CFSG.Perm.Native.treeBFS n 0 ls #[0, 1]
  vOrbitOK 11 n colsAa colsBa O && O.pts[0]! == v && T.pts.size == n &&
    CFSG.Perm.Native.treeOK n 0 T ls #[0, 1] && others.all fun w => !O.pts.contains w

@[expose] def coverCheck11 : Bool :=
  (List.range (2 ^ 11)).all fun w =>
    w == 0 || (orbitOf11 eMaskC 1288).pts.contains w || (orbitOf11 eMaskA 759).pts.contains w

end CFSG.EvenSporadicStandard.TwoCo1

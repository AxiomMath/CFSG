module

public import CFSG.HardMathSupport.Malle.SeitzCube.E6ThreeKernelData
public import CFSG.RankThree.Lattice.SteinbergBIListMatrix

public section

namespace CFSG.HardMathSupport.Malle.SeitzCube

open CFSG.Blueprint CFSG.Blueprint.Chevalley

@[expose] def e6D4Wp : List (Fin 6) :=
  [4, 5, 3, 4, 2, 3, 0, 2, 1, 3, 4, 5, 4, 3, 2, 1, 3, 4, 0, 2, 3, 0, 2, 1]

@[expose] def e6D4M : List (Fin 6) := [0, 2, 3, 1]

@[expose] def e6D4Ws (s : Fin 3) : List (Fin 6) :=
  match s with
  | 0 => [5, 0, 2, 3, 4, 3, 1]
  | 1 => [5, 0, 2, 3, 4, 1, 3, 2, 1]
  | 2 => [5, 0, 2, 3, 4, 3, 2, 1, 3]

@[expose] def e6D4RootsF : Finset (Fin Tag.E6.rank → ℤ) :=
  (rootFinset .E6).filter fun α => α 0 = 0 ∧ α 5 = 0

theorem e6D4_twist : ∀ i : Fin 3, i ≠ 2 → ∀ k : Fin 6,
    e6KerP i (e6D4Wp.foldr (reflect Tag.E6) (Pi.single k 1)) = - e6KerQ i (Pi.single k 1) ∧
    e6KerQ i (e6D4Wp.foldr (reflect Tag.E6) (Pi.single k 1)) =
      e6KerP i (Pi.single k 1) - e6KerQ i (Pi.single k 1) := by
  decide +kernel

theorem e6D4_image : ∀ s : Fin 3,
    (e6BlockRootsF 2 ∪ e6MixedRootsF s).image
      (fun v => (e6D4Ws s ++ e6D4M).foldr (reflect Tag.E6) v) = e6D4RootsF := by
  decide +kernel

end CFSG.HardMathSupport.Malle.SeitzCube

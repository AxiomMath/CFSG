module

public import CFSG.LieType.SeitzGeneration.ExcTorusBlocks
public import CFSG.LieType.SeitzGeneration.ExcTorusTw

public section

namespace CFSG.HardMathSupport.Lang.SeitzPlane

open CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.SeitzGeneration CFSG.RankThree.Lattice CFSG.RankThree.PartOne.KE Polynomial
open scoped Matrix

@[expose] def twE6PlaneWord : List (Fin TwistTag.E6.tag.rank) := [0, 2, 0, 3, 2]

@[expose] def twE6PlaneMat : List (List ℤ) :=
  [[0, 1, 1, -1, 0, 0], [0, 1, 0, 0, 0, 0], [0, 1, 1, 0, -1, 0], [0, 1, 1, 0, -1, 1],
   [0, 0, 1, 0, 0, 0], [1, 0, 0, 0, 0, 0]]

@[expose] def twE6PlaneBasis : List (List ℤ) :=
  [[1, 0, -1, -1, -1, -1], [2, -1, -1, -1, -1, -1], [2, -1, -1, -1, -1, -2],
   [3, -1, -1, -2, -1, -3], [2, -1, -1, -1, 0, -1], [1, -1, -1, -1, -1, -1]]

@[expose] def twE6PlaneBasisInv : List (List ℤ) :=
  [[0, 1, 0, 0, 0, -1], [1, 0, 0, 0, 0, -1], [-1, 1, -1, 1, -1, 0], [0, 0, 2, -1, 0, -1],
   [0, -1, 0, 0, 1, 0], [0, 1, -1, 0, 0, 0]]

theorem twE6Plane_wordMat :
    wordMat TwistTag.E6.tag twE6PlaneWord =
      toMat TwistTag.E6.tag.rank (lmul TwistTag.E6.tag.rank twE6PlaneMat twE6PermList) :=
  wordMat_eq_toMat TwistTag.E6.tag _ (by decide +kernel)

theorem twE6Plane_pow : (toMat TwistTag.E6.tag.rank twE6PlaneMat) ^ 6 = 1 := by
  rw [← toMat_lpow, ← toMat_lid]
  exact congrArg (toMat TwistTag.E6.tag.rank) (by decide +kernel)

theorem twE6Plane_charpoly :
    (toMat TwistTag.E6.tag.rank twE6PlaneMat).charpoly =
      ([1, 2, 6, 6].map fun d => cyclotomic d ℤ).prod :=
  charpoly_of_basis twE6PlaneMat twE6PlaneBasis twE6PlaneBasisInv [1, 2, 6, 6]
    (by decide) (by decide) (by decide +kernel) (by decide +kernel)

@[expose] def twE6PlaneTheta : Fin TwistTag.E6.tag.rank → ℤ := ![1, 2, 2, 3, 2, 1]

@[expose] def twE6PlaneThetaTag : Fin Tag.E6.rank → ℤ := ![1, 2, 2, 3, 2, 1]

theorem twE6PlaneThetaTag_mem : twE6PlaneThetaTag ∈ rootFinset .E6 := by decide +kernel

theorem twE6PlaneTheta_mem : twE6PlaneTheta ∈ rootFinset .E6 := twE6PlaneThetaTag_mem

theorem twE6Plane_mulVec_theta :
    toMat TwistTag.E6.tag.rank twE6PlaneMat *ᵥ twE6PlaneTheta = twE6PlaneTheta := by
  show toMat 6 twE6PlaneMat *ᵥ (![1, 2, 2, 3, 2, 1] : Fin 6 → ℤ) = ![1, 2, 2, 3, 2, 1]
  decide +kernel

theorem permLattice_E6_theta : permLattice TwistTag.E6.perm twE6PlaneTheta = twE6PlaneTheta := by
  rw [permLattice_E6_eq]
  show toMat 6 twE6PermList *ᵥ (![1, 2, 2, 3, 2, 1] : Fin 6 → ℤ) = ![1, 2, 2, 3, 2, 1]
  decide +kernel

end CFSG.HardMathSupport.Lang.SeitzPlane

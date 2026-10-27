module

public import CFSG.ClassicalGroups.Symplectic.Sp6ThreeLocalNormalizer
public import CFSG.ClassicalGroups.Symplectic.Sp6ThreeLocalRealizers
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.KInputs811CoordDefs

public section

namespace CFSG.ClassicalGroups.Symplectic.Sp6ThreeLocal

open CFSG.Open CFSG.Open.StatedAPI CFSG.LinearAlgebra
open CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82 (IsSignedCoords)
open scoped MatrixGroups

variable {K : Type} [Field K]

theorem c₀_signedCoords {s : SL(2, K)} (hs : IsCubeRootBlock s) :
    IsSignedCoords (c₀ hs).range (c₀ hs) :=
  ⟨c₀_injective hs, rfl, c₀_normalizer hs, c₀_realizer hs⟩

end CFSG.ClassicalGroups.Symplectic.Sp6ThreeLocal

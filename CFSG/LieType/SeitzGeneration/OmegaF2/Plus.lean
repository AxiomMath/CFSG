module

public import CFSG.LieType.SeitzGeneration.OmegaF2.Engine
public import CFSG.LieType.SeitzGeneration.RootPairOrthPlusChar2

public section

namespace CFSG.LieType.SeitzGeneration

open QuadraticMap CFSG.ClassicalGroups.Orthogonal CFSG.RankThree.PartOne.KCOrthogonalSubfield
  CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
  CFSG.ComponentClassification.CatalogueBOrthogonalPointData
open RootPairOrth

theorem OmegaF2.tailAnisotropic_plus (n : ℕ) (K : Type) [Field K] (hn : 4 ≤ n) :
    OmegaF2.TailAnisotropic (plusHyp n K hn) := by
  intro v hv _
  funext a
  exact hv a (Finset.mem_univ _)

theorem subfieldPairOmegaPlusF2_holds : SubfieldPairOmegaPlusF2 := by
  intro n p hn hp hp3 K _ _ k hk hK
  haveI : CharP K 2 := OmegaF2.charP_two_of_subfield_card_two hk
  have hp2 : p ≠ 2 := by omega
  have hk1 : Nat.card k = 2 ^ 1 := by simpa using hk
  have hK1 : Nat.card K = 2 ^ (1 * p) := by simpa using hK
  have hdeg : Module.finrank k K = p := finrank_subfield_eq k Nat.prime_two (by omega) hk1 hK1
  have hK' : Nat.card K = Nat.card k ^ p := by rw [hK, hk]
  intro g hg hne
  obtain ⟨gl, rfl⟩ := hg
  exact OmegaF2.orthPair_of_hypCoord_F2 (plusHyp n K hn) (OmegaF2.tailAnisotropic_plus n K hn) hk
    (coordinateQuadPlus_isExtension k n) (commutator_coordinateQuadPlus n K (by omega)).symm
    (regular_coordinateQuadPlus n K (by omega)).1 hp hp2 hdeg hK'
    (fun σ hσo hσk => subfieldSetup_plus k hσk hp hp2 hσo (by omega)) gl.1
    ((mem_linearSimilarityPairs_iff _ gl.1).mp gl.2) hne

end CFSG.LieType.SeitzGeneration

module

public import CFSG.CharacterTheory.BrauerThirdMainTheorem.Blocks
public import CFSG.CharacterTheory.BrauerThirdMainTheorem.Idempotents
public import CFSG.CharacterTheory.BrauerThirdMainTheorem.Projection
public import CFSG.CharacterTheory.BrauerThirdMainTheorem.OrbitCongruence
public import CFSG.CharacterTheory.BrauerThirdMainTheorem.CentralCharacters
public import CFSG.CharacterTheory.BrauerThirdMainTheorem.Convolution
public import CFSG.CharacterTheory.BrauerThirdMainTheorem.Spectral
public import CFSG.CharacterTheory.BrauerThirdMainTheorem.LocalCoefficientRing
public import CFSG.CharacterTheory.BrauerThirdMainTheorem.PolynomialProjectors
public import CFSG.CharacterTheory.BrauerThirdMainTheorem.CentralIntegrality
public import CFSG.CharacterTheory.BrauerThirdMainTheorem.PolynomialCoefficients
public import CFSG.CharacterTheory.BrauerThirdMainTheorem.BlockResidues
public import CFSG.CharacterTheory.BrauerThirdMainTheorem.PrincipalImage
public import CFSG.CharacterTheory.BrauerThirdMainTheorem.BlockAtoms
public import CFSG.CharacterTheory.BrauerThirdMainTheorem.ModularFixedPoints
public import CFSG.CharacterTheory.BrauerThirdMainTheorem.ResidueExtension
public import CFSG.CharacterTheory.BrauerThirdMainTheorem.ModularRadical
public import CFSG.CharacterTheory.BrauerThirdMainTheorem.ClassCoefficients
public import CFSG.CharacterTheory.BrauerThirdMainTheorem.LocalGroupAlgebra
public import CFSG.CharacterTheory.BrauerThirdMainTheorem.NormalPVanishing
public import CFSG.CharacterTheory.BrauerThirdMainTheorem.CentralResidueMaps
public import CFSG.CharacterTheory.BrauerThirdMainTheorem.CharacterTransport
public import CFSG.CharacterTheory.BrauerThirdMainTheorem.SubgroupCoefficients
public import CFSG.CharacterTheory.BrauerThirdMainTheorem.ProjectionMultiplicativity
public import CFSG.CharacterTheory.BrauerThirdMainTheorem.ProjectionTransitivity
public import CFSG.CharacterTheory.BrauerThirdMainTheorem.NormalCentralAlgebra
public import CFSG.CharacterTheory.BrauerThirdMainTheorem.NormalCentralizerProjection
public import CFSG.CharacterTheory.BrauerThirdMainTheorem.NormalPrincipalCriterion
public import CFSG.CharacterTheory.BrauerThirdMainTheorem.NormalizerReduction
public import CFSG.CharacterTheory.BrauerThirdMainTheorem.DefectDefinitions
public import CFSG.CharacterTheory.BrauerThirdMainTheorem.ThirdMainTheorem

public section

open CFSG

namespace CFSG.BrauerThirdMainTheorem

theorem brauer_third_main_theorem (p : ℕ) (hp : p.Prime) (m : Ideal BlocksAlgInt) (hm : m.IsMaximal)
    (hpm : (p : BlocksAlgInt) ∈ m)
    (G : Type) [Group G] [Finite G] (P H : Subgroup G) (hP : IsPGroup p P)
    (hPH : P ≤ H) (hCH : Subgroup.centralizer (P : Set G) ≤ H)
    (hHN : H ≤ Subgroup.normalizer (P : Set G))
    (β : Set (H → ℂ)) (hβ : BlocksIsBlock m H β) :
    BlocksBrauerCorr m P H β (BlocksPrincipalBlock m G) ↔ β = BlocksPrincipalBlock m H := by
  constructor
  · exact Helpers.principal_of_brauerCorr p hp m hm hpm G P H hP hPH hCH hHN hβ
  · rintro rfl
    exact Helpers.brauerCorr_principal m hm p hp hpm G P H hP hCH hHN

end CFSG.BrauerThirdMainTheorem

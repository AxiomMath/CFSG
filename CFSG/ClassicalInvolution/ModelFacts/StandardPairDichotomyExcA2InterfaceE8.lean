module

public import CFSG.ClassicalInvolution.ModelFacts.StandardPairDichotomyExcA2Interface
public import CFSG.ClassicalInvolution.ModelFacts.StandardPairDichotomyExcA2E8Factor

public section

namespace CFSG.ClassicalInvolution.ModelFacts.Levi

open CFSG.Assembly.LowTwoRank CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Steinberg.Adjoint CFSG.LieType.AlgebraicGroups
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.ClassicalInvolution.ModelFacts
open CFSG.ClassicalInvolution.Phan (UnitaryBlockStandardPair)

@[expose] def A2UnitaryE8 (p e : ℕ) [Fact p.Prime] : Prop :=
  StatedLieAdmissible .E8 0 p e → p ≠ 2 → 5 ≤ p ^ e →
    ∀ (R₂ : Subgroup ↥(adjointGroup .E8 (GaloisField p e)))
      (c₂ : ↥(adjointGroup .E8 (GaloisField p e))),
      R₂ ∈ longestFundamental (e8Datum (GaloisField p e)) → c₂ ∈ R₂ → orderOf c₂ = 2 →
      (c₂ : ModGL .E8 (GaloisField p e)) * signDiagE8 (GaloisField p e) thetaE8 =
        signDiagE8 (GaloisField p e) thetaE8 * (c₂ : ModGL .E8 (GaloisField p e)) →
      ¬ (∀ r ∈ stdRankOne (e8Datum (GaloisField p e)) thetaE8, c₂ * r = r * c₂) →
      (∃ v ∈ h1E8 (AlgClosGF p e),
        v * baseChangeGL (algebraMap (GaloisField p e) (AlgClosGF p e))
            (c₂ : ModGL .E8 (GaloisField p e)) * v⁻¹ = signDiagE8 (AlgClosGF p e) deltaE8 ∧
        ∃ m ∈ parabolicLevi .E8 (AlgClosGF p e) JE8,
          entrywiseFrobGL .E8 (AlgClosGF p e) p e v * v⁻¹ =
            m * rootSL2 .E8 (AlgClosGF p e) thetaE8 WSL) →
      ∃ W, UnitaryBlockStandardPair (GaloisField p (2 * e)) p e W
        (stdRankOne (e8Datum (GaloisField p e)) thetaE8) R₂

end CFSG.ClassicalInvolution.ModelFacts.Levi

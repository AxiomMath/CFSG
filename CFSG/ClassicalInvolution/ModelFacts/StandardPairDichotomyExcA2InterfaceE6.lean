module

public import CFSG.ClassicalInvolution.ModelFacts.StandardPairDichotomyExcA2Interface
public import CFSG.ClassicalInvolution.ModelFacts.StandardPairDichotomyExcA2E6Factor

public section

namespace CFSG.ClassicalInvolution.ModelFacts.Levi

open CFSG.Assembly.LowTwoRank CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Steinberg.Adjoint CFSG.LieType.AlgebraicGroups
  CFSG.LieType.Steinberg.Isogeny CFSG.LieType.Steinberg.Minuscule
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.ClassicalInvolution.ModelFacts
open CFSG.ClassicalInvolution.Phan (UnitaryBlockStandardPair)

@[expose] def A2UnitaryE6 (p e : ℕ) [Fact p.Prime] : Prop :=
  StatedLieAdmissible .E6 0 p e → p ≠ 2 → 5 ≤ p ^ e →
    ∀ (R₂ : Subgroup (E6sc p e)) (c₂ : E6sc p e),
      R₂ ∈ longestFundamental (e6Datum (GaloisField p e)) → c₂ ∈ R₂ → orderOf c₂ = 2 →
      ((e6Isogeny (GaloisField p e) c₂ : ↥(adjointGroup .E6 (GaloisField p e))) :
        ModGL .E6 (GaloisField p e)) * signDiagE6 (GaloisField p e) thetaE6 =
        signDiagE6 (GaloisField p e) thetaE6 *
          ((e6Isogeny (GaloisField p e) c₂ : ↥(adjointGroup .E6 (GaloisField p e))) :
            ModGL .E6 (GaloisField p e)) →
      ¬ (∀ r ∈ stdRankOne (e6Datum (GaloisField p e)) thetaE6, c₂ * r = r * c₂) →
      (∃ v ∈ h1E6 (AlgClosGF p e),
        v * baseChangeGL (algebraMap (GaloisField p e) (AlgClosGF p e))
            ((e6Isogeny (GaloisField p e) c₂ : ↥(adjointGroup .E6 (GaloisField p e))) :
              ModGL .E6 (GaloisField p e)) * v⁻¹ = signDiagE6 (AlgClosGF p e) deltaE6 ∧
        ∃ m ∈ parabolicLevi .E6 (AlgClosGF p e) JE6,
          entrywiseFrobGL .E6 (AlgClosGF p e) p e v * v⁻¹ =
            m * rootSL2 .E6 (AlgClosGF p e) thetaE6 WSL) →
      ∃ W, UnitaryBlockStandardPair (GaloisField p (2 * e)) p e W
        (stdRankOne (e6Datum (GaloisField p e)) thetaE6) R₂

end CFSG.ClassicalInvolution.ModelFacts.Levi

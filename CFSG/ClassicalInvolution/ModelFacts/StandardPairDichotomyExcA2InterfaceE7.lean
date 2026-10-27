module

public import CFSG.ClassicalInvolution.ModelFacts.StandardPairDichotomyExcA2Interface
public import CFSG.ClassicalInvolution.ModelFacts.StandardPairDichotomyExcA2E7Factor

public section

namespace CFSG.ClassicalInvolution.ModelFacts.Levi

open CFSG.Assembly.LowTwoRank CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Steinberg.Adjoint CFSG.LieType.AlgebraicGroups
  CFSG.LieType.Steinberg.Isogeny CFSG.LieType.Steinberg.Minuscule
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.ClassicalInvolution.ModelFacts
open CFSG.ClassicalInvolution.Phan (UnitaryBlockStandardPair)

@[expose] def A2UnitaryE7 (p e : ℕ) [Fact p.Prime] : Prop :=
  StatedLieAdmissible .E7 0 p e → p ≠ 2 → 5 ≤ p ^ e →
    ∀ (R₂ : Subgroup (E7sc p e)) (c₂ : E7sc p e),
      R₂ ∈ longestFundamental (e7Datum (GaloisField p e)) → c₂ ∈ R₂ → orderOf c₂ = 2 →
      ((e7Isogeny (GaloisField p e) c₂ : ↥(adjointGroup .E7 (GaloisField p e))) :
        ModGL .E7 (GaloisField p e)) * signDiagE7 (GaloisField p e) thetaE7 =
        signDiagE7 (GaloisField p e) thetaE7 *
          ((e7Isogeny (GaloisField p e) c₂ : ↥(adjointGroup .E7 (GaloisField p e))) :
            ModGL .E7 (GaloisField p e)) →
      ¬ (∀ r ∈ stdRankOne (e7Datum (GaloisField p e)) thetaE7, c₂ * r = r * c₂) →
      (∃ v ∈ h1E7 (AlgClosGF p e),
        v * baseChangeGL (algebraMap (GaloisField p e) (AlgClosGF p e))
            ((e7Isogeny (GaloisField p e) c₂ : ↥(adjointGroup .E7 (GaloisField p e))) :
              ModGL .E7 (GaloisField p e)) * v⁻¹ = signDiagE7 (AlgClosGF p e) deltaE7 ∧
        ∃ m ∈ parabolicLevi .E7 (AlgClosGF p e) JE7,
          entrywiseFrobGL .E7 (AlgClosGF p e) p e v * v⁻¹ =
            m * rootSL2 .E7 (AlgClosGF p e) thetaE7 WSL) →
      ∃ W, UnitaryBlockStandardPair (GaloisField p (2 * e)) p e W
        (stdRankOne (e7Datum (GaloisField p e)) thetaE7) R₂

end CFSG.ClassicalInvolution.ModelFacts.Levi

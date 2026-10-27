module

public import CFSG.ClassicalInvolution.ModelFacts.StandardPairDichotomyExcA2F4Factor
public import CFSG.ClassicalInvolution.ModelFacts.PairFrameExcReduce

public section

namespace CFSG.ClassicalInvolution.ModelFacts.Levi

open CFSG.Assembly.LowTwoRank CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Steinberg.Adjoint CFSG.LieType.AlgebraicGroups
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.ClassicalInvolution.ModelFacts
open CFSG.ClassicalInvolution.Phan (UnitaryBlockStandardPair)

abbrev AlgClosGF (p e : ℕ) [Fact p.Prime] : Type := AlgebraicClosure (GaloisField p e)

instance instCharPAlgClosGF (p e : ℕ) [Fact p.Prime] : CharP (AlgClosGF p e) p :=
  charP_of_injective_algebraMap (algebraMap (GaloisField p e) (AlgClosGF p e)).injective p

@[expose] def A2UnitaryF4 (p e : ℕ) [Fact p.Prime] : Prop :=
  StatedLieAdmissible .F4 0 p e → p ≠ 2 → 5 ≤ p ^ e →
    ∀ (R₂ : Subgroup ↥(adjointGroup .F4 (GaloisField p e)))
      (c₂ : ↥(adjointGroup .F4 (GaloisField p e))),
      R₂ ∈ longestFundamental (f4Datum (GaloisField p e)) → c₂ ∈ R₂ → orderOf c₂ = 2 →
      (c₂ : ModGL .F4 (GaloisField p e)) * signDiagF4 (GaloisField p e) thetaF4 =
        signDiagF4 (GaloisField p e) thetaF4 * (c₂ : ModGL .F4 (GaloisField p e)) →
      ¬ (∀ r ∈ stdRankOne (f4Datum (GaloisField p e)) thetaF4, c₂ * r = r * c₂) →
      (∃ v ∈ h1F4 (AlgClosGF p e),
        v * baseChangeGL (algebraMap (GaloisField p e) (AlgClosGF p e))
            (c₂ : ModGL .F4 (GaloisField p e)) * v⁻¹ = signDiagF4 (AlgClosGF p e) deltaF4 ∧
        ∃ m ∈ parabolicLevi .F4 (AlgClosGF p e) JF4,
          entrywiseFrobGL .F4 (AlgClosGF p e) p e v * v⁻¹ =
            m * rootSL2 .F4 (AlgClosGF p e) thetaF4 WSL) →
      ∃ W, UnitaryBlockStandardPair (GaloisField p (2 * e)) p e W
        (stdRankOne (f4Datum (GaloisField p e)) thetaF4) R₂

end CFSG.ClassicalInvolution.ModelFacts.Levi

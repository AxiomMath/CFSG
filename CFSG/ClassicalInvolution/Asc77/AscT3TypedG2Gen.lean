module

public import CFSG.ClassicalInvolution.ModelFacts.G2D4Max

public section

namespace CFSG.ClassicalInvolution.Asc77.T3Typed

open CFSG.ClassicalInvolution.Generic CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.G2D4Models

@[expose] def G2CentralizersGenerate (p : ℕ) [Fact p.Prime] : Prop :=
  ∀ e : ℕ, StatedLieAdmissible .G2 0 p e → p ≠ 2 → 5 ≤ p ^ e →
    ∀ z z' : (modelUniv .G2 0 p e Fact.out).K, z * z = 1 → z' * z' = 1 → z ≠ 1 → z' ≠ 1 →
      z ≠ z' → z * z' = z' * z →
        Subgroup.centralizer ({z} : Set (modelUniv .G2 0 p e Fact.out).K) ⊔
          Subgroup.centralizer ({z'} : Set (modelUniv .G2 0 p e Fact.out).K) = ⊤

@[expose] def D4NormalizerMax (p : ℕ) [Fact p.Prime] : Prop :=
  ∀ e : ℕ, StatedLieAdmissible .trialityD4 0 p e → p ≠ 2 →
    ∀ R ∈ fundamentalSubgroups .trialityD4 (modelUniv .trialityD4 0 p e Fact.out).D,
      IsCoatom (Subgroup.normalizer (R : Set (modelUniv .trialityD4 0 p e Fact.out).K))

theorem d4NormalizerMax_of_maxNormalizer {p : ℕ} [Fact p.Prime] (hM : G2D4MaxNormalizer p) :
    D4NormalizerMax p :=
  fun e hadm hp2 R hR => hM .trialityD4 0 e hadm hp2 (Or.inr rfl) R hR

end CFSG.ClassicalInvolution.Asc77.T3Typed

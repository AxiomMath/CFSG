module

public import CFSG.ClassicalInvolution.Generic.Induction
public import CFSG.LieType.HighestRoot.Defs

public section

namespace CFSG.ComponentClassification.RankTwoOddLie

open Subgroup CFSG.Assembly.LowTwoRank CFSG.LieType.HighestRoot
open CFSG.ClassicalInvolution.Generic (modelUniv IsFundTag IsLongestRoot)
open scoped MatrixGroups

@[expose] def ModelCenterPPrime : Prop :=
  ∀ (t : StatedLieTag) (n p e : ℕ) (hp : p.Prime), p ≠ 2 → IsFundTag t →
    StatedLieAdmissible t n p e →
    ∀ z ∈ center (modelUniv t n p e hp).K, z ^ p = 1 → z = 1

@[expose] def ModelAutLift : Prop :=
  ∀ (t : StatedLieTag) (n p e : ℕ) (hp : p.Prime), p ≠ 2 → IsFundTag t →
    StatedLieAdmissible t n p e →
    ∀ (X G : Type) [Group X] [Group G] [Finite X] [Finite G]
      (ψ₀ : (modelUniv t n p e hp).K →* X) (ψ : X →* G), Function.Surjective ψ₀ →
      ψ₀.ker ≤ center (modelUniv t n p e hp).K → Odd (Nat.card ψ₀.ker) →
      IsPGroup 2 (center X) → Function.Surjective ψ → ψ.ker ≤ center X →
      ∀ τ : MulAut G, ∃ τ' : MulAut X, ∀ x, ψ (τ' x) = τ (ψ x)

@[expose] def SL2OuterComm : Prop :=
  ∀ (F : Type) [Field F] [Finite F], Odd (Nat.card F) →
    ∀ α β : MulAut SL(2, F), ∃ y : SL(2, F), α * β * α⁻¹ * β⁻¹ = MulAut.conj y

@[expose] def TrialityD4SL2Unique : Prop :=
  ∀ (n p e : ℕ) [Fact p.Prime], p ≠ 2 → StatedLieAdmissible .trialityD4 n p e → 5 ≤ p ^ e →
    ∀ γ, IsLongestRoot (modelUniv .trialityD4 n p e Fact.out).D γ →
    ∀ z ∈ rankOneGroup (modelUniv .trialityD4 n p e Fact.out).D γ, orderOf z = 2 →
    ∀ L : Subgroup (modelUniv .trialityD4 n p e Fact.out).K, L ≤ centralizer {z} →
      centralizer {z} ≤ normalizer (L : Set (modelUniv .trialityD4 n p e Fact.out).K) →
      Nonempty (L ≃* SL(2, GaloisField p e)) → z ∈ L →
      L = rankOneGroup (modelUniv .trialityD4 n p e Fact.out).D γ

end CFSG.ComponentClassification.RankTwoOddLie

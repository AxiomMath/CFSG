module

public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.ClassicalInvolution.Balance.Basic
public import CFSG.ClassicalInvolution.Q3.Basic
public import CFSG.GroupTheory.LocalCores.PrimeSetCore

public section

namespace CFSG.ClassicalInvolution.Q3.Q3T

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.LocalCores

@[expose] def SteinbergOddAut3 : Prop :=
  ∀ (t : CFSG.Assembly.LowTwoRank.StatedLieTag) (n : ℕ), Generic.IsFundTag t →
    CFSG.Assembly.LowTwoRank.StatedLieAdmissible t n 3 1 →
      ∀ (X : Type) [Group X] [Finite X], CFSG.Open.IsQuasisimple X → Subgroup.center X = ⊥ →
        ∀ f : (Generic.modelUniv t n 3 1 Nat.prime_three).K →* X, Function.Surjective f →
          f.ker ≤ Subgroup.center (Generic.modelUniv t n 3 1 Nat.prime_three).K →
            ∀ α : MulAut X, Odd (orderOf α) →
              (∃ g : X, α = MulAut.conj g) ∨ (t = .POmegaPlus ∧ n = 4) ∨ t = .trialityD4

@[expose] def D4OddAutInner3 : Prop :=
  ∀ (X : Type) [Group X] [Finite X], CFSG.Open.IsQuasisimple X → Subgroup.center X = ⊥ →
    ∀ f : (Generic.modelUniv .POmegaPlus 4 3 1 Nat.prime_three).K →* X, Function.Surjective f →
      f.ker ≤ Subgroup.center (Generic.modelUniv .POmegaPlus 4 3 1 Nat.prime_three).K →
        ∀ (z : X) (K : Subgroup X), IsClassicalMember3 K z →
          ∀ α : MulAut X, Odd (orderOf α) →
            (∀ c ∈ Subgroup.centralizer ({z} : Set X),
              c⁻¹ * α c ∈ Balance.oddCoreIn (Subgroup.centralizer ({z} : Set X))) →
              ∃ g : X, α = MulAut.conj g

@[expose] def TrialityD4OddAutInner3 : Prop :=
  ∀ (X : Type) [Group X] [Finite X], CFSG.Open.IsQuasisimple X → Subgroup.center X = ⊥ →
    ∀ f : (Generic.modelUniv .trialityD4 0 3 1 Nat.prime_three).K →* X, Function.Surjective f →
      f.ker ≤ Subgroup.center (Generic.modelUniv .trialityD4 0 3 1 Nat.prime_three).K →
        ∀ (z : X) (K : Subgroup X), IsClassicalMember3 K z →
          ∀ α : MulAut X, Odd (orderOf α) →
            (∀ c ∈ Subgroup.centralizer ({z} : Set X),
              c⁻¹ * α c ∈ Balance.oddCoreIn (Subgroup.centralizer ({z} : Set X))) →
              ∃ g : X, α = MulAut.conj g

end CFSG.ClassicalInvolution.Q3.Q3T

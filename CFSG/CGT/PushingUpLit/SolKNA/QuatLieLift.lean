module

public import CFSG.ClassicalInvolution.Q3.TL3LeafEdge
public import CFSG.CGT.PushingUpLit.SolKAb.Setup
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherTheorem3Statement

public section

namespace CFSG.CGT.PushingUpLit.SolKNA

open CFSG.CGT.PushingUpLit.SolKAb (STSetting sylowImg)
open CFSG.ComponentClassification.AschbacherTheorem3 (IsQuaternionTwoGroup)
open CFSG.Assembly (pCoreOf)
open CFSG.Assembly.LowTwoRank (StatedLieTag StatedLieAdmissible)
open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Q3
open CFSG.ClassicalInvolution.Generic

@[expose] def TightLiftSimple : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G], (∃ a b : G, a * b ≠ b * a) →
    ¬ TwoSubgroupsFourGenerated G →
    ∀ (R : Subgroup G) (S : Sylow 2 R) (t : G), TightDatum R S t → TightHasLift R t


@[expose] def Lie3Table : Prop :=
  ∀ (τ : StatedLieTag) (n : ℕ), IsFundTag τ → StatedLieAdmissible τ n 3 1 →
    ∀ (X : Type) [Group X] [Finite X] (ψ : (modelUniv τ n 3 1 Nat.prime_three).K →* X),
      Function.Surjective ψ → ψ.ker ≤ Subgroup.center _ →
      ∀ (R : Subgroup (modelUniv τ n 3 1 Nat.prime_three).K),
        R ∈ fundamentalSubgroups τ (modelUniv τ n 3 1 Nat.prime_three).D →
      ∀ (K : Subgroup X), STSetting X K → ∀ R₀ : Sylow 2 K, IsQuaternionTwoGroup (sylowImg R₀) →
        pCoreOf 2 K ≤ R.map ψ →
        (τ = .PSL ∧ n = 3) ∨ (τ = .PSU ∧ n = 3) ∨ τ = .G2

end CFSG.CGT.PushingUpLit.SolKNA

module

public import CFSG.LieType.SeitzGeneration.OrthLift

public section

namespace CFSG.LieType.SeitzGeneration

open Module QuadraticMap
open CFSG.RankThree.Classical2 (orthDerived)

@[expose] def OrthNoInvariantSingular {K V : Type} [Field K]
    [AddCommGroup V] [Module K V] (Q : QuadraticForm K V)
    (E : Subgroup (orthDerived Q)) : Prop :=
  ∀ T : Submodule K V,
    (∀ e ∈ E, ∀ vector ∈ T, ((e : orthDerived Q) : V ≃ₗ[K] V) vector ∈ T) →
    (∀ vector ∈ T, Q vector = 0) → T = ⊥

@[expose] def OrthMasterScoped
    (scope : ∀ (K V : Type) [Field K] [AddCommGroup V] [Module K V],
      (Q : QuadraticForm K V) → Subgroup (orthDerived Q) → Prop) : Prop :=
  ∀ (K V : Type) [Field K] [Finite K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    (Q : QuadraticForm K V), (polarBilin Q).Nondegenerate →
    (∃ T : Submodule K V, finrank K T = 3 ∧ ∀ vector ∈ T, Q vector = 0) →
    7 ≤ finrank K V → ∀ prime : ℕ, prime.Prime → 5 ≤ prime → prime ≠ ringChar K →
    ∀ E : Subgroup (orthDerived Q),
      (∀ first ∈ E, ∀ second ∈ E, first * second = second * first) →
      (∀ element ∈ E, element ^ prime = 1) → Nat.card E = prime ^ 2 →
      scope K V Q E →
      Subgroup.closure {element : orthDerived Q |
        ∃ witness ∈ E, witness ≠ 1 ∧ element * witness = witness * element} = ⊤

@[expose] def OrthMasterParabolic : Prop :=
  OrthMasterScoped fun _ _ _ _ _ Q E => ¬ OrthNoInvariantSingular Q E

@[expose] def OrthMasterNoSingular : Prop :=
  OrthMasterScoped fun _ _ _ _ _ Q E => OrthNoInvariantSingular Q E

theorem orthMaster_of_parabolic_noSingular
    (hParabolic : OrthMasterParabolic) (hNoSingular : OrthMasterNoSingular) : OrthMaster := by
  intro K V fieldInst finiteInst addInst moduleInst dimensionInst Q hQ hT hdim
    prime hPrime hFive hChar E hComm hExp hCard
  classical
  by_cases hNS : OrthNoInvariantSingular Q E
  · exact hNoSingular K V Q hQ hT hdim prime hPrime hFive hChar E hComm hExp hCard hNS
  · exact hParabolic K V Q hQ hT hdim prime hPrime hFive hChar E hComm hExp hCard hNS

end CFSG.LieType.SeitzGeneration

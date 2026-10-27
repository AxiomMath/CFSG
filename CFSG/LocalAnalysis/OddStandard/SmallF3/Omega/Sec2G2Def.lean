module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec3L34Inputs

public section

namespace CFSG.OddStandard.SmallF3.Omega

theorem orderOf_quaternion_a_two_eq_two :
    orderOf (QuaternionGroup.a 2 : QuaternionGroup 2) = 2 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact orderOf_eq_prime (by decide) (by decide)

@[expose] def Asc82OddCoreCentralizerQ8 : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y], FStarQuotientNoL81 Y →
    ∀ f : QuaternionGroup 2 →* Y, Function.Injective f →
      oddCore ↥(Subgroup.centralizer ({f (QuaternionGroup.a 2)} : Set Y)) = ⊥

end CFSG.OddStandard.SmallF3.Omega

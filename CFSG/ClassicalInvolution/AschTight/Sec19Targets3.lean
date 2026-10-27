module

public import CFSG.ClassicalInvolution.AschTight.Sec19Targets2

public section

namespace CFSG.ClassicalInvolution.Disconnected.AschTight

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77

variable (p f : ℕ) [Fact p.Prime]

@[expose] def C19_7aTmp : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (K : Subgroup G) (z : G) (S : Sylow 2 G)
    (W : Subgroup G), Sec19Data p f K z S W →
      (W ⊔ sec19Y K z = oddCoreOf (sec19Y K z) ⊔ W ∧
          IsSL2Three (sec19X K z) (K ⊔ oddCoreOf (sec19X K z)) (p ^ f)) ∨
        ((K ⊔ sec19Y K z).relIndex (sec19X K z) = 2 ∧ IsSL2Three (W ⊔ K) K (p ^ f) ∧
          (∃ m : ℕ, IsSL2ModOdd (sec19Y K z) m ∧ IsSL2Three (W ⊔ sec19Y K z) (sec19Y K z) m) ∧
            IsQuaternionSub ((S : Subgroup G) ⊓ sec19Y K z) ∧
            Nat.card ↥((S : Subgroup G) ⊓ sec19Y K z) = Nat.card ↥((S : Subgroup G) ⊓ K)) ∨
        ((K ⊔ sec19Y K z).relIndex (sec19X K z) = 2 ∧ IsSL2Three (W ⊔ K) K (p ^ f) ∧
          sec19Y K z = oddCoreOf (sec19Y K z) ⊔ ((S : Subgroup G) ⊓ sec19Y K z) ∧
            IsQuaternionSub ((S : Subgroup G) ⊓ sec19Y K z) ∧
            Nat.card ↥((S : Subgroup G) ⊓ sec19Y K z) = Nat.card ↥((S : Subgroup G) ⊓ K))

variable {p f}

theorem c19_6Tmp_of_c19_7aTmp (h7 : C19_7aTmp p f) : C19_6Tmp p f := by
  intro G _ _ _ K z S W hd
  rcases h7 G K z S W hd with ⟨h1, -⟩ | ⟨-, -, -, hQ, -⟩ | ⟨-, -, -, hQ, -⟩
  · exact Or.inl h1
  · exact Or.inr hQ
  · exact Or.inr hQ

end CFSG.ClassicalInvolution.Disconnected.AschTight

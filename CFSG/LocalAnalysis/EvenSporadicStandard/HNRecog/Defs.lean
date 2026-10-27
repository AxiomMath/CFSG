module

public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoHS.Defs
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.Extraspecial

public section

namespace CFSG.EvenSporadicStandard.HNRecog

open Subgroup

abbrev A5WrTwo : Type := alternatingGroup (Fin 5) ≀ᵣ Multiplicative (ZMod 2)

@[expose] def IsPlusExtraspecial (m : ℕ) {Γ : Type*} [Group Γ] (D : Subgroup Γ) : Prop :=
  CFSG.IsExtraspecial 2 ↥D ∧ Nat.card D = 2 ^ (1 + 2 * m) ∧
    ∃ E : Subgroup Γ, E ≤ D ∧ CFSG.Open.IsElemAbelian 2 E ∧ Nat.card E = 2 ^ (m + 1)

structure IsExtraspecialPlusByA5WrTwoWith (C : Type*) [Group C] (Q : Subgroup C) [Q.Normal] :
    Prop where
  plus : IsPlusExtraspecial 4 Q
  centralizer_le : centralizer (Q : Set C) ≤ Q
  quotient : Nonempty (C ⧸ Q ≃* A5WrTwo)

@[expose] def IsExtraspecialPlusByA5WrTwo (C : Type*) [Group C] : Prop :=
  ∃ (Q : Subgroup C) (_ : Q.Normal), IsExtraspecialPlusByA5WrTwoWith C Q

structure IsF5Type {G : Type} [Group G] (a z : G) : Prop where
  orderOf_a : orderOf a = 2
  orderOf_z : orderOf z = 2
  cent_a : ∃ E : Subgroup (centralizer ({a} : Set G)),
    TwoHS.IsF5Centralizer (centralizer ({a} : Set G)) E
  cent_z : IsExtraspecialPlusByA5WrTwo (centralizer ({z} : Set G))

end CFSG.EvenSporadicStandard.HNRecog

module

public import CFSG.Blueprint.Catalog
public import CFSG.Open.StandardComponentRecognitionMilestoneDefs

public section

namespace CFSG.ComponentClassification.RankTwoStandard

open CFSG.Blueprint CFSG.Assembly.LowTwoRank

abbrev rankTwoX {G : Type} [Group G] (A : Subgroup G) : Subgroup G :=
  Subgroup.normalClosure (A : Set G)

abbrev rankTwoQuot {G : Type} [Group G] (A : Subgroup G) : Type :=
  ↥A ⧸ Subgroup.center ↥A

structure RankTwoHyp (G : Type) [Group G] [Finite G] (A : Subgroup G) : Prop where
  kProper : Assembly.KProper Catalog G
  standard : Open.standardComponentIsStandard A
  not_normal : ¬ A.Normal
  rank : 2 ≤ Open.pRank 2 (Subgroup.centralizer (A : Set G))

@[expose] def RankTwoAlternatingType (Q : Type) [Group Q] : Prop :=
  ∃ n : ℕ, 5 ≤ n ∧ Nonempty (Q ≃* alternatingGroup (Fin n))

@[expose] def RankTwoBenderType (Q : Type) [Group Q] : Prop :=
  (∃ m : ℕ, 3 ≤ m ∧ StatedClassicalModel Q .PSL 2 2 m) ∨
    (∃ m : ℕ, 2 ≤ m ∧ StatedClassicalModel Q .PSU 3 2 m) ∨
    ∃ m : ℕ, 1 ≤ m ∧ SuzukiModel Q 2 (2 * m + 1)

@[expose] def RankTwoOddLieType (Q : Type) [Group Q] : Prop :=
  OddLieType Q ∧ ¬ Nonempty (Q ≃* alternatingGroup (Fin 5)) ∧
    ¬ Nonempty (Q ≃* alternatingGroup (Fin 6)) ∧ ¬ StatedClassicalModel Q .PSL 2 2 3

@[expose] def RankTwoExceptionalEvenType (Q : Type) [Group Q] : Prop :=
  (∃ m : ℕ, 2 ≤ m ∧ ChevalleyExceptionalModel Q .G2 2 m) ∨
    (∃ t : StatedLieTag, t ∈ ({.trialityD4, .F4, .E6, .twistedE6, .E7, .E8} : Finset _) ∧
      ∃ m : ℕ, 1 ≤ m ∧ ChevalleyExceptionalModel Q t 2 m) ∨
    (∃ m : ℕ, 1 ≤ m ∧ ReeTitsModel Q .twistedF4 2 (2 * m + 1)) ∨
    ReeTitsModel Q .Tits 2 1

@[expose] def RankTwoClassicalEvenType (Q : Type) [Group Q] : Prop :=
  ((∃ n m : ℕ, 4 ≤ n ∧ StatedClassicalModel Q .PSL n 2 m) ∨
    (∃ n m : ℕ, 4 ≤ n ∧ StatedClassicalModel Q .PSU n 2 m) ∨
    (∃ n m : ℕ, 2 ≤ n ∧ StatedClassicalModel Q .PSp n 2 m) ∨
    ∃ n m : ℕ, 4 ≤ n ∧
      (StatedClassicalModel Q .POmegaPlus n 2 m ∨ StatedClassicalModel Q .POmegaMinus n 2 m)) ∧
    ¬ Nonempty (Q ≃* alternatingGroup (Fin 8)) ∧ ¬ Nonempty (Q ≃* alternatingGroup (Fin 6))

@[expose] def RankTwoAlternatingStandard : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G), RankTwoHyp G A →
    Open.standardComponentOddCore G = ⊥ →
    ∀ n : ℕ, 5 ≤ n → Nonempty (rankTwoQuot A ≃* alternatingGroup (Fin n)) →
      Nonempty (rankTwoX A ≃* alternatingGroup (Fin (n + 4))) ∨
        (n = 5 ∧ NativeSporadic.IsSporadic (rankTwoX A) .J2) ∨
        (n = 5 ∧ NativeSporadic.IsSporadic (rankTwoX A) .M12 ∧ rankTwoX A ≠ ⊤)

@[expose] def RankTwoBenderStandard : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G), RankTwoHyp G A →
    Open.standardComponentOddCore G = ⊥ → RankTwoBenderType (rankTwoQuot A) →
      SuzukiModel (rankTwoQuot A) 2 3 ∧ NativeSporadic.IsSporadic (rankTwoX A) .Ru

@[expose] def RankTwoOddLieStandard : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G), RankTwoHyp G A →
    Open.standardComponentOddCore G = ⊥ → ¬ RankTwoOddLieType (rankTwoQuot A)

@[expose] def RankTwoL3EvenStandard : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G), RankTwoHyp G A →
    ∀ m : ℕ, 2 ≤ m → StatedClassicalModel (rankTwoQuot A) .PSL 3 2 m →
      (Open.standardComponentOddCore G = ⊥ → m = 2) ∧
      (m = 2 →
        (NativeSporadic.IsSporadic (rankTwoX A ⧸ Subgroup.center (rankTwoX A)) .Suz ∧
            Nat.card (Subgroup.center (rankTwoX A)) ∣ 3) ∨
          (Nonempty (Subgroup.center A ≃* Multiplicative (ZMod 2) × Multiplicative (ZMod 2)) ∧
            NativeSporadic.IsSporadic (rankTwoX A) .He)) ∧
      (Open.standardComponentOddCore G = ⊥ →
        NativeSporadic.IsSporadic (rankTwoX A) .Suz ∨
          (Nonempty (Subgroup.center A ≃* Multiplicative (ZMod 2) × Multiplicative (ZMod 2)) ∧
            NativeSporadic.IsSporadic (rankTwoX A) .He))

@[expose] def RankTwoExceptionalEvenStandard : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G), RankTwoHyp G A →
    Open.standardComponentOddCore G = ⊥ → RankTwoExceptionalEvenType (rankTwoQuot A) →
      ChevalleyExceptionalModel A .G2 2 2 ∧ NativeSporadic.IsSporadic (rankTwoX A) .Co1

@[expose] def RankTwoClassicalEvenStandard : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G), RankTwoHyp G A →
    Open.standardComponentOddCore G = ⊥ → ¬ RankTwoClassicalEvenType (rankTwoQuot A)

@[expose] def RankTwoSporadicStandard : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G), RankTwoHyp G A →
    ¬ NativeSporadic.SporadicRep (rankTwoQuot A)

end CFSG.ComponentClassification.RankTwoStandard

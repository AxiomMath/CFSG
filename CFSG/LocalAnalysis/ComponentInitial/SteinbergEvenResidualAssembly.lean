module

public import CFSG.LocalAnalysis.ComponentInitial.SteinbergEvenTwoMultiplierFrontier
public import CFSG.LocalAnalysis.ComponentInitial.SteinbergCBCorefreeCenter
public import CFSG.LocalAnalysis.ComponentInitial.SteinbergSuzukiEightZStar
public import CFSG.Blueprint.EvenBNRankTwoExact
public import CFSG.LieType.CurtisTits.Conclusion

public section

namespace CFSG.LocalAnalysis.ComponentInitial.EvenResidual

open Subgroup CFSG.Open CFSG.Blueprint CFSG.Blueprint.Recognition.Exact

@[expose] def SuzukiEightExclusion : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G], (∃ a b : G, a * b ≠ b * a) →
    ∀ L : Subgroup G, standardComponentIsStandard L →
    ∀ S : Sylow 2 (centralizer (L : Set G)), IsCyclic (S : Subgroup (centralizer (L : Set G))) →
    (∀ t : G, orderOf t = 2 →
      standardComponentOddCore (centralizer ({t} : Set G)) = ⊥) →
    Nat.card (center L) = 2 → LieModel (L ⧸ center L) .twistedB2 0 2 3 → False

@[expose] def SeitzCenterlessStatement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G], (∃ a b : G, a * b ≠ b * a) →
    CFSG.Assembly.KProper CFSG.Blueprint.Catalog G →
    ∀ L : Subgroup G, standardComponentIsStandard L →
    (∀ t : G, orderOf t = 2 →
      standardComponentOddCore (centralizer ({t} : Set G)) = ⊥) →
    ∀ S : Sylow 2 (centralizer (L : Set G)), IsCyclic (S : Subgroup (centralizer (L : Set G))) →
    EvenStandardType (L ⧸ center L) → ¬ EvenStandardException (L ⧸ center L) →
    center L = ⊥ →
    NativeSporadic.SporadicRep L ∨ EvenBNRankTwoType L ∨
      (LieModel L .PSp 3 2 1 ∨ LieModel L .PSU 6 2 1 ∨ LieModel L .POmegaMinus 4 2 1 ∨
        LieModel L .POmegaPlus 4 2 1)

@[expose] def BNRankTwoCenterStatement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G], (∃ a b : G, a * b ≠ b * a) →
    CFSG.Assembly.KProper CFSG.Blueprint.Catalog G →
    ∀ L : Subgroup G, standardComponentIsStandard L →
    (∀ t : G, orderOf t = 2 →
      standardComponentOddCore (centralizer ({t} : Set G)) = ⊥) →
    ∀ S : Sylow 2 (centralizer (L : Set G)), IsCyclic (S : Subgroup (centralizer (L : Set G))) →
    EvenStandardType (L ⧸ center L) → ¬ EvenStandardException (L ⧸ center L) →
    EvenBNRankTwoType (L ⧸ center L) → Even (Nat.card (center L))

theorem suzukiEightExclusion : SuzukiEightExclusion :=
  fun _ _ _ _ hnonab _ hL S hS hcore hZ hmod =>
    SuzukiEightZStar.false_of_suzuki_eight_double_cover hnonab hL S hS hcore hZ hmod

variable {G : Type} [Group G]

theorem isPGroup_two_center [Finite G] {L : Subgroup G} (hL : standardComponentIsStandard L)
    (hcore : ∀ t : G, orderOf t = 2 →
      standardComponentOddCore (centralizer ({t} : Set G)) = ⊥) :
    IsPGroup 2 (center L) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨t, ht⟩ :=
    exists_prime_orderOf_dvd_card' (G := centralizer (L : Set G)) 2 (even_iff_two_dvd.1 hL.2.1)
  rw [← Subgroup.orderOf_coe] at ht
  exact corefree_standard_center_two_group hL t.2 ht (hcore _ ht)

theorem even_exceptional_two_multiplier_frontier [Finite G] [IsSimpleGroup G] (hnonab : ∃ a b : G, a * b ≠ b * a) {L : Subgroup G}
    (hL : standardComponentIsStandard L)
    (hcore : ∀ t : G, orderOf t = 2 →
      standardComponentOddCore (centralizer ({t} : Set G)) = ⊥)
    (S : Sylow 2 (centralizer (L : Set G)))
    (hS : IsCyclic (S : Subgroup (centralizer (L : Set G))))
    (hexc : ¬ EvenStandardException (L ⧸ center L)) (hlie : EvenLieType (L ⧸ center L))
    (hne : center L ≠ ⊥) :
    (Nat.card (center L) = 2 ∧ (LieModel (L ⧸ center L) .G2 0 2 2 ∨
        LieModel (L ⧸ center L) .F4 0 2 1 ∨ LieModel (L ⧸ center L) .twistedE6 0 2 1)) ∨
      (LieModel (L ⧸ center L) .PSp 3 2 1 ∨ LieModel (L ⧸ center L) .PSU 6 2 1 ∨
        LieModel (L ⧸ center L) .POmegaPlus 4 2 1) := by
  rcases EvenTwoMultiplier.even_exceptional_two_multiplier_cases hL S hS hexc hlie
      (isPGroup_two_center hL hcore) hne with h | h | ⟨h2, hm⟩
  · exact Or.inl h
  · exact Or.inr h
  · exact (suzukiEightExclusion G hnonab L hL S hS hcore h2 hm).elim

theorem even_standard_residual_of_frontiers (hSeitz : SeitzCenterlessStatement)
    (hBN : BNRankTwoCenterStatement)
    (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (hnonab : ∃ a b : G, a * b ≠ b * a)
    (hK : CFSG.Assembly.KProper CFSG.Blueprint.Catalog G)
    (L : Subgroup G) (hL : standardComponentIsStandard L)
    (hcore : ∀ t : G, orderOf t = 2 →
      standardComponentOddCore (centralizer ({t} : Set G)) = ⊥)
    (S : Sylow 2 (centralizer (L : Set G)))
    (hS : IsCyclic (S : Subgroup (centralizer (L : Set G))))
    (htype : EvenStandardType (L ⧸ center L))
    (hexc : ¬ EvenStandardException (L ⧸ center L)) :
    EvenStandardResidual L := by
  have hHe : ¬ NativeSporadic.IsSporadic (L ⧸ center L) .He := fun h =>
    hexc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))
  refine ⟨isPGroup_two_center hL hcore, ?_⟩
  rcases htype with hlie | hspor
  · by_cases hne : center L = ⊥
    ·
      let e : L ≃* L ⧸ center L :=
        QuotientGroup.quotientBot.symm.trans (QuotientGroup.quotientMulEquivOfEq hne.symm)
      rcases hSeitz G hnonab hK L hL hcore S hS (Or.inl hlie) hexc hne with
        ⟨s, ⟨e'⟩⟩ | ⟨t, n, f, hf, htn, hm⟩ | h | h | h | h
      · exact Or.inl ⟨⟨s, ⟨e.symm.trans e'⟩⟩, hHe⟩
      · exfalso
        have heven := hBN G hnonab hK L hL hcore S hS (Or.inl hlie) hexc
          ⟨t, n, f, hf, htn, CFSG.LieType.CurtisTits.lieModel_of_mulEquiv e hm⟩
        rw [hne, Subgroup.card_bot] at heven
        exact Nat.not_even_one heven
      · exact Or.inr (Or.inr (Or.inl (Or.inl (CFSG.LieType.CurtisTits.lieModel_of_mulEquiv e h))))
      · exact Or.inr (Or.inr (Or.inl (Or.inr (Or.inl
          (CFSG.LieType.CurtisTits.lieModel_of_mulEquiv e h)))))
      · exact Or.inr (Or.inr (Or.inr ⟨hne, h⟩))
      · exact Or.inr (Or.inr (Or.inl (Or.inr (Or.inr
          (CFSG.LieType.CurtisTits.lieModel_of_mulEquiv e h)))))
    ·
      rcases even_exceptional_two_multiplier_frontier hnonab hL hcore S hS
          hexc hlie hne with hb | hc
      · exact Or.inr (Or.inl hb)
      · exact Or.inr (Or.inr (Or.inl hc))
  · exact Or.inl ⟨hspor, hHe⟩

end CFSG.LocalAnalysis.ComponentInitial.EvenResidual

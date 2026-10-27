module

public import CFSG.Foundations.Basic
public import CFSG.LocalAnalysis.EvenSporadicStandard.Reduction

public section

namespace CFSG.EvenSporadicStandard.TwoHS

open Subgroup CFSG.Blueprint CFSG.Blueprint.NativeSporadic

structure IsHSCover (H : Type) [Group H] (E : Subgroup H) : Prop where
  normal : E.Normal
  index_dvd_two : E.index ∣ 2
  perfect : Group.IsPerfect E
  card_center : Nat.card (center E) = 2
  quotient : IsSporadic (E ⧸ center E) .HS
  centralizer_le : centralizer (E : Set H) ≤ E

structure IsF5Centralizer (H : Type) [Group H] (E : Subgroup H) : Prop extends IsHSCover H E where
  index_eq_two : E.index = 2
  exists_outer_involution : ∃ v : H, v ∉ E ∧ v ^ 2 = 1

@[expose] def SolomonTwoHSCentralizer : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G), CFSG.EvenSporadicStandard.StdHyp G L →
    Nat.card (center L) = 2 → IsSporadic (L ⧸ center L) .HS →
      ∀ S : Sylow 2 (centralizer (L : Set G)), Nat.card S = 2

@[expose] def HaradaCentralizerShape : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G], (∃ a b : G, a * b ≠ b * a) →
    ∀ t : G, orderOf t = 2 → ∀ E : Subgroup (centralizer ({t} : Set G)),
      IsHSCover (centralizer ({t} : Set G)) E → IsF5Centralizer (centralizer ({t} : Set G)) E

@[expose] def HaradaHNRecognition : Prop :=
  ∀ z₀ : Carrier .HN, orderOf z₀ = 2 →
    (∃ K : Subgroup (centralizer ({z₀} : Set (Carrier .HN))), CFSG.IsComponent K) →
    ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (z : G), orderOf z = 2 →
      Nonempty (centralizer ({z} : Set G) ≃* centralizer ({z₀} : Set (Carrier .HN))) →
        IsSporadic G .HN

@[expose] def HaradaHNRecognitionKP : Prop :=
  ∀ z₀ : Carrier .HN, orderOf z₀ = 2 →
    (∃ K : Subgroup (centralizer ({z₀} : Set (Carrier .HN))), CFSG.IsComponent K) →
    ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G],
      CFSG.Assembly.KProper CFSG.Blueprint.Catalog G → ∀ z : G, orderOf z = 2 →
      Nonempty (centralizer ({z} : Set G) ≃* centralizer ({z₀} : Set (Carrier .HN))) →
        IsSporadic G .HN

theorem haradaHNRecognitionKP_of_haradaHNRecognition (h : HaradaHNRecognition) :
    HaradaHNRecognitionKP :=
  fun z₀ hz₀ hK G _ _ _ _ z hz hc => h z₀ hz₀ hK G z hz hc

end CFSG.EvenSporadicStandard.TwoHS

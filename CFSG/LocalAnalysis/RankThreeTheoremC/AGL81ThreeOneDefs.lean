module

public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81NineThreeKFacts

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.Hyp111.ThreeOne

open CFSG.Open CFSG.AGLEmbedding CFSG.RankThreeCoreUniqueness.Helpers

@[expose] def IsSporPlanePair (s : TauCeti.SporadicName) (p : ℕ) : Prop :=
  (s = .M24 ∧ p = 3) ∨ (s = .J2 ∧ p = 3) ∨ (s = .J4 ∧ p = 3) ∨ (s = .He ∧ p = 3) ∨
    (s = .Ru ∧ p = 3) ∨ (s = .Co2 ∧ p = 5) ∨ (s = .Co3 ∧ p = 5) ∨ (s = .Th ∧ p = 5) ∨
    (s = .M ∧ p = 13)

@[expose] def KFactThreeOneSporPlane : Prop :=
  ∀ (s : TauCeti.SporadicName) (p : ℕ), IsSporPlanePair s p →
    ∀ (K : Type) [Group K] [Finite K], Nonempty (K ≃* (TauCeti.CFSGIndex.sporadic s).Group) →
      ∀ A : Subgroup K, IsElemAbelian p A → Nat.card A = p ^ 2 → GLBCore p 1 A = ⊤

@[expose] def OnThreeOneList (p : ℕ) (K : Type*) [Group K] : Prop :=
  ∃ i : TauCeti.CFSGIndex, IsThreeOneIndex p i ∧ Nonempty (K ≃* i.Group)

structure Hyp (p : ℕ) {G : Type} [Group G] [Finite G] (K : Subgroup G) (P : Sylow p G)
    (E : Subgroup G) : Prop where
  prime : p.Prime
  ne_two : p ≠ 2
  normal : K.Normal
  sup_eq_top : K ⊔ (P : Subgroup G) = ⊤
  quasi : CFSG.Open.IsQuasisimple K
  catalog : CatalogSimpleSections G
  core : primeComplementCore (G := K) p = ⊥
  E_le : E ≤ P
  elem : IsElemAbelian p E
  card_E : Nat.card E = p ^ 2

end CFSG.LocalAnalysis.RankThreeTheoremC.Hyp111.ThreeOne

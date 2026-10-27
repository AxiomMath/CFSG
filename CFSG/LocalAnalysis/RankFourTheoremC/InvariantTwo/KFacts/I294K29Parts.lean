module

public import CFSG.LocalAnalysis.RankFourTheoremC.InvariantTwo.KFacts.I294Alt
public import CFSG.LocalAnalysis.RankFourTheoremC.InvariantTwo.KFacts.I294Assembly

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC

open CFSG.Open CFSG.LocalAnalysis.RankThreeTheoremC Subgroup

@[expose] def KD29Spor : Prop :=
  ∀ (p : ℕ), p.Prime → 5 ≤ p → ∀ (X : Type) [Group X] [Finite X] (L : Subgroup X) [L.Normal],
    IsSimpleGroup L → (∃ a b : L, a * b ≠ b * a) → IsCatalogGroup L →
    (∃ s : TauCeti.SporadicName, Nonempty (L ≃* (TauCeti.CFSGIndex.sporadic s).Group)) →
    ¬ IsLinearOrUnitaryAt p L → centralizer (L : Set X) = ⊥ →
    3 ≤ CFSG.Open.pRank p (⊤ : Subgroup X) →
    (∃ x ∈ L, orderOf x = p ∧ CFSG.Open.pRank p (centralizer ({x} : Set X)) ≤ 2) →
    ∀ d ∈ L, d ≠ 1 → d ^ p = 1 →
      GLAPLayer p (centralizer ({d} : Set X)) = ⊥ ∧
      GLAPPrimeCoreOf p (centralizer ({d} : Set X)) = ⊥

@[expose] def KD29Cross : Prop :=
  ∀ (p : ℕ), p.Prime → 5 ≤ p → ∀ (X : Type) [Group X] [Finite X] (L : Subgroup X) [L.Normal],
    IsSimpleGroup L → (∃ a b : L, a * b ≠ b * a) → IsCatalogGroup L →
    (∃ d : TauCeti.ValidLieTypeIndex, d.1.characteristic ≠ p ∧
      Nonempty (L ≃* (TauCeti.CFSGIndex.lie d).Group)) →
    ¬ IsLinearOrUnitaryAt p L → centralizer (L : Set X) = ⊥ →
    3 ≤ CFSG.Open.pRank p (⊤ : Subgroup X) →
    (∃ x ∈ L, orderOf x = p ∧ CFSG.Open.pRank p (centralizer ({x} : Set X)) ≤ 2) →
    ∀ d ∈ L, d ≠ 1 → d ^ p = 1 →
      GLAPLayer p (centralizer ({d} : Set X)) = ⊥ ∧
      GLAPPrimeCoreOf p (centralizer ({d} : Set X)) = ⊥

@[expose] def KD29DefChar : Prop :=
  ∀ (p : ℕ), p.Prime → 5 ≤ p → ∀ (X : Type) [Group X] [Finite X] (L : Subgroup X) [L.Normal],
    IsSimpleGroup L → (∃ a b : L, a * b ≠ b * a) → IsCatalogGroup L →
    (∃ d : TauCeti.ValidLieTypeIndex, d.1.characteristic = p ∧
      Nonempty (L ≃* (TauCeti.CFSGIndex.lie d).Group)) →
    ¬ IsLinearOrUnitaryAt p L → centralizer (L : Set X) = ⊥ →
    3 ≤ CFSG.Open.pRank p (⊤ : Subgroup X) →
    (∃ x ∈ L, orderOf x = p ∧ CFSG.Open.pRank p (centralizer ({x} : Set X)) ≤ 2) →
    ∀ d ∈ L, d ≠ 1 → d ^ p = 1 →
      GLAPLayer p (centralizer ({d} : Set X)) = ⊥ ∧
      GLAPPrimeCoreOf p (centralizer ({d} : Set X)) = ⊥

theorem kd29Inner_of_parts (hS : KD29Spor) (hC : KD29Cross) (hD : KD29DefChar) : KD29Inner := by
  intro p hp hp5 X _ _ L _ hs hn hc hl hcen hrank hex d hd hd1 hdp
  obtain ⟨i, ⟨e⟩⟩ := id hc
  cases i with
  | cyclic r hr =>
    exfalso
    obtain ⟨a, b, hab⟩ := hn
    exact hab (e.injective (by rw [map_mul, map_mul]; exact mul_comm _ _))
  | alternating n hn5 =>
    exact kd29Alt_holds p hp hp5 X L hs hn hc ⟨n, hn5, ⟨e⟩⟩ hl hcen hrank hex d hd hd1 hdp
  | sporadic s =>
    exact hS p hp hp5 X L hs hn hc ⟨s, ⟨e⟩⟩ hl hcen hrank hex d hd hd1 hdp
  | lie m =>
    by_cases hch : m.1.characteristic = p
    · exact hD p hp hp5 X L hs hn hc ⟨m, hch, ⟨e⟩⟩ hl hcen hrank hex d hd hd1 hdp
    · exact hC p hp hp5 X L hs hn hc ⟨m, hch, ⟨e⟩⟩ hl hcen hrank hex d hd hd1 hdp

end CFSG.LocalAnalysis.RankFourTheoremC

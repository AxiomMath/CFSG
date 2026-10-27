module

public import CFSG.LocalAnalysis.RankThreeTheoremC.D2PairStrong3Irr
public import CFSG.LocalAnalysis.AGLEmbeddingD2.U3Data
public import CFSG.LocalAnalysis.AGLEmbeddingD2.L2Data

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open CFSG.AGLEmbedding CFSG.AGLEmbeddingD2
open CFSG.RankThreeCoreUniqueness.Helpers (primeComplementCore)

@[expose] def AutomizerIrreducible {X : Type*} [Group X] (p : ℕ) (R X₀ : Subgroup X) : Prop :=
  ∀ Y : Subgroup X, Y ≤ R → Nat.card Y = p →
    ∃ t ∈ X₀ ⊓ Subgroup.normalizer (R : Set X), t ∉ Subgroup.normalizer (Y : Set X)

@[expose] def D2AutomizerAt (i : TauCeti.CFSGIndex) (Pp : ℕ → Prop) : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (p : ℕ), Pp p → ∀ (R : Sylow p X) (A X₀ K : Subgroup X),
    D2AlmostSimple p X R A X₀ K → Nonempty (K ≃* i.Group) →
      AutomizerIrreducible p (R : Subgroup X) X₀

@[expose] def D2SylowNineAt (i : TauCeti.CFSGIndex) (Pp : ℕ → Prop) : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (p : ℕ), Pp p → ∀ (R : Sylow p X) (A X₀ K : Subgroup X),
    D2AlmostSimple p X R A X₀ K → Nonempty (K ≃* i.Group) → Nat.card (R : Subgroup X) = p ^ 2

variable {G : Type} [Group G] [Finite G] {P : Sylow 3 G} {M A H R : Subgroup G}

theorem _root_.CFSG.AGLEmbeddingD2.D2Escape.irreducibleOn_of_automizer
    (h : D2Escape 3 P M A H R) (hR9 : Nat.card R = 9)
    (hX : AutomizerIrreducible 3
      ((R.subgroupOf H).map (QuotientGroup.mk' (primeComplementCore (G := H) 3)))
      (((H ⊓ M).subgroupOf H).map (QuotientGroup.mk' (primeComplementCore (G := H) 3)))) :
    IrreducibleOn (H ⊓ M ⊓ Subgroup.normalizer (R : Set G)) R := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  intro W hWR hWN
  by_contra hne
  rw [not_or] at hne
  obtain ⟨hW1, hWR'⟩ := hne
  have hWH : W ≤ H := hWR.trans h.le_H
  have hWdvd : Nat.card W ∣ 3 ^ 2 := by
    have := Subgroup.card_dvd_of_le hWR
    rwa [hR9, show (9 : ℕ) = 3 ^ 2 by norm_num] at this
  have hW3 : Nat.card W = 3 := by
    obtain ⟨k, hk, hkW⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp hWdvd
    interval_cases k
    · exact absurd (Subgroup.eq_bot_of_card_eq W (by simpa using hkW)) hW1
    · simpa using hkW
    · exact absurd (Subgroup.eq_of_le_of_card_ge hWR (by rw [hR9, hkW]; norm_num)) hWR'
  set π := QuotientGroup.mk' (primeComplementCore (G := H) 3) with hπ
  set Y : Subgroup (H ⧸ primeComplementCore (G := H) 3) := (W.subgroupOf H).map π with hY
  have hYR : Y ≤ (R.subgroupOf H).map π :=
    Subgroup.map_mono (Subgroup.subgroupOf_mono H hWR)
  have hY3 : Nat.card Y = 3 := (h.card_map_eq hWR).trans hW3
  obtain ⟨t, ht, htY⟩ := hX Y hYR hY3
  obtain ⟨s, hsM, hsN, hst⟩ := h.exists_lift_normalizer ht.1 ht.2
  have hsW : (s : G) ∈ Subgroup.normalizer (W : Set G) := hWN ⟨⟨s.2, hsM⟩, hsN⟩
  have hsW' : s ∈ Subgroup.normalizer ((W.subgroupOf H : Subgroup H) : Set H) := by
    rw [← Subgroup.subgroupOf_normalizer_eq hWH]
    exact hsW
  apply htY
  rw [← hst]
  exact Subgroup.le_normalizer_map π ⟨s, hsW', rfl⟩

end CFSG.LocalAnalysis.RankThreeTheoremC

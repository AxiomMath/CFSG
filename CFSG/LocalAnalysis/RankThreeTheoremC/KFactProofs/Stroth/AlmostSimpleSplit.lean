module

public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimpleRankOne

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimple

open CFSG CFSG.Open Subgroup CFSG.LocalAnalysis.RankThreeTheoremC
open CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData (IsChevTwo)

@[expose] def AlmostSimplePartA : Prop :=
  ∀ (p : ℕ), p.Prime → p ≠ 2 → ∀ (X : Type) [Group X] [Finite X] (L : Subgroup X) [L.Normal],
    IsSimpleGroup L → (∃ a b : L, a * b ≠ b * a) → IsCatalogGroup L →
    (¬ ∃ n : ℕ, Nonempty (L ≃* alternatingGroup (Fin n))) →
    Subgroup.centralizer (L : Set X) = ⊥ →
    (∀ E : Subgroup X, IsElemAbelian p E → Nat.card E ≤ p ^ 2) →
      ∀ P : Sylow p (X ⧸ L), (P : Subgroup (X ⧸ L)).Normal

@[expose] def AlmostSimplePartB : Prop :=
  ∀ (p : ℕ), p.Prime → p ≠ 2 → ∀ (X : Type) [Group X] [Finite X] (L : Subgroup X) [L.Normal],
    IsSimpleGroup L → (∃ a b : L, a * b ≠ b * a) → IsCatalogGroup L →
    (¬ ∃ n : ℕ, Nonempty (L ≃* alternatingGroup (Fin n))) →
    Subgroup.centralizer (L : Set X) = ⊥ →
    (∀ E : Subgroup X, IsElemAbelian p E → Nat.card E ≤ p ^ 2) →
      IsChevTwo L → ∀ D : Subgroup X, ThompsonFrame p D → NormalizerExponent p D →
        p ∣ Nat.card (invariantTwoJoinIn D L) → False

@[expose] def AlmostSimplePartBRankTwo : Prop :=
  ∀ (p : ℕ), p.Prime → p ≠ 2 → ∀ (X : Type) [Group X] [Finite X] (L : Subgroup X) [L.Normal],
    IsSimpleGroup L → (∃ a b : L, a * b ≠ b * a) → IsCatalogGroup L →
    (¬ ∃ n : ℕ, Nonempty (L ≃* alternatingGroup (Fin n))) →
    Subgroup.centralizer (L : Set X) = ⊥ →
    (∀ E : Subgroup X, IsElemAbelian p E → Nat.card E ≤ p ^ 2) →
    CFSG.Open.pRank p (⊤ : Subgroup L) = 2 →
      IsChevTwo L → ∀ D : Subgroup X, ThompsonFrame p D → NormalizerExponent p D →
        p ∣ Nat.card (invariantTwoJoinIn D L) → False

theorem kFactAlmostSimpleRankTwo_of_parts (ha : AlmostSimplePartA) (hb : AlmostSimplePartB) :
    KFactAlmostSimpleRankTwo := by
  unfold KFactAlmostSimpleRankTwo
  intro p hp hp2 X _ _ L _ hs hnab hcat hnalt hC hE
  exact ⟨ha p hp hp2 X L hs hnab hcat hnalt hC hE, hb p hp hp2 X L hs hnab hcat hnalt hC hE⟩

section Certificates


theorem almostSimplePartB_of_rankTwo (h : AlmostSimplePartBRankTwo) : AlmostSimplePartB := by
  unfold AlmostSimplePartB
  intro p hp hp2 X _ _ L _ hs hnab hcat hnalt hC hE hchev D hF hexp hjoin
  have hp1 : 1 < p := hp.one_lt
  have hX : CFSG.Open.pRank p (⊤ : Subgroup X) ≤ 2 := by
    unfold CFSG.Open.pRank
    refine csSup_le' ?_
    intro k hk
    obtain ⟨E, -, hEel, hcard⟩ := hk
    have hb := hE E hEel
    rw [hcard] at hb
    exact (pow_le_pow_iff_right₀ hp1).mp hb
  have hrank : CFSG.Open.pRank p (⊤ : Subgroup L) ≤ 2 :=
    (CFSG.SectionRank.pRank_top_le_of_injective hp1 L.subtype L.subtype_injective).trans hX
  rcases Nat.lt_or_ge (CFSG.Open.pRank p (⊤ : Subgroup L)) 2 with hlt | hge
  · exact false_of_pRank_le_one hs hnab hcat hC hF hexp (by omega)
  · exact h p hp hp2 X L hs hnab hcat hnalt hC hE (le_antisymm hrank hge) hchev D hF hexp hjoin

end Certificates

end CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimple

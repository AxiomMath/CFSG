module

public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83SmallRank614ExtDefs

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers Subgroup

variable {G : Type} [Group G] [Finite G]

theorem exists_isMaxTwoInvariantIn_of_le {B X S : Subgroup G} (h : IsTwoInvariantIn B X S) :
    ∃ S' : Subgroup G, S ≤ S' ∧ IsMaxTwoInvariantIn B X S' := by
  obtain ⟨S', hle, hmax⟩ := Finite.exists_le_maximal (p := IsTwoInvariantIn B X) h
  exact ⟨S', hle, hmax.1, fun T hT hST => le_antisymm (hmax.2 hT hST) hST⟩

omit [Finite G] in
private theorem prop614Better_iff_lt (H' S' H S : Subgroup G) :
    Prop614Better H' S' H S ↔
      toLex (Nat.card S, toLex (Nat.card (pCoreOf 2 H), Nat.card H)) <
        toLex (Nat.card S', toLex (Nat.card (pCoreOf 2 H'), Nat.card H')) := by
  simp only [Prop614Better, Prod.Lex.toLex_lt_toLex]

theorem exists_prop614Extremal {M B : Subgroup G}
    (h : ∃ H S : Subgroup G, Prop614Pair M B H S) :
    ∃ H S : Subgroup G, Prop614Extremal M B H S := by
  obtain ⟨H, S, hHS⟩ := h
  obtain ⟨q, hq, hmax⟩ := Set.Finite.exists_maximalFor
    (fun q : Subgroup G × Subgroup G =>
      toLex (Nat.card q.2, toLex (Nat.card (pCoreOf 2 q.1), Nat.card q.1)))
    {q : Subgroup G × Subgroup G | Prop614Pair M B q.1 q.2} (Set.toFinite _) ⟨(H, S), hHS⟩
  refine ⟨q.1, q.2, hq, fun H' S' hpair hbetter => ?_⟩
  have hlt := (prop614Better_iff_lt H' S' q.1 q.2).mp hbetter
  exact (hmax (j := (H', S')) hpair hlt.le).not_gt hlt

theorem Prop614Extremal.eq_normalizer_pCoreOf {M B H S : Subgroup G}
    (h : Prop614Extremal M B H S) : H = normalizer (pCoreOf 2 H : Set G) := by
  have hHH' : H ≤ normalizer (pCoreOf 2 H : Set G) := localGroup_le_normalizer_pCoreOf 2 H
  obtain ⟨⟨hSle, hSp, hBS⟩, -⟩ := h.pair.isMax
  obtain ⟨S', hSS', hS'max⟩ := exists_isMaxTwoInvariantIn_of_le
    (X := normalizer (pCoreOf 2 H : Set G) ⊓ M) ⟨hSle.trans (inf_le_inf_right M hHH'), hSp, hBS⟩
  have hpair : Prop614Pair M B (normalizer (pCoreOf 2 H : Set G)) S' :=
    ⟨normalizer_pCoreOf_isTwoLocal H h.pair.isTwoLocal, h.pair.le.trans hHH',
      fun hle => h.pair.not_le (hHH'.trans hle), hS'max,
      fun hbot => h.pair.ne_bot (le_bot_iff.mp (hbot ▸ hSS'))⟩
  have hnot := h.max _ _ hpair
  have h1 : Nat.card S ≤ Nat.card S' := card_le_of_le hSS'
  have h2 : Nat.card (pCoreOf 2 H) ≤ Nat.card (pCoreOf 2 (normalizer (pCoreOf 2 H : Set G))) :=
    card_le_of_le (twoLocal_witness_le_pCoreOf _ _ (pCoreOf_isPGroup 2 H) rfl)
  have h3 : Nat.card (normalizer (pCoreOf 2 H : Set G)) ≤ Nat.card H := by
    unfold Prop614Better at hnot
    omega
  exact eq_of_le_of_card_ge hHH' h3

set_option linter.unusedSectionVars false in
theorem pCoreOf_le_of_isMaxTwoInvariantIn {B H S : Subgroup G} (hBH : B ≤ H)
    (h : IsMaxTwoInvariantIn B H S) : pCoreOf 2 H ≤ S := by
  obtain ⟨⟨hSH, hSp, hBS⟩, hmax⟩ := h
  have hN := localGroup_le_normalizer_pCoreOf 2 H
  have hT : IsTwoInvariantIn B H (S ⊔ pCoreOf 2 H) :=
    ⟨sup_le hSH (pCoreOf_le 2 H),
      IsPGroup.to_sup_of_normal_right' hSp (pCoreOf_isPGroup 2 H) (hSH.trans hN),
      (le_inf hBS (hBH.trans hN)).trans (inf_normalizer_le_normalizer_sup _ _)⟩
  exact le_sup_right.trans (hmax _ hT le_sup_left).le

theorem Prop614Extremal.normalizer_le_of_pCoreOf_lt {M B H S : Subgroup G}
    (h : Prop614Extremal M B H S) {S₀ : Subgroup G} (h1 : pCoreOf 2 H < S₀) (h2 : S₀ ≤ S)
    (h3 : S ⊔ B ≤ normalizer (S₀ : Set G)) : normalizer (S₀ : Set G) ≤ M := by
  by_contra hnle
  obtain ⟨⟨hSle, hSp, hBS⟩, -⟩ := h.pair.isMax
  have hS₀p : IsPGroup 2 S₀ := hSp.to_le h2
  obtain ⟨S₁, hSS₁, hS₁max⟩ := exists_isMaxTwoInvariantIn_of_le
    (X := normalizer (S₀ : Set G) ⊓ M)
    ⟨le_inf (le_sup_left.trans h3) (hSle.trans inf_le_right), hSp, hBS⟩
  have hpair : Prop614Pair M B (normalizer (S₀ : Set G)) S₁ :=
    ⟨⟨S₀, ne_bot_of_gt h1, hS₀p, rfl⟩, le_sup_right.trans h3, hnle, hS₁max,
      fun hbot => h.pair.ne_bot (le_bot_iff.mp (hbot ▸ hSS₁))⟩
  apply h.max _ _ hpair
  have hc1 : Nat.card S ≤ Nat.card S₁ := card_le_of_le hSS₁
  have hc2 : Nat.card (pCoreOf 2 H) < Nat.card S₀ := card_lt_of_lt h1
  have hc3 : Nat.card S₀ ≤ Nat.card (pCoreOf 2 (normalizer (S₀ : Set G))) :=
    card_le_of_le (twoLocal_witness_le_pCoreOf S₀ _ hS₀p rfl)
  unfold Prop614Better
  omega

end CFSG.LocalAnalysis.RankThreeTheoremC

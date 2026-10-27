module

public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesKD291G2RankPat

public noncomputable section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.KD291DC.G2Rank

section Chain

variable {G : Type*} [Group G]

theorem chain_step (E V W : Subgroup G) {q : ℕ} (hq : 0 < q) (hWV : W ≤ V)
    (hcard : Nat.card V = q * Nat.card W) (hpos : 0 < Nat.card W) :
    ∃ n : ℕ, n ≤ 1 ∧ (n = 1 → ¬ E ⊓ V ≤ W) ∧
      Nat.card ↥(E ⊓ V) ≤ q ^ n * Nat.card ↥(E ⊓ W) := by
  have hB : W ⊓ (E ⊓ V) = E ⊓ W := by
    ext x
    simp only [Subgroup.mem_inf]
    exact ⟨fun ⟨a, b, _⟩ => ⟨b, a⟩, fun ⟨a, b⟩ => ⟨b, a, hWV b⟩⟩
  have h1 := Subgroup.relIndex_mul_card (H := W) (K := E ⊓ V)
  have h2 := Subgroup.relIndex_mul_card (H := W) (K := V)
  rw [inf_eq_left.2 hWV] at h2
  rw [hB] at h1
  have hrel : W.relIndex V = q := by
    have h3 : W.relIndex V * Nat.card W = q * Nat.card W := by rw [h2, hcard]
    exact Nat.eq_of_mul_eq_mul_right hpos h3
  have h3 : W.relIndex (E ⊓ V) ≤ q := by
    rw [← hrel]
    exact Subgroup.relIndex_le_of_le_right inf_le_right (by rw [hrel]; exact hq.ne')
  by_cases hle : E ⊓ V ≤ W
  · refine ⟨0, by norm_num, fun h => absurd h (by norm_num), ?_⟩
    have h4 : W.relIndex (E ⊓ V) = 1 := Subgroup.relIndex_eq_one.2 hle
    rw [h4, one_mul] at h1
    rw [← h1, pow_zero, one_mul]
  · refine ⟨1, le_rfl, fun _ => hle, ?_⟩
    rw [pow_one, ← h1]
    exact Nat.mul_le_mul_right _ h3

end Chain

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.KD291DC.G2Rank

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.KD291DC.G2Rank

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.GH74.GLS.IVK.Proofs2.Ivk47
open scoped commutatorElement


section Main

variable {F : Type} [Field F]

theorem card_le_cube [Finite F] (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0)
    (E : Subgroup (ModGL .G2 F)) (hE : E ≤ heightSeries .G2 F 1)
    (hcomm : ∀ x ∈ E, ∀ y ∈ E, ⁅x, y⁆ = 1) : Nat.card E ≤ Nat.card F ^ 3 := by
  have hqpos : 0 < Nat.card F := Nat.card_pos
  have hqp : ∀ k : ℕ, 0 < Nat.card F ^ k := fun k => pow_pos hqpos k
  obtain ⟨n1, hn1, hB1, hc1⟩ := chain_step E (heightSeries .G2 F 1) (Wg F) hqpos Wg_le_hs_one
    (by rw [card_hs_one, card_Wg, pow_succ']) (by rw [card_Wg]; exact hqp 5)
  obtain ⟨n2, hn2, hB2, hc2⟩ := chain_step E (Wg F) (heightSeries .G2 F 2) hqpos hs_two_le_Wg
    (by rw [card_Wg, card_hs_two, pow_succ']) (by rw [card_hs_two]; exact hqp 4)
  obtain ⟨n3, hn3, hB3, hc3⟩ := chain_step E (heightSeries .G2 F 2) (heightSeries .G2 F 3) hqpos
    (hs_mono (by norm_num)) (by rw [card_hs_two, card_hs_three, pow_succ'])
    (by rw [card_hs_three]; exact hqp 3)
  obtain ⟨n4, hn4, hB4, hc4⟩ := chain_step E (heightSeries .G2 F 3) (heightSeries .G2 F 4) hqpos
    (hs_mono (by norm_num)) (by rw [card_hs_three, card_hs_four, pow_succ'])
    (by rw [card_hs_four]; exact hqp 2)
  obtain ⟨n5, hn5, hB5, hc5⟩ := chain_step E (heightSeries .G2 F 4) (heightSeries .G2 F 5) hqpos
    (hs_mono (by norm_num)) (by rw [card_hs_four, card_hs_five, pow_two])
    (by rw [card_hs_five]; exact hqpos)
  obtain ⟨n6, hn6, hB6, hc6⟩ := chain_step E (heightSeries .G2 F 5) ⊥ hqpos bot_le
    (by rw [card_hs_five, Subgroup.card_bot, mul_one]) (by rw [Subgroup.card_bot]; exact one_pos)
  have pA : ¬ (n1 = 1 ∧ n2 = 1) := by
    rintro ⟨e1, e2⟩
    obtain ⟨f, hf, hfn⟩ := SetLike.not_le_iff_exists.1 (hB1 e1)
    obtain ⟨g, hg, hgn⟩ := SetLike.not_le_iff_exists.1 (hB2 e2)
    exact patA hf.2 hfn hg.2 hgn (hcomm g hg.1 f hf.1)
  have pB : ¬ (n3 = 1 ∧ n4 = 1) := by
    rintro ⟨e3, e4⟩
    obtain ⟨x, hx, hxn⟩ := SetLike.not_le_iff_exists.1 (hB3 e3)
    obtain ⟨y, hy, hyn⟩ := SetLike.not_le_iff_exists.1 (hB4 e4)
    exact patB h3 hx.2 hxn hy.2 hyn (hcomm x hx.1 y hy.1)
  have pC : ¬ ((n1 = 1 ∨ n2 = 1) ∧ n5 = 1 ∧ (n3 = 1 ∨ n4 = 1)) := by
    rintro ⟨hf12, e5, he34⟩
    obtain ⟨f, hf1, hf, hfn⟩ : ∃ f : ModGL .G2 F, f ∈ E ∧ f ∈ heightSeries .G2 F 1 ∧
        f ∉ heightSeries .G2 F 2 := by
      rcases hf12 with e1 | e2
      · obtain ⟨f, hf, hfn⟩ := SetLike.not_le_iff_exists.1 (hB1 e1)
        exact ⟨f, hf.1, hf.2, fun h => hfn (hs_two_le_Wg h)⟩
      · obtain ⟨g, hg, hgn⟩ := SetLike.not_le_iff_exists.1 (hB2 e2)
        exact ⟨g, hg.1, Wg_le_hs_one hg.2, hgn⟩
    obtain ⟨z, hz, hzn⟩ := SetLike.not_le_iff_exists.1 (hB5 e5)
    rcases he34 with e3 | e4
    · obtain ⟨x, hx, hxn⟩ := SetLike.not_le_iff_exists.1 (hB3 e3)
      exact patC h2 h3 hf hfn hz.2 hzn (Or.inl ⟨hx.2, hxn⟩) (hcomm f hf1 z hz.1)
        (hcomm f hf1 x hx.1)
    · obtain ⟨y, hy, hyn⟩ := SetLike.not_le_iff_exists.1 (hB4 e4)
      exact patC h2 h3 hf hfn hz.2 hzn (Or.inr ⟨hy.2, hyn⟩) (hcomm f hf1 z hz.1)
        (hcomm f hf1 y hy.1)
  have hsum : n1 + n2 + n3 + n4 + n5 + n6 ≤ 3 := by omega
  have e1 : E ⊓ heightSeries .G2 F 1 = E := inf_of_le_left hE
  have e7 : Nat.card ↥(E ⊓ (⊥ : Subgroup (ModGL .G2 F))) = 1 := by
    rw [inf_bot_eq, Subgroup.card_bot]
  rw [e1] at hc1
  rw [e7] at hc6
  have hq1 : 1 ≤ Nat.card F := hqpos
  calc Nat.card E ≤ Nat.card F ^ n1 * Nat.card ↥(E ⊓ Wg F) := hc1
    _ ≤ Nat.card F ^ n1 * (Nat.card F ^ n2 * Nat.card ↥(E ⊓ heightSeries .G2 F 2)) :=
        Nat.mul_le_mul_left _ hc2
    _ ≤ Nat.card F ^ n1 * (Nat.card F ^ n2 * (Nat.card F ^ n3 *
          Nat.card ↥(E ⊓ heightSeries .G2 F 3))) :=
        Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ hc3)
    _ ≤ Nat.card F ^ n1 * (Nat.card F ^ n2 * (Nat.card F ^ n3 * (Nat.card F ^ n4 *
          Nat.card ↥(E ⊓ heightSeries .G2 F 4)))) :=
        Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ hc4))
    _ ≤ Nat.card F ^ n1 * (Nat.card F ^ n2 * (Nat.card F ^ n3 * (Nat.card F ^ n4 *
          (Nat.card F ^ n5 * Nat.card ↥(E ⊓ heightSeries .G2 F 5))))) :=
        Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _
          (Nat.mul_le_mul_left _ hc5)))
    _ ≤ Nat.card F ^ n1 * (Nat.card F ^ n2 * (Nat.card F ^ n3 * (Nat.card F ^ n4 *
          (Nat.card F ^ n5 * (Nat.card F ^ n6 * 1))))) :=
        Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _
          (Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ hc6))))
    _ = Nat.card F ^ (n1 + n2 + n3 + n4 + n5 + n6) := by ring
    _ ≤ Nat.card F ^ 3 := Nat.pow_le_pow_right hqpos hsum

end Main

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.KD291DC.G2Rank

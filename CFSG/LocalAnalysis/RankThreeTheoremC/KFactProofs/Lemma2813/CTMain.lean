module

public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Lemma2813.Counting
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Lemma2813.Inequalities
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Lemma2813.SmallCases
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Lemma2813.Case64

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Lemma2813

section
open CFSG.Open Subgroup CFSG.QuasithinUnique.Setup.Family
variable {M : Type} [AddCommGroup M] [Finite M] [DistribMulAction GL32 M]

theorem ct_classify {p₀ : V3} {d : GL32} (h : CTHyp M p₀ d) :
    (Nat.card M = 8 ∧ Nat.card (fixSub M (Spt p₀)) = 2) ∨
    (Nat.card M = 8 ∧ Nat.card (fixSub M (Spt p₀)) = 4 ∧ Ncnt M 1 = 0) ∨
    (Nat.card M = 16 ∧ Nat.card (fixSub M (Spt p₀)) = 4 ∧ Ncnt M 1 = 0) ∨
    (Nat.card M = 64 ∧ Nat.card (fixSub M (Spt p₀)) = 16 ∧
      (∀ p q : V3, p ≠ 0 → q ≠ 0 → p ≠ q → Nat.card (fixSub M (Spt p ⊔ Spt q)) = 4) ∧
      Ncnt M 0 = 0) := by
  classical
  obtain ⟨q₀, hq₀, hq₀p⟩ : ∃ q : V3, q ≠ 0 ∧ q ≠ p₀ := by
    by_cases h1 : p₀ = Pi.single 0 1
    · refine ⟨Pi.single 1 1, ?_, ?_⟩ <;> simp [h1, Pi.single_apply, funext_iff, Fin.forall_fin_succ]
    · exact ⟨Pi.single 0 1, by simp [funext_iff, Fin.forall_fin_succ], fun h => h1 h.symm⟩
  have hM0 := h.fixed
  have hp₀ := h.hp₀
  have hC1 := Ncnt_total (M := M) hM0
  have hC2 := Ncnt_points (M := M) hM0 hp₀
  have hC3 := Ncnt_pairs (M := M) hM0 hp₀ hq₀ (Ne.symm hq₀p)
  have hsq := card_fixSub_Spt_sq (M := M) hp₀ hq₀ (Ne.symm hq₀p)
  have hcube := card_fixSub_Spt_cube (M := M) hM0 hp₀
  have hlt := card_fixSub_Spt_lt (M := M) hM0 h.ne hp₀
  have hS2 : IsPGroup 2 (Spt p₀) := by
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    exact IsPGroup.of_card (n := 2) (by rw [Spt_card hp₀]; norm_num)
  have ha2 : 2 ≤ Nat.card (fixSub M (Spt p₀)) := by
    have hd2 := two_dvd_card_fixSub (M := M) h.two h.ne hS2
    have hpos : 0 < Nat.card (fixSub M (Spt p₀)) := Nat.card_pos
    exact Nat.le_of_dvd hpos hd2
  have hn2 : ∃ k, Nat.card M = 2 ^ k := by
    obtain ⟨k, hk⟩ := card_addSubgroup_pow_two (M := M) h.two ⊤
    exact ⟨k, by rw [← hk]; exact (Nat.card_congr (AddSubgroup.topEquiv).toEquiv).symm⟩
  obtain ⟨ka, hka⟩ := card_addSubgroup_pow_two (M := M) h.two (fixSub M (Spt p₀))
  obtain ⟨kb, hkb⟩ := card_addSubgroup_pow_two (M := M) h.two (fixSub M (Spt p₀ ⊔ Spt q₀))
  have hmain := ct_arith (Nat.card M) (Nat.card (fixSub M (Spt p₀)))
    (Nat.card (fixSub M (Spt p₀ ⊔ Spt q₀))) hn2 ⟨ka, hka⟩ ⟨kb, hkb⟩ ha2 hlt h.off hcube
    (by omega) (by omega) hsq
  rcases hmain with ⟨hn, ha, hb⟩ | ⟨hn, ha, hb⟩ | ⟨hn, ha, hb⟩ | ⟨hn, ha, hb⟩
  · left
    exact ⟨hn, ha⟩
  · right; left
    exact ⟨hn, ha, by omega⟩
  · right; right; left
    exact ⟨hn, ha, by omega⟩
  · right; right; right
    refine ⟨hn, ha, fun p q hp hq hpq => ?_, by omega⟩
    rw [card_fixSub_pair (M := M) hp hq hp₀ hq₀ hpq (Ne.symm hq₀p), hb]

theorem ct_main {p₀ : V3} {d : GL32} (h : CTHyp M p₀ d) : CTConcl M p₀ d := by
  rcases ct_classify h with ⟨hn, ha⟩ | ⟨hn, ha, hN⟩ | ⟨hn, ha, hN⟩ | ⟨hn, ha, hb, hN⟩
  · exact ct_case_8_2 h hn ha
  · exact ct_case_N1 h (by omega) hN
  · exact ct_case_N1 h (by omega) hN
  · exact ct_case_64 h hn ha hb hN
end

end CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Lemma2813

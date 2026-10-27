module

public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Lemma2813.PsetStructure
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Lemma2813.OrderThree

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Lemma2813

open CFSG.Open Subgroup CFSG.QuasithinUnique.Setup.Family

section CT

variable {M : Type} [AddCommGroup M] [Finite M] [DistribMulAction GL32 M]

theorem sc_CTConcl_intro {p₀ : V3} {d : GL32}
    (h1 : Nat.card (commSub M (zpowers d)) ≤ 16)
    (h2 : Nat.card (fixSub M (Spt p₀ ⊔ zpowers d)) ≤ 2)
    (h3 : (∃ m ∈ fixSub M (Spt p₀), d • m ≠ m) → fixSub M (Spt p₀ ⊔ zpowers d) = ⊥) :
    CTConcl M p₀ d := by
  unfold CTConcl
  exact ⟨h1, h2, h3⟩

theorem sc_Ncnt_pos {k : ℕ} {w : M} (hw : w ≠ 0) (hk : (Pset M w).card = k) :
    0 < Ncnt M k := by
  unfold Ncnt
  haveI : Nonempty {w : M // w ≠ 0 ∧ (Pset M w).card = k} := ⟨⟨w, hw, hk⟩⟩
  exact Nat.card_pos

theorem sc_card_commSub_le (hn : Nat.card M ≤ 16) (H : Subgroup GL32) :
    Nat.card (commSub M H) ≤ 16 :=
  le_trans (Nat.card_le_card_of_injective _ Subtype.val_injective) hn

theorem ct_case_8_2 {p₀ : V3} {d : GL32} (h : CTHyp M p₀ d) (hn : Nat.card M = 8)
    (ha : Nat.card (fixSub M (Spt p₀)) = 2) : CTConcl M p₀ d := by
  refine sc_CTConcl_intro (sc_card_commSub_le (by omega) _) ?_ ?_
  · have hle : fixSub M (Spt p₀ ⊔ zpowers d) ≤ fixSub M (Spt p₀) := fixSub_mono le_sup_left
    exact (AddSubgroup.card_le_of_le hle).trans ha.le
  · rintro ⟨m, hm, hdm⟩
    exfalso
    have hm0 : m ≠ 0 := by
      rintro rfl
      exact hdm (smul_zero d)
    have hdm' : d • m ∈ fixSub M (Spt p₀) := smul_mem_fixSub_Spt h.hdp hm
    have hdm0 : d • m ≠ 0 := by
      intro h0
      apply hm0
      have h1 := congrArg (fun z => d⁻¹ • z) h0
      simpa using h1
    obtain ⟨y, -, hy⟩ := (Nat.card_eq_two_iff' (0 : fixSub M (Spt p₀))).1 ha
    have e1 : (⟨m, hm⟩ : fixSub M (Spt p₀)) = y :=
      hy _ (fun h0 => hm0 (congrArg Subtype.val h0))
    have e2 : (⟨d • m, hdm'⟩ : fixSub M (Spt p₀)) = y :=
      hy _ (fun h0 => hdm0 (congrArg Subtype.val h0))
    exact hdm (congrArg Subtype.val (e2.trans e1.symm))

theorem ct_case_N1 {p₀ : V3} {d : GL32} (h : CTHyp M p₀ d) (hn : Nat.card M ≤ 16)
    (hN : Ncnt M 1 = 0) : CTConcl M p₀ d := by
  have hbot : fixSub M (Spt p₀ ⊔ zpowers d) = ⊥ := by
    rw [AddSubgroup.eq_bot_iff_forall]
    intro w hw
    by_contra hw0
    rw [fixSub_sup] at hw
    obtain ⟨hw1, hw2⟩ := hw
    have hdw : d • w = w := mem_fixSub_zpowers.1 hw2
    have hp₀w : p₀ ∈ Pset M w := mem_Pset.2 ⟨h.hp₀, hw1⟩
    rcases Pset_card_cases h.fixed hw0 with hc | hc | ⟨x, y, hx, hy, hxy, hP⟩
    · exact absurd (Finset.card_pos.2 ⟨p₀, hp₀w⟩) (by omega)
    · have hpos := sc_Ncnt_pos hw0 hc
      omega
    · have hinv : ∀ z : V3, z ∈ Pset M w → act d z ∈ Pset M w := by
        intro z hz
        have h1 := Pset_smul d w (act d z)
        rw [hdw, act_inv_act] at h1
        exact h1.2 hz
      have hxm : x ∈ Pset M w := by rw [hP]; simp
      have hym : y ∈ Pset M w := by rw [hP]; simp
      have h1 : act d x ∈ ({x, y, x + y} : Finset V3) := by rw [← hP]; exact hinv x hxm
      have h2 : act d y ∈ ({x, y, x + y} : Finset V3) := by rw [← hP]; exact hinv y hym
      obtain ⟨p, q, hp, hq, hpq, -, h3, h4, hfix⟩ := order3_exists_invariant_pair h.hd
      have heq := order3_invariant_triple_unique h.hd hx hy hxy hp hq hpq h1 h2 h3 h4
      rw [hP, heq] at hp₀w
      have hf := hfix p₀ h.hp₀ h.hdp
      simp only [Finset.mem_insert, Finset.mem_singleton] at hp₀w
      rcases hp₀w with e | e | e
      · exact hf.1 e
      · exact hf.2.1 e
      · exact hf.2.2 e
  refine sc_CTConcl_intro (sc_card_commSub_le hn _) ?_ (fun _ => hbot)
  rw [hbot, AddSubgroup.card_bot]
  norm_num

end CT

end CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Lemma2813

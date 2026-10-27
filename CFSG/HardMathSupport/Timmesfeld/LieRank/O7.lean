module

public import CFSG.HardMathSupport.Timmesfeld.LieRank.O7Sylow
public import CFSG.HardMathSupport.Timmesfeld.SporadicRank.CoverLower
public import CFSG.HardMathSupport.Timmesfeld.SporadicRank.CoverRank

public section

namespace CFSG.HardMathSupport.Timmesfeld.LieRank.O7

open Matrix CFSG.AGLEmbedding CFSG.AGLEmbedding.R3 CFSG.Open
  CFSG.HardMathSupport.Timmesfeld.SporadicRank

theorem rank_le_six {V G : Type*} [Fintype V] [DecidableEq V] [DecidableEq G]
    (hV : Fintype.card V = 3 ^ 5) (fix : G → Finset V) (O : Finset G) (h1 : O.card ≤ 44)
    (h2 : ∀ g ∈ O, (fix g).card ≤ 27) (S : Finset G) (hSO : S ⊆ O) (B : Finset V) {a j : ℕ}
    (hB : B.card = 3 ^ a) (hS : S.card + 1 = 3 ^ j) (hfix : ∀ g ∈ S, B ⊆ fix g) : a + j ≤ 6 := by
  have hSle : S.card ≤ 44 := (Finset.card_le_card hSO).trans h1
  have hj3 : j ≤ 3 := by
    by_contra hj
    have : 3 ^ 4 ≤ 3 ^ j := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  by_cases hSe : S = ∅
  · subst hSe
    have : 3 ^ j = 1 := by simpa using hS.symm
    have hj0 : j = 0 := by
      rcases Nat.pow_eq_one.mp this with h | h
      · omega
      · exact h
    have hBle : 3 ^ a ≤ 3 ^ 5 := by rw [← hB, ← hV]; exact Finset.card_le_univ B
    have := (Nat.pow_le_pow_iff_right (by norm_num)).1 hBle
    omega
  · obtain ⟨g0, hg0⟩ := Finset.nonempty_iff_ne_empty.mpr hSe
    have h' : 3 ^ a ≤ 27 := hB ▸ (Finset.card_le_card (hfix g0 hg0)).trans (h2 g0 (hSO hg0))
    have ha3 : a ≤ 3 := by
      by_contra ha
      have : 3 ^ 4 ≤ 3 ^ a := Nat.pow_le_pow_right (by norm_num) (by omega)
      omega
    omega

theorem O7_card : (o3SetN 5 (wordsL 3 5 gensL)).card ≤ 44 := by decide +kernel

theorem O7_fix : ∀ A ∈ wordsL 3 5 gensL, toMatL 3 5 A ≠ 1 → toMatL 3 5 A ^ 3 = 1 →
    (fixSetN 5 (toMatL 3 5 A)).card ≤ 27 := by decide +kernel

theorem O7_facts : (o3SetN 5 (wordsL 3 5 gensL)).card ≤ 44 ∧
    ∀ M ∈ o3SetN 5 (wordsL 3 5 gensL), (fixSetN 5 M).card ≤ 27 := by
  refine ⟨O7_card, fun M hM => ?_⟩
  simp only [o3SetN, matSetN, Finset.mem_filter, List.mem_toFinset, List.mem_map] at hM
  obtain ⟨⟨A, hA, rfl⟩, h1, h2⟩ := hM
  exact O7_fix A hA h1 h2

theorem pRank_Om7_le_six : CFSG.Open.pRank 3 (⊤ : Subgroup Om7) ≤ 6 := by
  have : Finite Om7 := inferInstance
  refine pRank_le_of_cover sylowCover_O7 fun m hm S B a j hSO hB hS hfix => ?_
  subst hm
  have hV : Fintype.card (Fin 5 → ZMod 3) = 3 ^ 5 := by simp [ZMod.card]
  exact rank_le_six hV (fixSetN 5) (o3SetN 5 (wordsL 3 5 gensL)) O7_facts.1 O7_facts.2 S hSO B hB
    hS hfix

theorem pRank_quotient_le_of_cover_O7 {L : Type} [Group L] [Finite L]
    (hq : CFSG.Open.IsQuasisimple L)
    (e : L ⧸ Subgroup.center L ≃* StatedProj (StatedOmega (StatedQuadOdd 3 (ZMod 3))))
    (h3 : 3 ∣ Nat.card (Subgroup.center L)) (hZ6 : Nat.card (Subgroup.center L) ∣ 6) :
    CFSG.Open.pRank 3 (⊤ : Subgroup (L ⧸ Subgroup.center L)) ≤
      CFSG.Open.pRank 3 (⊤ : Subgroup L) := by
  have e' : L ⧸ Subgroup.center L ≃* Om7 := e.trans ProjEquivOm7
  have hlow := CFSG.HardMathSupport.Timmesfeld.SporadicRank.lower_of_cover hq e' hZ6 h3 modSpec
    noAlt_O7 noFun_O7
  have hup := pRank_Om7_le_six
  have heq := CFSG.SectionRank.pRank_top_eq_of_mulEquiv (p := 3) (by norm_num) e'
  have hn : modSpec.n = 5 := rfl
  omega

end CFSG.HardMathSupport.Timmesfeld.LieRank.O7

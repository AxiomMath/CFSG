module

public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.I294CrossSylow
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.I294OuterDiag
public import CFSG.HardMathSupport.Solomon.Coordinator.L514CRank

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.Bal3

open CFSG CFSG.Open Subgroup
open CFSG.LocalAnalysis.RankFourTheoremC (IsLinearOrUnitaryAt)

theorem I294Cross.pRank_three_le_two_of_isL3Eps {X : Type} [Group X] [Finite X] {r : ℕ}
    (h : CFSG.HardMathSupport.Solomon.LocalBalance.Lemma514CoverNs.IsL3Eps r X) :
    CFSG.Open.pRank 3 (⊤ : Subgroup X) ≤ 2 := by
  refine CFSG.SectionRank.pRank_le Nat.prime_three.one_lt fun E _ hE => ?_
  have := CFSG.HardMathSupport.Solomon.Coordinator.lemma514Cover_inputL3rk_holds X r h E hE
  simpa using this

theorem I294Cfg.false_of_linear_three {Y : Type} [Group Y] [Finite Y] {L : Subgroup Y}
    [L.Normal] {z g : Y} {D : Subgroup Y} (h : I294Cfg 3 L z g D) {n : ℕ} {K : Type} [Field K]
    [Finite K] (h3n : 3 ∣ n) (h3K : 3 ∣ Nat.card K - 1)
    (e : ↥L ≃* StatedProj (StatedSL n K)) : False := by
  have hn0 : 0 < n := by
    rcases Nat.eq_zero_or_pos n with rfl | hn0
    · haveI : Subsingleton (StatedProj (StatedSL 0 K)) := inferInstance
      exact (od_false_of_zero_dim h.nonab e).elim
    · exact hn0
  by_cases hn3 : n = 3
  · subst hn3
    by_cases h9 : 9 ∣ Nat.card K - 1
    · obtain ⟨P, hDP⟩ := h.exists_sylow_ge
      have h81 : 81 ∣ Nat.card L := by
        rw [Nat.card_congr e.toEquiv]
        exact linThree_eightyOne_dvd h3K h9
      have hPL := h.le_of_dvd_eightyOne' hDP h81
      have hK1 : 1 ≤ Nat.card K := Nat.card_pos
      have hL3 : CFSG.HardMathSupport.Solomon.LocalBalance.Lemma514CoverNs.IsL3Eps
          (Nat.card K) ↥L :=
        Or.inl ⟨by omega, ⟨K, inferInstance, inferInstance, rfl, ⟨e⟩⟩⟩
      exact h.false_of_sylow_le hPL (I294Cross.pRank_three_le_two_of_isL3Eps hL3)
    · obtain ⟨E, hE, hEc⟩ := h.exists_elemAbelian_twentySeven
      let e' : ↥L ≃* CFSG.LocalAnalysis.ComponentInitial.LinearFlag.projectiveSL 3 K :=
        e.trans (CFSG.LocalAnalysis.RankFourTheoremC.l212in_projectiveSLEquivStated 3 K).symm
      obtain ⟨B, hB, hBc⟩ := od_exists_elemAbelian_mulAut_of_equiv h.cent e' hE hEc
      exact h9 (linThree_nine_dvd h3K B hB hBc.ge)
  · have hn6 : 6 ≤ n := by omega
    have h4 := odFour_le_pRank_psl Nat.prime_three hn6 h3K
    have h1 : CFSG.Open.pRank 3 (⊤ : Subgroup (StatedProj (StatedSL n K))) ≤
        CFSG.Open.pRank 3 (⊤ : Subgroup Y) :=
      CFSG.SectionRank.pRank_top_le_of_injective (by norm_num)
        (L.subtype.comp e.symm.toMonoidHom) (L.subtype_injective.comp e.symm.injective)
    have := h.rank
    omega

theorem I294Cfg.false_of_unitary_three {Y : Type} [Group Y] [Finite Y] {L : Subgroup Y}
    [L.Normal] {z g : Y} {D : Subgroup Y} (h : I294Cfg 3 L z g D) {n q : ℕ} {K : Type}
    [Field K] [Finite K] (hKq : Nat.card K = q ^ 2) (h3n : 3 ∣ n) (h3q : 3 ∣ q + 1)
    (e : ↥L ≃* StatedProj (StatedSU n q K)) : False := by
  have hn0 : 0 < n := by
    rcases Nat.eq_zero_or_pos n with rfl | hn0
    · haveI : Subsingleton (StatedProj (StatedSU 0 q K)) := inferInstance
      exact (od_false_of_zero_dim h.nonab e).elim
    · exact hn0
  obtain ⟨r, m, hr, hchar, -, hKr⟩ := CFSG.LocalAnalysis.RankFourTheoremC.exists_char_pow_card K
  haveI : Fact r.Prime := ⟨hr⟩
  haveI := hchar
  obtain ⟨f, -, hqf⟩ : ∃ f ≤ m, q = r ^ f := by
    refine (Nat.dvd_prime_pow hr).1 ?_
    rw [← hKr, hKq]
    exact dvd_pow_self q two_ne_zero
  subst hqf
  have hf : 1 ≤ f := by
    rcases Nat.eq_zero_or_pos f with rfl | hf
    · exfalso
      rw [pow_zero] at hKq
      have : Nat.card K = 1 := by rw [hKq]; norm_num
      have h2 : 1 < Nat.card K := Finite.one_lt_card
      omega
    · exact hf
  have hU : CFSG.LocalAnalysis.ComponentInitial.UnitaryFieldData r f K :=
    ⟨hr, hf, by rw [hKq, ← pow_mul, mul_comm]⟩
  by_cases hn3 : n = 3
  · subst hn3
    by_cases hq2 : r ^ f = 2
    · haveI := h.simple
      exact uniThree_two_false hKq hf hq2 h.nonab e
    · have hq : 2 < r ^ f := by
        have hq1 : 1 < r ^ f := Nat.one_lt_pow (by omega) hr.one_lt
        omega
      by_cases h9 : 9 ∣ r ^ f + 1
      · obtain ⟨P, hDP⟩ := h.exists_sylow_ge
        have h81 : 81 ∣ Nat.card L := by
          rw [Nat.card_congr e.toEquiv]
          exact uniThree_eightyOne_dvd hKq hf h3q h9
        have hPL := h.le_of_dvd_eightyOne' hDP h81
        have hL3 : CFSG.HardMathSupport.Solomon.LocalBalance.Lemma514CoverNs.IsL3Eps
            (r ^ f) ↥L :=
          Or.inr ⟨by omega, ⟨K, inferInstance, inferInstance, hKq, ⟨e⟩⟩⟩
        exact h.false_of_sylow_le hPL (I294Cross.pRank_three_le_two_of_isL3Eps hL3)
      · obtain ⟨E, hE, hEc⟩ := h.exists_elemAbelian_twentySeven
        let e' : ↥L ≃* CFSG.ClassicalGroups.UnitaryFlag.unitaryPSU hU 3 :=
          e.trans (CFSG.ClassicalGroups.UnitaryFlag.unitaryPSUEquiv hU (by norm_num)).symm
        obtain ⟨B, hB, hBc⟩ := od_exists_elemAbelian_mulAut_of_equiv h.cent e' hE hEc
        exact h9 (uniThree_nine_dvd hU hq h3q B hB hBc.ge)
  · have hn6 : 6 ≤ n := by omega
    have h4 := odFour_le_pRank_psu hU Nat.prime_three hn6 h3q
    have h1 : CFSG.Open.pRank 3 (⊤ : Subgroup (StatedProj (StatedSU n (r ^ f) K))) ≤
        CFSG.Open.pRank 3 (⊤ : Subgroup Y) :=
      CFSG.SectionRank.pRank_top_le_of_injective (by norm_num)
        (L.subtype.comp e.symm.toMonoidHom) (L.subtype_injective.comp e.symm.injective)
    have := h.rank
    omega

theorem I294Cfg.false_of_linearOrUnitary_three {Y : Type} [Group Y] [Finite Y] {L : Subgroup Y}
    [L.Normal] {z g : Y} {D : Subgroup Y} (h : I294Cfg 3 L z g D)
    (hLU : IsLinearOrUnitaryAt 3 ↥L) : False := by
  rcases hLU with ⟨n, K, _, _, h3n, h3K, ⟨e⟩⟩ | ⟨n, q, K, _, _, hKq, h3n, h3q, ⟨e⟩⟩
  · exact h.false_of_linear_three h3n h3K e
  · exact h.false_of_unitary_three hKq h3n h3q e

end CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.Bal3

module

public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.I294Bridge
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.I294OuterDiagSylow
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.I294OuterDiagUni
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.I294OuterDiagRank
public import CFSG.LocalAnalysis.RankFourTheoremC.InvariantTwo.KFacts.I294OD
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.I294Inputs

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.Bal3

open CFSG CFSG.Open Subgroup
open CFSG.LocalAnalysis.RankFourTheoremC (IsLinearOrUnitaryAt)

theorem od_false_of_zero_dim {L : Type} [Group L] {X : Type} [Group X] [Subsingleton X]
    (hnab : ∃ a b : L, a * b ≠ b * a) (e : L ≃* X) : False := by
  obtain ⟨a, b, hab⟩ := hnab
  exact hab (e.injective (Subsingleton.elim _ _))

theorem I294Cfg.le_of_linear_three {Y : Type} [Group Y] [Finite Y] {L : Subgroup Y} [L.Normal]
    {z g : Y} {D : Subgroup Y} (h : I294Cfg 3 L z g D) {n : ℕ} {K : Type} [Field K] [Finite K]
    (h3n : 3 ∣ n) (h3K : 3 ∣ Nat.card K - 1) (e : ↥L ≃* StatedProj (StatedSL n K)) :
    D ≤ L := by
  have hn0 : 0 < n := by
    rcases Nat.eq_zero_or_pos n with rfl | hn0
    · haveI : Subsingleton (StatedProj (StatedSL 0 K)) := inferInstance
      exact (od_false_of_zero_dim h.nonab e).elim
    · exact hn0
  by_cases hn3 : n = 3
  · subst hn3
    by_cases h9 : 9 ∣ Nat.card K - 1
    · have h81 : 81 ∣ Nat.card L := by
        rw [Nat.card_congr e.toEquiv]
        exact linThree_eightyOne_dvd h3K h9
      exact h.le_of_dvd_eightyOne h81
    · exfalso
      obtain ⟨E, hE, hEc⟩ := h.exists_elemAbelian_twentySeven
      let e' : ↥L ≃* CFSG.LocalAnalysis.ComponentInitial.LinearFlag.projectiveSL 3 K :=
        e.trans (CFSG.LocalAnalysis.RankFourTheoremC.l212in_projectiveSLEquivStated 3 K).symm
      obtain ⟨B, hB, hBc⟩ := od_exists_elemAbelian_mulAut_of_equiv h.cent e' hE hEc
      exact h9 (linThree_nine_dvd h3K B hB hBc.ge)
  · exfalso
    have hn6 : 6 ≤ n := by omega
    have h4 := odFour_le_pRank_psl Nat.prime_three hn6 h3K
    have h1 : CFSG.Open.pRank 3 (⊤ : Subgroup (StatedProj (StatedSL n K))) ≤
        CFSG.Open.pRank 3 (⊤ : Subgroup Y) :=
      CFSG.SectionRank.pRank_top_le_of_injective (by norm_num)
        (L.subtype.comp e.symm.toMonoidHom) (L.subtype_injective.comp e.symm.injective)
    have := h.rank
    omega

theorem I294Cfg.le_of_unitary_three {Y : Type} [Group Y] [Finite Y] {L : Subgroup Y} [L.Normal]
    {z g : Y} {D : Subgroup Y} (h : I294Cfg 3 L z g D) {n q : ℕ} {K : Type} [Field K] [Finite K]
    (hKq : Nat.card K = q ^ 2) (h3n : 3 ∣ n) (h3q : 3 ∣ q + 1)
    (e : ↥L ≃* StatedProj (StatedSU n q K)) : D ≤ L := by
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
    · exfalso
      haveI := h.simple
      exact uniThree_two_false hKq hf hq2 h.nonab e
    · have hq : 2 < r ^ f := by
        have hq1 : 1 < r ^ f := Nat.one_lt_pow (by omega) hr.one_lt
        omega
      by_cases h9 : 9 ∣ r ^ f + 1
      · have h81 : 81 ∣ Nat.card L := by
          rw [Nat.card_congr e.toEquiv]
          exact uniThree_eightyOne_dvd hKq hf h3q h9
        exact h.le_of_dvd_eightyOne h81
      · exfalso
        obtain ⟨E, hE, hEc⟩ := h.exists_elemAbelian_twentySeven
        let e' : ↥L ≃* CFSG.ClassicalGroups.UnitaryFlag.unitaryPSU hU 3 :=
          e.trans (CFSG.ClassicalGroups.UnitaryFlag.unitaryPSUEquiv hU (by norm_num)).symm
        obtain ⟨B, hB, hBc⟩ := od_exists_elemAbelian_mulAut_of_equiv h.cent e' hE hEc
        exact h9 (uniThree_nine_dvd hU hq h3q B hB hBc.ge)
  · exfalso
    have hn6 : 6 ≤ n := by omega
    have h4 := odFour_le_pRank_psu hU Nat.prime_three hn6 h3q
    have h1 : CFSG.Open.pRank 3 (⊤ : Subgroup (StatedProj (StatedSU n (r ^ f) K))) ≤
        CFSG.Open.pRank 3 (⊤ : Subgroup Y) :=
      CFSG.SectionRank.pRank_top_le_of_injective (by norm_num)
        (L.subtype.comp e.symm.toMonoidHom) (L.subtype_injective.comp e.symm.injective)
    have := h.rank
    omega

theorem i294OuterDiag_holds : I294OuterDiag := by
  intro p Y _ _ L _ z g D cfg hlin
  by_cases hp5 : 5 ≤ p
  · exfalso
    obtain ⟨x, hxD, hx1, hxS⟩ := cfg.sylowLine
    exact CFSG.LocalAnalysis.RankFourTheoremC.i294OutDiagExcluded_holds p cfg.prime hp5 Y L
      cfg.simple cfg.nonab cfg.catalog cfg.cent D cfg.elem cfg.card cfg.sylow cfg.rank.ge z g
      cfg.mem cfg.ne_one cfg.diag
      ⟨x, hxD, hx1, pRank_centralizer_le_two_of_isSylowOf cfg.prime cfg.card hxS⟩ hlin
  · have hp3 : p = 3 := by
      have h1 := cfg.prime.two_le
      have h2 := cfg.odd
      have h4 : p ≠ 4 := by rintro rfl; exact absurd cfg.prime (by decide)
      omega
    subst hp3
    rcases hlin with ⟨n, K, _, _, h3n, h3K, ⟨e⟩⟩ | ⟨n, q, K, _, _, hKq, h3n, h3q, ⟨e⟩⟩
    · exact cfg.le_of_linear_three h3n h3K e
    · exact cfg.le_of_unitary_three hKq h3n h3q e

end CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.Bal3

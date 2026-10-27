module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.D4XFIso
public import CFSG.RankThree.PartTwo.Sec4.T444.Item434SmallTwoIVKit
public import CFSG.RankThree.PartTwo.Sec4.Census.RankOmegaF4
public import CFSG.LocalAnalysis.GLTheoremA.S9.L94Transport

public section

namespace CFSG.LocalAnalysis.GLTheoremA.D4XF

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremA.S9

theorem exists_E27_of_three_le_twoLocalPrimeRank {G : Type} [Group G] [Finite G]
    (h : 3 ≤ CFSG.Open.twoLocalPrimeRank 3 G) :
    ∃ E W : Subgroup G, CFSG.Open.IsElemAbelian 3 E ∧ Nat.card E = 3 ^ 3 ∧ IsPGroup 2 W ∧ W ≠ ⊥ ∧
      E ≤ Subgroup.normalizer (W : Set G) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hp : 1 < 3 := by norm_num
  have hbdd : BddAbove {k : ℕ | ∃ H : Subgroup G, CFSG.Open.IsTwoLocal H ∧ CFSG.Open.pRank 3 H = k} := by
    refine ⟨Nat.card G, ?_⟩
    rintro k ⟨H, -, rfl⟩
    obtain ⟨E, -, -, hE⟩ := CFSG.SectionRank.exists_pRank hp H
    have h1 : CFSG.Open.pRank 3 H < 3 ^ CFSG.Open.pRank 3 H := Nat.lt_pow_self (by norm_num)
    have h2 : Nat.card E ≤ Nat.card G := Subgroup.card_le_card_group E
    rw [hE] at h2
    omega
  have hne : ({k : ℕ | ∃ H : Subgroup G, CFSG.Open.IsTwoLocal H ∧ CFSG.Open.pRank 3 H = k}).Nonempty := by
    by_contra hn
    rw [Set.not_nonempty_iff_eq_empty] at hn
    have h0 : CFSG.Open.twoLocalPrimeRank 3 G = 0 := by
      unfold CFSG.Open.twoLocalPrimeRank
      rw [hn]; simp
    omega
  obtain ⟨H, hH2, hHk⟩ := Nat.sSup_mem hne hbdd
  have h3 : 3 ≤ CFSG.Open.pRank 3 H := by
    rw [hHk]
    exact h
  obtain ⟨P, hP, hP2, rfl⟩ := hH2
  obtain ⟨E, hEH, hE, hEc⟩ := CFSG.SectionRank.exists_pRank hp (Subgroup.normalizer (P : Set G))
  have hdvd : 3 ^ 3 ∣ Nat.card E := by
    rw [hEc]
    exact Nat.pow_dvd_pow 3 h3
  obtain ⟨E₀, hE₀⟩ := Sylow.exists_subgroup_card_pow_prime 3 (G := E) hdvd
  refine ⟨E₀.map E.subtype, P, ?_, ?_, hP2, hP, ?_⟩
  · exact CFSG.LocalAnalysis.GLTheoremA.isElemAbelian_mono hE (Subgroup.map_subtype_le E₀)
  · rw [Subgroup.card_map_of_injective E.subtype_injective, hE₀]
  · intro x hx
    obtain ⟨y, -, rfl⟩ := Subgroup.mem_map.1 hx
    exact hEH y.2

theorem d4two_rank3 {K : Type} [Group K] [Finite K] (h : catalogIs K S9.isD4two) :
    ∃ E W : Subgroup K, CFSG.Open.IsElemAbelian 3 E ∧ Nat.card E = 3 ^ 3 ∧ IsPGroup 2 W ∧ W ≠ ⊥ ∧
      E ≤ Subgroup.normalizer (W : Set K) := by
  obtain ⟨e⟩ := equiv_projOmegaPlus h
  haveI : Finite (CFSG.PGLModel.projOmegaPlus 4 (GaloisField 2 1)) := Finite.of_equiv K e.toEquiv
  apply exists_E27_of_three_le_twoLocalPrimeRank
  have hloc := CFSG.RankThree.PartTwo.Census.localRank_eq_of_mulEquiv e Nat.prime_three
  change 3 ≤ CFSG.Assembly.RankThreeEven.localRank 3 K
  rw [hloc]
  exact CFSG.RankThree.PartTwo.Sec4.Census.localRank_omega8PlusTwo

theorem d4two_rank4 {K : Type} [Group K] [Finite K] (h : catalogIs K S9.isD4two) :
    ∃ E : Subgroup K, CFSG.Open.IsElemAbelian 3 E ∧ Nat.card E = 3 ^ 4 := by
  obtain ⟨e⟩ := equiv_projOmegaPlus h
  obtain ⟨D, hD, hDc⟩ := CFSG.RankThree.PartTwo.Sec4.Item434SmallTwoIV.exists_e81_of_three_lt_pRank
    CFSG.RankThree.PartTwo.Sec4.Census.three_lt_pRank_omegaPlus
  refine ⟨D.map e.symm.toMonoidHom, CFSG.LocalAnalysis.GLTheoremA.S9.l94t_isElemAbelian_map _ hD, ?_⟩
  rw [Subgroup.card_map_of_injective e.symm.injective, hDc]
  norm_num

end CFSG.LocalAnalysis.GLTheoremA.D4XF

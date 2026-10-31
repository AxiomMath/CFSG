module

public import CFSG.LocalAnalysis.RankFourTheoremC.RelativePair.Endgame
import CFSG.LocalAnalysis.RankThreeTheoremC.RelPair2A7_Main

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers CFSG.LocalAnalysis.RankThreeTheoremC Subgroup

variable {G : Type} [Group G] [Finite G]

theorem le_pRank_of_isElemAbelian_of_pow_le {q : ℕ} (hq : q.Prime) {H E : Subgroup G}
    (hEH : E ≤ H) (hE : IsElemAbelian q E) {k : ℕ} (hk : q ^ k ≤ Nat.card E) :
    k ≤ CFSG.Open.pRank q H := by
  have : Fact q.Prime := ⟨hq⟩
  have hEp : IsPGroup q E := fun x => ⟨1, by
    have := hE.2 x x.2
    exact Subtype.ext (by simpa using this)⟩
  obtain ⟨j, hj⟩ := hEp.exists_card_eq
  have hkj : k ≤ j := by
    rw [hj] at hk
    exact (Nat.pow_le_pow_iff_right hq.one_lt).mp hk
  exact hkj.trans (le_pRank_of_isElemAbelian' hq.one_lt hEH hE hj)

theorem three_mem_sigmaA_of_four_le_localRank (hloc : 4 ≤ rankThreeLocalRank 3 G)
    (h3dvd : 3 ∣ Nat.card G) : 3 ∈ rankThreeSigmaA G := by
  have hS1 : (3 : ℕ) ∈ {p : ℕ | p.Prime ∧ p ≠ 2 ∧ p ∣ Nat.card G ∧ 3 < rankThreeLocalRank p G} :=
    ⟨Nat.prime_three, by norm_num, h3dvd, by omega⟩
  have hne : ({p : ℕ | p.Prime ∧ p ≠ 2 ∧ p ∣ Nat.card G ∧
      3 < rankThreeLocalRank p G}).Nonempty := ⟨3, hS1⟩
  unfold rankThreeSigmaA
  dsimp only
  split_ifs
  · exact hS1
  all_goals exact absurd hne h1

theorem ObstructionSetting.not_dvd_card_invariantTwoJoinIn_of_rank_three
    (hS : ObstructionSetting G) (hD1 : TheoremD1 G) {p : ℕ} (hp : p ∈ rankThreeSigmaA G)
    {P : Sylow p G} {M D H : Subgroup G} (hext : ExtremalObstruction p P M D)
    (hPD : ¬ (P : Subgroup G) ≤ normalizer (D : Set G)) (hR : TransitivityReduction G)
    (h13 : GL83InvariantTwoSylow G) (hHtwo : IsTwoLocal H) {Q : Subgroup G} (hQH : Q ≤ H)
    (hQ3 : IsPGroup 3 Q)
    (hA : ∃ A : Subgroup G, A ≤ Q ∧ IsElemAbelian 3 A ∧ 3 ^ 4 ≤ Nat.card A)
    (hB : ∃ d ∈ D, d ≠ 1 ∧ ∃ B : Subgroup G, B ≤ Q ⊓ centralizer ({d} : Set G) ∧
      IsElemAbelian 3 B ∧ 3 ^ 3 ≤ Nat.card B) :
    ¬ p ∣ Nat.card (invariantTwoJoinIn D (H ⊓ normalizer (Q : Set G))) := by
  classical
  obtain ⟨A, hAQ, hAe, hA4⟩ := hA
  obtain ⟨d, hdD, hd1, B, hBQ, hBe, hB3⟩ := hB
  have hprime := sigmaA_prime p hp
  have hfact : Fact p.Prime := ⟨hprime⟩
  have h3prime : (3 : ℕ).Prime := Nat.prime_three
  obtain ⟨hDab, z, hzD, hz1, hzc, hzp, hN₀M, hCD, -⟩ :=
    hS.transitivity_data hD1 hp hext hPD hR h13
  obtain ⟨hM, hDP, -, -⟩ := hext.obstruction
  have hQ4 : 4 ≤ CFSG.Open.pRank 3 Q := le_pRank_of_isElemAbelian_of_pow_le h3prime hAQ hAe hA4
  have hH4 : 4 ≤ CFSG.Open.pRank 3 H := hQ4.trans (pRank_mono 3 h3prime.one_lt hQH)
  have hloc : 4 ≤ rankThreeLocalRank 3 G :=
    hH4.trans (local_pRank_le_localRank 3 h3prime.one_lt H hHtwo)
  have h3dvd : 3 ∣ Nat.card G := prime_dvd_card_of_pRank_pos 3 H (by omega)
  have h3sig : 3 ∈ rankThreeSigmaA G := three_mem_sigmaA_of_four_le_localRank hloc h3dvd
  obtain ⟨Y, hQY⟩ := hQ3.exists_le_sylow
  obtain ⟨M', hM', hYM'⟩ := hS.exists_isCoreMaxLocal h3sig Y
  have hQM' : Q ≤ M' := hQY.trans hYM'
  obtain ⟨g, hgN, hgz⟩ := hS.exists_mem_normalizer_zpowers_eq hD1 hp hext hPD hDab hCD hzD hz1
    hzc hN₀M hdD hd1
  have hBMg : B ≤ M.map (MulAut.conj g).toMonoidHom := by
    refine (hBQ.trans inf_le_right).trans
      ((centralizer_singleton_le_normalizer_zpowers d).trans ?_)
    rw [hgz, ← Subgroup.map_equiv_normalizer_eq]
    exact map_mono hN₀M
  have hBM' : B ≤ M' := (hBQ.trans inf_le_left).trans hQM'
  have hrk3 : 3 ≤ CFSG.Open.pRank 3 (M.map (MulAut.conj g).toMonoidHom ⊓ M') :=
    le_pRank_of_isElemAbelian_of_pow_le h3prime (le_inf hBMg hBM') hBe hB3
  have hMgM' : M.map (MulAut.conj g).toMonoidHom ≤ M' :=
    le_of_three_le_pRank_inf hD1 h3sig hM' (twoLocal_map_automorphism M hM.1.1 _) hrk3
  have hMgmax := rankThreeIsMaxTwoLocal_map hM.1 (MulAut.conj g)
  have hMgeq : M' = M.map (MulAut.conj g).toMonoidHom := hMgmax.2 M' hM'.1.1 hMgM'
  have hNQ : normalizer (Q : Set G) ≤ M' :=
    normalizer_le_of_three_le_pRank hD1 h3sig hM' hQM' (by omega)
  have hjoin : invariantTwoJoinIn D (H ⊓ normalizer (Q : Set G)) ≤
      (invariantTwoJoinIn D M).map (MulAut.conj g).toMonoidHom := by
    refine (invariantTwoJoinIn_mono (inf_le_right.trans hNQ)).trans ?_
    rw [hMgeq]
    exact invariantTwoJoinIn_map_le hgN
  intro hdvd
  have hcop := hS.coprime_card_invariantTwoJoinIn_left hD1 hp hext hPD hR h13
  have hdvd' : p ∣ Nat.card ((invariantTwoJoinIn D M).map (MulAut.conj g).toMonoidHom) :=
    hdvd.trans (Subgroup.card_dvd_of_le hjoin)
  rw [Subgroup.card_map_of_injective (MulAut.conj g).injective] at hdvd'
  exact (hprime.coprime_iff_not_dvd.mp hcop) hdvd'

end CFSG.LocalAnalysis.RankFourTheoremC

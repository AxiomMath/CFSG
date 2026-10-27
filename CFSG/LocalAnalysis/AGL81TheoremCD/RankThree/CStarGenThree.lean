module

public import CFSG.LocalAnalysis.AGL81TheoremCD.AlmostStrongCoreMap
public import CFSG.LocalAnalysis.AGL81TheoremC.SigmaPrimes
public import CFSG.LocalAnalysis.SectionRank.DerivedQuotient
import CFSG.LocalAnalysis.AGL81TheoremCD.FrobeniusRank

public section

namespace CFSG.LocalAnalysis.AGL81TheoremCD.RankThree

open CFSG.Open Subgroup
open CFSG.LocalAnalysis.AGL81TheoremCD CFSG.LocalAnalysis.RankThreeUC
open CFSG.LocalAnalysis.RankThreeTheoremC
open CFSG.RankThreeCoreUniqueness.Helpers

variable {G : Type} [Group G] [Finite G]

theorem almostClauseTwoCore_of_rankThreeClauseB {M P : Subgroup G} {p : ℕ}
    (h : rankThreeClauseB M P p) : AlmostClauseTwoCore M P p := by
  obtain ⟨hp5, hsolv, P₀, hP₀P, hcard, hweak, hiso, hnotle, hfrob, hother⟩ := h
  obtain ⟨X, hXW, hXK, hKne, -, hKX, hKnorm, hdisj, hfpf⟩ := hfrob
  refine ⟨hp5, hsolv, P₀, hP₀P, hcard, hweak, hiso, hnotle, hother, ?_, ?_⟩
  · intro q hq hq2
    have hK2 : IsPGroup 2 (pCoreOf 2 M) :=
      CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_isPGroup 2 M
    have hWX : rankThreePrimeCore p M ≤ X := by
      intro y hy
      exact (hXW y).mpr ⟨y, hy, 1, Subgroup.one_mem _, by simp⟩
    have hVX : Subgroup.centralizer
        (rankThreeLayer (Subgroup.centralizer (P₀ : Set G)) : Set G) ≤ X := by
      intro v hv
      exact (hXK v).mpr ⟨1, Subgroup.one_mem _, v, hv, by simp⟩
    have hVnorm : Subgroup.centralizer
        (rankThreeLayer (Subgroup.centralizer (P₀ : Set G)) : Set G) ≤
        Subgroup.normalizer (pCoreOf 2 M : Set G) :=
      hVX.trans ((Subgroup.normal_subgroupOf_iff_le_normalizer hKX).mp hKnorm)
    exact pRank_le_one_of_twoGroup_frobeniusProduct hK2 hKne hKX hVX hWX hKnorm hdisj
      (fun x hx => (hXK x).mp hx) hVnorm hfpf hq hq2
  · intro q hq hq2
    have hK2 : IsPGroup 2 (pCoreOf 2 M) :=
      CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_isPGroup 2 M
    have hVX : Subgroup.centralizer
        (rankThreeLayer (Subgroup.centralizer (P₀ : Set G)) : Set G) ≤ X := by
      intro v hv
      exact (hXK v).mpr ⟨1, Subgroup.one_mem _, v, hv, by simp⟩
    have hVnorm : Subgroup.centralizer
        (rankThreeLayer (Subgroup.centralizer (P₀ : Set G)) : Set G) ≤
        Subgroup.normalizer (pCoreOf 2 M : Set G) :=
      hVX.trans ((Subgroup.normal_subgroupOf_iff_le_normalizer hKX).mp hKnorm)
    have hVrank : CFSG.Open.pRank q (Subgroup.centralizer
        (rankThreeLayer (Subgroup.centralizer (P₀ : Set G)) : Set G)) ≤ 1 :=
      pRank_le_one_of_twoGroup_fixedPointFree hK2 hKne hVnorm hfpf hq hq2
    exact (CFSG.SectionRank.pRank_mono hq.one_lt
      (inf_le_right : Subgroup.centralizer (P₀ : Set G) ⊓
        Subgroup.centralizer (rankThreeLayer (Subgroup.centralizer (P₀ : Set G)) : Set G) ≤
        Subgroup.centralizer
          (rankThreeLayer (Subgroup.centralizer (P₀ : Set G)) : Set G))).trans hVrank

theorem almostStrongCore_of_isWitness (hS : Standing G) {p : ℕ}
    (hp : p ∈ rankThreeSigmaA G) {P : Sylow p G} {M : Subgroup G} (hw : IsWitness p P M) :
    AlmostStrongCore M p := by
  refine ⟨P, hw.sylow_le hS hp, hw.u0, ?_⟩
  rcases hw.u1 with hΓ1 | hB | ⟨h3, hC⟩
  · exact Or.inl hΓ1
  · exact Or.inr (Or.inl (almostClauseTwoCore_of_rankThreeClauseB hB))
  · exact Or.inr (Or.inr ⟨h3, hC⟩)

theorem exists_map_conj_eq_of_isWitness (hS : Standing G) {p : ℕ}
    (hp : p ∈ rankThreeSigmaA G) {P : Sylow p G} {M N : Subgroup G}
    (hw : IsWitness p P M) (hN : rankThreeIsMaxTwoLocal N)
    (h2 : 2 ≤ CFSG.Open.pRank p N) :
    ∃ g : G, M.map (MulAut.conj g).toMonoidHom = N := by
  have hqp : p.Prime := sigmaA_prime p hp
  haveI : Fact p.Prime := ⟨hqp⟩
  obtain ⟨E, hEN, hE, hEc⟩ :=
    CFSG.SectionRank.exists_isElemAbelian_card_of_le_pRank (p := p) (k := 2) h2
  have hEp : IsPGroup p E := elementary_isPGroup p E hE
  obtain ⟨Q, hEQ⟩ := hEp.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.IsPretransitive.exists_smul_eq (M := G) P Q
  have hPQ : (Q : Subgroup G) = (P : Subgroup G).map (MulAut.conj g).toMonoidHom := by
    rw [← sylow_conjugate_eq_map, hg]
  have hcw : IsCoreWitness p (Q : Subgroup G) (M.map (MulAut.conj g).toMonoidHom) := by
    have h := hw.isCoreWitness.map hqp.one_lt (MulAut.conj g)
    rwa [← hPQ] at h
  have hQM : (Q : Subgroup G) ≤ M.map (MulAut.conj g).toMonoidHom :=
    le_normalizer.trans (hcw.normalizer_le hS hp)
  have hE2 : 2 ≤ CFSG.Open.pRank p (N ⊓ M.map (MulAut.conj g).toMonoidHom) := by
    have hk : 2 ≤ CFSG.Open.pRank p E := CFSG.SectionRank.le_pRank hqp.one_lt (le_refl E) hE hEc
    exact hk.trans (CFSG.RankThreeCoreUniqueness.Helpers.pRank_mono p hqp.one_lt
      (le_inf hEN (hEQ.trans hQM)))
  have hM₁ : rankThreeIsMaxTwoLocal (M.map (MulAut.conj g).toMonoidHom) :=
    rankThreeIsMaxTwoLocal_map hw.maxLocal (MulAut.conj g)
  have hNM : N ≤ M.map (MulAut.conj g).toMonoidHom := hcw.u2 N hN.1 hE2
  exact ⟨g, hN.2 _ hM₁.1 hNM⟩

theorem almostStrongCore_of_two_le_pRank (hS : Standing G) (hUC : rankThreeUC G)
    {p : ℕ} (hp : p ∈ rankThreeSigmaA G) {N : Subgroup G}
    (hN : rankThreeIsMaxTwoLocal N) (h2 : 2 ≤ CFSG.Open.pRank p N) :
    AlmostStrongCore N p := by
  obtain ⟨P, M, hw⟩ := rankThreeUC_iff.mp hUC p hp
  have hM : AlmostStrongCore M p := almostStrongCore_of_isWitness hS hp hw
  obtain ⟨g, hg⟩ := exists_map_conj_eq_of_isWitness hS hp hw hN h2
  rw [← hg]
  exact AlmostStrongCore.map (sigmaA_prime p hp).one_lt hM g

theorem mem_rankThreeSigmaA_of_gt_five
    (h : ∀ q : ℕ, q.Prime → q ≠ 2 → rankThreeLocalRank q G ≤ 3)
    {p : ℕ} (hp : p.Prime) (hp5 : 5 < p) (hdvd : p ∣ Nat.card G)
    (hrank : rankThreeLocalRank p G = 3) : p ∈ rankThreeSigmaA G := by
  classical
  have hS₁ : ¬ ({q : ℕ | q.Prime ∧ q ≠ 2 ∧ q ∣ Nat.card G ∧
      3 < rankThreeLocalRank q G} : Set ℕ).Nonempty := by
    rintro ⟨q, hq⟩
    exact absurd hq.2.2.2 (not_lt.mpr (h q hq.1 hq.2.1))
  have hS₂ : ({q : ℕ | q.Prime ∧ 5 < q ∧ q ∣ Nat.card G ∧
      rankThreeLocalRank q G = 3} : Set ℕ).Nonempty := ⟨p, hp, hp5, hdvd, hrank⟩
  simp only [rankThreeSigmaA]
  rw [if_neg hS₁, if_pos hS₂]
  exact ⟨hp, hp5, hdvd, hrank⟩

theorem cStarGen_of_rankThreeUC (hS : Standing G) (hUC : rankThreeUC G) : CStarGen G where
  simple := hS.simple
  nonab := hS.nonab
  kProper := hS.kProper
  charTwo := hS.charTwo
  rank := le_of_eq hS.rank.symm
  embed := by
    intro p hp N hN Q hQN hQ hQ2 H hH hQH
    exact CFSG.LocalAnalysis.AGL81TheoremC.le_of_mem_sigmaA hS hUC hp hN hQN hQ2 hH hQH
  exists_maxLocal := by
    intro p hp
    obtain ⟨P, M, hw⟩ := rankThreeUC_iff.mp hUC p hp
    refine ⟨M, hw.maxLocal, hp, ?_⟩
    have h3 := (hw.pRank_eq_three hS hp).2
    omega
  almost := by
    intro N hN p hp
    exact almostStrongCore_of_two_le_pRank hS hUC hp.1 hN hp.2
  off_sigma := by
    intro p hpPrime hp2 hpNot
    have hle : rankThreeLocalRank p G ≤ 3 := by
      have h := rankThreeLocalRank_le_evenRank (G := G) p hpPrime hp2
      rwa [hS.rank] at h
    refine ⟨hle, ?_⟩
    intro hrank
    by_contra h5
    have hp5 : 5 < p := by omega
    have hdvd : p ∣ Nat.card G := by
      obtain ⟨H, -, hHrank⟩ := rankThreeLocalRank_attained (G := G) p (by rw [hrank]; norm_num)
      have hpPos : 0 < CFSG.Open.pRank p H := by rw [hHrank, hrank]; norm_num
      exact prime_dvd_card_of_pRank_pos p H hpPos
    have hmem : p ∈ rankThreeSigmaA G :=
      mem_rankThreeSigmaA_of_gt_five (G := G) (fun q hq hq2 => by
        have h := rankThreeLocalRank_le_evenRank (G := G) q hq hq2
        rwa [hS.rank] at h) hpPrime hp5 hdvd hrank
    exact hpNot hmem

end CFSG.LocalAnalysis.AGL81TheoremCD.RankThree

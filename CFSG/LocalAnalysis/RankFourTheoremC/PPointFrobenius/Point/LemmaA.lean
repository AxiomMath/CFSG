module

public import CFSG.LocalAnalysis.RankFourTheoremC.PPointFrobenius.Point.Kx
public import CFSG.LocalAnalysis.RankFourTheoremC.PPointFrobenius.Critical
import CFSG.LocalAnalysis.RankThreeTheoremC.PSLTwoPElements
public import CFSG.LocalAnalysis.RankFourTheoremC.PPointFrobenius.Point.Data

public section

open Subgroup
open scoped MatrixGroups commutatorElement

namespace CFSG.LocalAnalysis.RankFourTheoremC.PPointFrobenius

open CFSG.LocalAnalysis.RankFourTheoremC CFSG.RankThreeCoreUniqueness.Helpers CFSG.Open
  CFSG.AGLEmbedding CFSG.AGLEmbeddingD2
open CFSG.LocalAnalysis.RankThreeTheoremC (eq_one_of_commute_of_mulEquiv_psl_two)

variable {G : Type} [Group G] [Finite G] {p : ℕ} {P : Sylow p G} {M : Subgroup G} {x : G}

theorem pt_keyF (hG : FrobGlobal G) (hloc : CFSG.AGLEmbedding.D1Local p P M) {r : ℕ}
    [Fact r.Prime] (hr2 : r ≠ 2) {D K₀ : Subgroup G} (hD : IsPGroup r D) (hDM : D ≤ M)
    (hD4 : 4 ≤ CFSG.Open.pRank r D) (hK₀ : ¬ K₀ ≤ M) (hKD : K₀ ≤ normalizer (D : Set G)) :
    False := by
  have hr : r.Prime := Fact.out
  have hpos : 0 < CFSG.Open.pRank r D := by omega
  have hdvd : r ∣ Nat.card G :=
    CFSG.PreuniquenessRankFour.Helpers.prime_dvd_card_of_positive_rank r hr D hpos
  have hrankM : 4 ≤ CFSG.Open.pRank r M :=
    hD4.trans (CFSG.PreuniquenessRankFour.Helpers.pRank_mono r hr hDM)
  have hrankG : 4 ≤ CFSG.Open.GLBTwoLocalRank r G :=
    hrankM.trans (le_csSup (CFSG.PreuniquenessRankFour.Helpers.twoLocalRank_bddAbove r hr)
      ⟨M, hloc.maxLocal.1, rfl⟩)
  have hβ : r ∈ CFSG.Open.GLBBetaFour G := ⟨hr, hr2, hdvd, hrankG⟩
  obtain ⟨F, hDF⟩ := hD.exists_le_sylow
  have hF3 : 3 ≤ CFSG.Open.pRank r (F : Subgroup G) := by
    have := CFSG.PreuniquenessRankFour.Helpers.pRank_mono r hr hDF
    omega
  obtain ⟨H, hHloc, hcoreH⟩ := (hG.pre r hβ).2 F
  obtain ⟨M', hHM', hM'max⟩ :=
    CFSG.PreuniquenessRankFour.Helpers.exists_maximal_twoLocal hHloc
  have hcoreM' : CFSG.Open.GLBWeakCore r (F : Subgroup G) ≤ M' := hcoreH.trans hHM'
  have hFM' : (F : Subgroup G) ≤ M' :=
    (CFSG.PreuniquenessRankFour.Helpers.subgroup_le_weakCore_of_rank r hr
      (F : Subgroup G) hF3).trans hcoreM'
  have hDM' : D ≤ M' := hDF.trans hFM'
  have h3 : 3 ≤ CFSG.Open.pRank r (M ⊓ M') := by
    have := CFSG.PreuniquenessRankFour.Helpers.pRank_mono r hr (le_inf hDM hDM')
    omega
  have hMM' : M ≤ M' := hG.d1 r hβ F M' hM'max hcoreM' M hloc.maxLocal.1 h3
  have hM'M : M' = M := hloc.maxLocal.2 M' hM'max.1 hMM'
  have hcoreM : CFSG.Open.GLBWeakCore r (F : Subgroup G) ≤ M :=
    hcoreH.trans (hHM'.trans hM'M.le)
  have hsup : CFSG.Open.pRank r D ≤
      CFSG.Open.pRank r (D ⊔ ((F : Subgroup G) ⊓ Subgroup.centralizer (D : Set G))) :=
    CFSG.PreuniquenessRankFour.Helpers.pRank_mono r hr le_sup_left
  have hN : Subgroup.normalizer (D : Set G) ≤ CFSG.Open.GLBWeakCore r (F : Subgroup G) :=
    CFSG.PreuniquenessRankFour.Helpers.normalizer_le_weakCore r hDF (by omega) (by omega)
  have hNM : Subgroup.normalizer (D : Set G) ≤ M := hN.trans hcoreM
  exact hK₀ (hKD.trans hNM)

private theorem isSimpleGroup_psl_pt {q m : ℕ} [Fact q.Prime] (hq5 : 5 ≤ q) (hm : 3 ≤ m) :
    IsSimpleGroup PSL(2, GaloisField q m) := by
  refine Matrix.ProjectiveSpecialLinearGroup.rank_two_simple ?_
  rw [GaloisField.card q m (by omega)]
  have h := Nat.pow_le_pow_right (by omega : q > 0) (by omega : 1 ≤ m)
  rw [Nat.pow_one] at h
  omega

private theorem commutator_eq_self_psl_pt {H : Type} [Group H] {q m : ℕ} [Fact q.Prime]
    (hq5 : 5 ≤ q) (hm : 3 ≤ m) {L : Subgroup H} (e : L ≃* PSL(2, GaloisField q m)) :
    ⁅L, L⁆ = L := by
  have : IsSimpleGroup PSL(2, GaloisField q m) := isSimpleGroup_psl_pt hq5 hm
  have : IsSimpleGroup L := e.isSimpleGroup
  rw [← Subgroup.isPerfect_iff, Group.isPerfect_def]
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (commutator L) with h | h
  · exfalso
    obtain ⟨l, hl1⟩ := exists_ne (1 : L)
    refine hl1 (Subtype.ext (eq_one_of_commute_of_mulEquiv_psl_two e l.2 fun g hg => ?_))
    have hmem : ⁅(⟨g, hg⟩ : L), l⁆ ∈ commutator L := by
      rw [_root_.commutator_def]
      exact commutator_mem_commutator (mem_top _) (mem_top _)
    rw [h, mem_bot, commutatorElement_eq_one_iff_mul_comm] at hmem
    exact congrArg Subtype.val hmem
  · exact h

private theorem commutator_eq_bot_of_pt [Fact p.Prime] (hG : FrobGlobal G)
    (hloc : CFSG.AGLEmbedding.D1Local p P M) {n : ℕ} (hp5 : 5 ≤ p) (hn : 3 ≤ n)
    {J O : Subgroup G} (hOJ : O ≤ J) (hOM : O ≤ M) (hJM : ¬ J ≤ M)
    (hodd : Odd (Nat.card O)) (hpO : ¬ p ∣ Nat.card O) (hJJ : ⁅J, J⁆ = J)
    {Q : Type} [Group Q] (ψ : J →* Q) (hψ : Function.Surjective ψ)
    (hker : ψ.ker = O.subgroupOf J) (he : Nonempty (Q ≃* PSL(2, GaloisField p n))) :
    ⁅J, O⁆ = ⊥ := by
  by_contra hne
  obtain ⟨q, D, hq, hDO, hDn, hDp, hrank⟩ :=
    criticalRankFour G p hp5 n hn J O hOJ hodd hpO hJJ Q ψ hψ hker he hne
  have hq2 : q ≠ 2 := by
    rintro rfl
    obtain ⟨E, hED, -, hEcard⟩ := CFSG.PreuniquenessRankFour.Helpers.pRank_attained 2 hq D
    have h2E : 2 ∣ Nat.card E := by
      rw [hEcard]
      exact dvd_pow_self 2 (by omega)
    have h2O : 2 ∣ Nat.card O := h2E.trans (card_dvd_of_le (hED.trans hDO))
    exact (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr h2O)
  haveI : Fact q.Prime := ⟨hq⟩
  have hDJ : D ≤ J := hDO.trans hOJ
  have hDM : D ≤ M := hDO.trans hOM
  have hJD : J ≤ normalizer (D : Set G) := (normal_subgroupOf_iff_le_normalizer hDJ).mp hDn
  exact pt_keyF hG hloc hq2 hDp hDM hrank hJM hJD

theorem pt_Kx_central [Fact p.Prime] (hG : FrobGlobal G) (hl : PtPoint p P M x) {n : ℕ}
    {R : Sylow p (RedCent p x)} {K : Subgroup (RedCent p x)} (hD : PtData p n P M x R K) :
    ptKx p x K ⊓ GLBPrimeCore p (centralizer ({x} : Set G)) ≤
      centralizer ((ptKx p x K : Subgroup G) : Set G) := by
  have hp5 : 5 ≤ p := hl.p5
  have hn : 3 ≤ n := hD.three_le
  obtain ⟨e⟩ := hD.equiv
  have hKp : ⁅K, K⁆ = K := commutator_eq_self_psl_pt hp5 hn e
  have hmapK := ptKx_map p x hKp
  have hJC : ptKx p x K ≤ centralizer ({x} : Set G) := ptKx_le_centralizer p x K
  let ψ₀ : ptKx p x K →* RedCent p x :=
    (QuotientGroup.mk' (primeComplementCore (G := centralizer ({x} : Set G)) p)).comp
      (Subgroup.inclusion hJC)
  have hψ₀ : ∀ j : ptKx p x K, ψ₀ j ∈ K := by
    intro j
    have hmem : QuotientGroup.mk' (primeComplementCore (G := centralizer ({x} : Set G)) p)
        (Subgroup.inclusion hJC j) ∈ ((ptKx p x K).subgroupOf (centralizer ({x} : Set G))).map
        (QuotientGroup.mk' (primeComplementCore (G := centralizer ({x} : Set G)) p)) :=
      Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.mpr j.2)
    rw [hmapK] at hmem
    exact hmem
  let ψ : ptKx p x K →* K := ψ₀.codRestrict K hψ₀
  have hψsurj : Function.Surjective ψ := by
    intro k
    have hk : (k : RedCent p x) ∈ ((ptKx p x K).subgroupOf (centralizer ({x} : Set G))).map
        (QuotientGroup.mk' (primeComplementCore (G := centralizer ({x} : Set G)) p)) := by
      rw [hmapK]
      exact k.2
    obtain ⟨c, hc, hck⟩ := Subgroup.mem_map.mp hk
    refine ⟨⟨(c : G), Subgroup.mem_subgroupOf.mp hc⟩, Subtype.ext ?_⟩
    exact hck
  have hN : primeComplementCore (G := centralizer ({x} : Set G)) p =
      (GLBPrimeCore p (centralizer ({x} : Set G))).subgroupOf (centralizer ({x} : Set G)) :=
    (glbPrimeCore_subgroupOf p _).symm
  have hker : ψ.ker = (ptKx p x K ⊓ GLBPrimeCore p (centralizer ({x} : Set G))).subgroupOf
      (ptKx p x K) := by
    ext j
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, Subgroup.mem_inf]
    have hj : (j : G) ∈ ptKx p x K := j.2
    constructor
    · intro h
      have h' : QuotientGroup.mk' (primeComplementCore (G := centralizer ({x} : Set G)) p)
          (Subgroup.inclusion hJC j) = 1 := congrArg Subtype.val h
      rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, hN, Subgroup.mem_subgroupOf,
        Subgroup.coe_inclusion] at h'
      exact ⟨hj, h'⟩
    · rintro ⟨-, h⟩
      apply Subtype.ext
      show QuotientGroup.mk' (primeComplementCore (G := centralizer ({x} : Set G)) p)
          (Subgroup.inclusion hJC j) = 1
      rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, hN, Subgroup.mem_subgroupOf,
        Subgroup.coe_inclusion]
      exact h
  have hOM : ptKx p x K ⊓ GLBPrimeCore p (centralizer ({x} : Set G)) ≤ M :=
    inf_le_right.trans (IsPPoint.primeCore_le hl.loc hl.point)
  have hJM : ¬ ptKx p x K ≤ M := ptKx_not_le hD.red
  have hD1 : CFSG.AGLEmbedding.D1Global G :=
    ⟨hG.simple, hG.nonab, hG.kProper, hG.charTwo, hG.rank, hG.pre⟩
  have hcore2 := IsPPoint.not_two_dvd_card_primeCore hD1 hG.d1 hl.loc hl.point
  have hcoreodd : Odd (Nat.card (GLBPrimeCore p (centralizer ({x} : Set G)))) :=
    Nat.not_even_iff_odd.mp (fun h2 => hcore2 (even_iff_two_dvd.mp h2))
  have hodd : Odd (Nat.card ↥(ptKx p x K ⊓ GLBPrimeCore p (centralizer ({x} : Set G)))) :=
    hcoreodd.of_dvd_nat (card_dvd_of_le inf_le_right)
  have hpO : ¬ p ∣ Nat.card ↥(ptKx p x K ⊓ GLBPrimeCore p (centralizer ({x} : Set G))) :=
    (Nat.Prime.coprime_iff_not_dvd (Fact.out : p.Prime)).mp
      (Nat.Coprime.coprime_dvd_right (card_dvd_of_le inf_le_right)
        (glbPrimeCore_coprime p _))
  have hJO : ⁅ptKx p x K, ptKx p x K ⊓ GLBPrimeCore p (centralizer ({x} : Set G))⁆ = ⊥ :=
    commutator_eq_bot_of_pt hG hl.loc hp5 hn inf_le_left hOM hJM hodd hpO
      (ptKx_perfect p x K) ψ hψsurj hker ⟨e⟩
  rw [commutator_comm] at hJO
  exact commutator_eq_bot_iff_le_centralizer.mp hJO

end CFSG.LocalAnalysis.RankFourTheoremC.PPointFrobenius

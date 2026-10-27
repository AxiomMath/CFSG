module

public import CFSG.LocalAnalysis.RankFourTheoremC.PPointSetup
public import CFSG.LocalAnalysis.AGLEmbedding.ReducedQuotient
import CFSG.LocalAnalysis.RankFourTheoremC.Equivalence
import CFSG.LocalAnalysis.RankFourTheoremC.FullCoreBridge
import CFSG.LocalAnalysis.RankThreeTheoremC.TransitivityReduction
import CFSG.LocalAnalysis.RankThreeTheoremC.ObstructionElements
import CFSG.LocalAnalysis.AGLEmbedding.CentralComponent

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC

open CFSG.Open CFSG.AGLEmbedding CFSG.AGLEmbeddingD2 CFSG.RankThreeCoreUniqueness.Helpers
  CFSG.LocalAnalysis.RankThreeTheoremC Subgroup

variable {G : Type} [Group G] [Finite G]

abbrev RedCent (p : ℕ) (x : G) : Type :=
  centralizer ({x} : Set G) ⧸ primeComplementCore (G := centralizer ({x} : Set G)) p

@[expose] noncomputable def redCentM (p : ℕ) (M : Subgroup G) (x : G) : Subgroup (RedCent p x) :=
  ((centralizer ({x} : Set G) ⊓ M).subgroupOf (centralizer ({x} : Set G))).map
    (QuotientGroup.mk' (primeComplementCore (G := centralizer ({x} : Set G)) p))

namespace IsPPoint

variable {p : ℕ} {P : Sylow p G} {M : Subgroup G} {x : G}

theorem primeCore_le (hloc : D1Local p P M) (h : IsPPoint p P M x) :
    GLBPrimeCore p (centralizer ({x} : Set G)) ≤ M :=
  CFSG.PreuniquenessRankFour.Helpers.intersecting_local_primeCore_le p hloc.beta.1 P
    (sylow_le_of_core hloc) hloc.core (by rw [inf_comm]; exact h.elem.2.2.1)

theorem not_two_dvd_card_primeCore (hS : D1Global G) (hD1 : D1For G) (hloc : D1Local p P M)
    (h : IsPPoint p P M x) : ¬ 2 ∣ Nat.card (GLBPrimeCore p (centralizer ({x} : Set G))) := by
  have hprime := hloc.beta.1
  have : Fact p.Prime := ⟨hprime⟩
  set C : Subgroup G := centralizer ({x} : Set G) with hC
  set O : Subgroup G := GLBPrimeCore p C with hO
  have hOM : O ≤ M := h.primeCore_le hloc
  have hOC : O ≤ C := glbPrimeCore_le p C
  have hCO : C ≤ normalizer (O : Set G) := le_normalizer_glbPrimeCore p C
  have hQp : IsPGroup p ((P : Subgroup G) ⊓ C : Subgroup G) := P.isPGroup'.to_inf_left
  intro h2
  obtain ⟨T, hT⟩ := CFSG.ABGLocalTools.exists_isSylowOf 2 O
  have hTne : T ≠ ⊥ := by
    intro hbot
    have hc := hT.card_eq
    rw [hbot, Subgroup.card_bot] at hc
    have hf : 1 ≤ (Nat.card O).factorization 2 :=
      (Nat.prime_two.dvd_iff_one_le_factorization Nat.card_pos.ne').1 h2
    have : 2 ≤ 2 ^ (Nat.card O).factorization 2 :=
      Nat.le_self_pow (by omega) 2 |>.trans (Nat.pow_le_pow_right (by norm_num) hf)
    omega
  have hNT : normalizer (T : Set G) ≤ M :=
    normalizer_le_of_isSylowOf_two_of_le (theoremD1_of_d1For hS.rank hD1)
      (mem_sigmaA_of_mem_betaFour hloc.beta) hloc.isCoreMaxLocal
      (inf_le_left.trans (sylow_le_of_core hloc)) hQp
      (h.three_le) hOM (inf_le_right.trans hCO) (glbPrimeCore_coprime p C) hT hTne
  have hfr : C ≤ O ⊔ normalizer (T : Set G) := le_sup_normalizer_of_isSylowOf hCO hT
  exact h.elem.2.2.2 (hfr.trans (sup_le hOM hNT))

end IsPPoint

theorem fullCore_map_le_map_inf_of_coprime (hFC : FullCoreLocality G) {p : ℕ} {P : Sylow p G}
    {M : Subgroup G} (hloc : D1Local p P M) {H R : Subgroup G} (hRP : R ≤ P) (hRH : R ≤ H)
    (O : Subgroup H) [O.Normal] (hO : p.Coprime (Nat.card O))
    (hOM : O ≤ (H ⊓ M).subgroupOf H) :
    GLBCore p 2 ((R.subgroupOf H).map (QuotientGroup.mk' O)) ≤
      ((H ⊓ M).subgroupOf H).map (QuotientGroup.mk' O) := by
  have hp := hloc.beta.1
  have hR : IsPGroup p (R.subgroupOf H) := (P.isPGroup'.to_le hRP).comap_subtype
  have hRG : (R.subgroupOf H).map H.subtype ≤ P :=
    (Subgroup.map_subgroupOf_eq_of_le hRH).le.trans hRP
  refine (CFSG.PreuniquenessRankFour.Helpers.fullCore_le_iff p 2 _ _).mpr fun Qbar hQR hQ2 => ?_
  obtain ⟨Q, hQR', rfl⟩ : ∃ Q ≤ R.subgroupOf H, Q.map (QuotientGroup.mk' O) = Qbar :=
    ⟨_, inf_le_right, map_comap_inf_eq _ hQR⟩
  rw [pRank_map_mk_eq_pRank_map_subtype hp O hO] at hQ2
  have hQG : (Q.map H.subtype) ≤ P := (Subgroup.map_mono hQR').trans hRG
  have hN : Subgroup.normalizer ((Q.map H.subtype : Subgroup G) : Set G) ≤ M :=
    normalizer_le_of_two_le_pRank hFC hloc (P.isPGroup'.to_le hQG)
      (hQG.trans (sylow_le_of_core hloc)) hQ2
  have hNH : Subgroup.normalizer (Q : Set H) ≤ (H ⊓ M).subgroupOf H := fun n hn =>
    Subgroup.mem_subgroupOf.mpr
      ⟨n.property, hN (Subgroup.le_normalizer_map H.subtype ⟨n, hn, rfl⟩)⟩
  exact le_map_of_comap_le (QuotientGroup.mk'_surjective O)
    ((comap_normalizer_map_le_sup hp O hO (hR.to_le hQR')).trans (sup_le hOM hNH))

namespace IsPPoint

variable {p : ℕ} {P : Sylow p G} {M : Subgroup G} {x : G}

theorem reducedNongeneration (hloc : D1Local p P M) (h : IsPPoint p P M x) :
    ∃ (T : Sylow p (centralizer ({x} : Set G))) (Tbar : Sylow p (RedCent p x)),
      (T : Subgroup (centralizer ({x} : Set G))).map (centralizer ({x} : Set G)).subtype =
          (P : Subgroup G) ⊓ centralizer ({x} : Set G) ∧
      (Tbar : Subgroup (RedCent p x)) = (T : Subgroup (centralizer ({x} : Set G))).map
          (QuotientGroup.mk' (primeComplementCore (G := centralizer ({x} : Set G)) p)) ∧
      ReducedNongeneration p (RedCent p x) Tbar (redCentM p M x) := by
  obtain ⟨T, hT⟩ := h.sylow
  obtain ⟨Tbar, hTbar, hred⟩ := reducedNongeneration_of_not_le hloc.beta.1 hloc.beta.2.1 P
    (sylow_le_of_core hloc) hloc.core h.elem.2.2.2 T (hT ▸ inf_le_left)
    (by rw [hT]; exact h.three_le) (h.primeCore_le hloc)
  exact ⟨T, Tbar, hT, hTbar, hred⟩

theorem central_xbar (hloc : D1Local p P M) (h : IsPPoint p P M x) :
    QuotientGroup.mk' (primeComplementCore (G := centralizer ({x} : Set G)) p)
        ⟨x, mem_centralizer_singleton_iff.2 rfl⟩ ∈ center (RedCent p x) ∧
      orderOf (QuotientGroup.mk' (primeComplementCore (G := centralizer ({x} : Set G)) p)
        ⟨x, mem_centralizer_singleton_iff.2 rfl⟩) = p :=
  ⟨mk_mem_center_centralizer _ rfl, orderOf_mk_of_coprime hloc.beta.1 _
    (primeComplementCore_coprime p) (by rw [← Subgroup.orderOf_coe]; exact h.elem.2.1)⟩

end IsPPoint

structure PPointReduced (p : ℕ) (M : Subgroup G) (x : G) (R : Sylow p (RedCent p x))
    (K : Subgroup (RedCent p x)) : Prop where
  red : ReducedNongeneration p (RedCent p x) R (redCentM p M x)
  fullCore : GLBCore p 2 (R : Subgroup (RedCent p x)) ≤ redCentM p M x
  component : IsComponentOf K ⊤
  normal : K.Normal
  unique : ∀ L, IsComponentOf L ⊤ → L = K
  not_le : ¬ K ≤ redCentM p M x
  cyclic : IsCyclic ((R : Subgroup (RedCent p x)) ⊓ centralizer (K : Set (RedCent p x)) :
    Subgroup (RedCent p x))

namespace IsPPoint

variable {p : ℕ} {P : Sylow p G} {M : Subgroup G} {x : G}

theorem exists_pPointReduced (hFC : FullCoreLocality G) (hloc : D1Local p P M)
    (h : IsPPoint p P M x) :
    ∃ (R : Sylow p (RedCent p x)) (K : Subgroup (RedCent p x)), PPointReduced p M x R K ∧
      (R : Subgroup (RedCent p x)) = (((P : Subgroup G) ⊓ centralizer ({x} : Set G)).subgroupOf
        (centralizer ({x} : Set G))).map
          (QuotientGroup.mk' (primeComplementCore (G := centralizer ({x} : Set G)) p)) := by
  have hp := hloc.beta.1
  have hodd := hloc.beta.2.1
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨T, Tbar, hT, hTbar, hred⟩ := h.reducedNongeneration hloc
  obtain ⟨hzc, hzp⟩ := h.central_xbar hloc
  set X₀ : Subgroup (RedCent p x) := redCentM p M x with hX₀
  have hOM : primeComplementCore (G := centralizer ({x} : Set G)) p ≤
      ((centralizer ({x} : Set G)) ⊓ M).subgroupOf (centralizer ({x} : Set G)) := by
    rw [← glbPrimeCore_subgroupOf]
    exact glbPrimeCore_subgroupOf_le_inf (h.primeCore_le hloc)
  have hTeq : (T : Subgroup (centralizer ({x} : Set G))) =
      ((P : Subgroup G) ⊓ centralizer ({x} : Set G)).subgroupOf (centralizer ({x} : Set G)) := by
    rw [← hT, Subgroup.subgroupOf, Subgroup.comap_map_eq_self_of_injective
      (centralizer ({x} : Set G)).subtype_injective]
  have hfull : GLBCore p 2 (Tbar : Subgroup (RedCent p x)) ≤ X₀ := by
    rw [hTbar, hTeq]
    exact fullCore_map_le_map_inf_of_coprime hFC hloc inf_le_left inf_le_right _
      (primeComplementCore_coprime p) hOM
  have hRX₀ : (Tbar : Subgroup (RedCent p x)) ≤ X₀ :=
    (CFSG.PreuniquenessRankFour.Helpers.subgroup_le_weakCore_of_rank p hp _
      hred.three_le_pRank).trans hred.weakCore_le
  have hpR : CFSG.pCore p (RedCent p x) ≤ Tbar :=
    sSup_le fun K ⟨hKn, hKp⟩ => @IsPGroup.le_sylow_of_normal _ _ _ K hKn hKp Tbar
  have hF : fittingSubgroup (RedCent p x) ≤ X₀ := by
    rw [CFSG.Fitting_eq_pcore _ p hred.core_eq_bot]
    exact hpR.trans hRX₀
  have hlayer : CFSG.layer (RedCent p x) ≠ ⊥ := by
    intro hbot
    have hFstar : CFSG.generalizedFitting (RedCent p x) = CFSG.pCore p (RedCent p x) := by
      rw [CFSG.generalizedFitting, hbot, sup_bot_eq, CFSG.Fitting_eq_pcore _ p hred.core_eq_bot]
    have hNn : (CFSG.pCore p (RedCent p x)).Normal := CFSG.pCore_normal
    by_cases hN2 : 2 ≤ Open.pRank p (CFSG.pCore p (RedCent p x))
    · have hN := (CFSG.PreuniquenessRankFour.Helpers.fullCore_le_iff p 2 _ _).mp hfull _ hpR hN2
      rw [Subgroup.normalizer_eq_top] at hN
      exact hred.ne_top (top_le_iff.mp hN)
    · have hcyc : IsCyclic (CFSG.pCore p (RedCent p x)) := by
        by_contra hnc
        exact hN2 (two_le_pRank_of_not_isCyclic hp hodd CFSG.pCore_isPGroup hnc)
      have hcent : (Tbar : Subgroup (RedCent p x)) ⊓
          centralizer ((CFSG.pCore p (RedCent p x) : Subgroup _) : Set _) ≤
            CFSG.pCore p (RedCent p x) := by
        have := CFSG.centralizer_generalizedFitting_le (RedCent p x)
        rw [hFstar] at this
        exact inf_le_right.trans this
      obtain ⟨A, hAR, hA, hAc⟩ := CFSG.PreuniquenessRankFour.Helpers.pRank_attained p hp
        (Tbar : Subgroup (RedCent p x))
      have hnorm : (Tbar : Subgroup (RedCent p x)) ≤
          normalizer ((CFSG.pCore p (RedCent p x) : Subgroup _) : Set _) := by
        rw [Subgroup.normalizer_eq_top]
        exact le_top
      have hle := card_le_of_isCyclic_of_centralizer_le hodd Tbar.isPGroup' hpR hnorm hcent hcyc
        hAR hA
      rw [hAc] at hle
      have := (Nat.pow_le_pow_iff_right hp.one_lt).1 hle
      have h3 := hred.three_le_pRank
      omega
  obtain ⟨K₀, hK₀⟩ := exists_isComponentOf_of_layer_ne_bot hlayer
  have hzF : QuotientGroup.mk' (primeComplementCore (G := centralizer ({x} : Set G)) p)
      ⟨x, mem_centralizer_singleton_iff.2 rfl⟩ ∈ CFSG.generalizedFitting (RedCent p x) :=
    Subgroup.mem_sup_left (CFSG.pCore_le_fitting _ p (mem_pCore_of_mem_center hzc hzp))
  have hrank2 : 2 ≤ Open.pRank p ((Tbar : Subgroup (RedCent p x)) ⊓
      CFSG.generalizedFitting (RedCent p x)) := by
    obtain ⟨t, ⟨htR, htK⟩, ht, htZ⟩ :=
      exists_mem_sylow_inf_component hp hodd hred.core_eq_bot Tbar hK₀
    have htp : t ^ p = 1 := by
      have := pow_orderOf_eq_one t
      rwa [ht] at this
    exact two_le_pRank_of_commute_of_not_mem_zpowers hp hzp htp
      (fun ht' => htZ (Subgroup.zpowers_le.mpr (Subgroup.center_le_centralizer _ hzc) ht'))
      (Subgroup.mem_center_iff.mp hzc t).symm ⟨mem_sylow_of_mem_center hzc hzp Tbar, hzF⟩
      ⟨htR, Subgroup.mem_sup_right (le_layer_of_isComponentOf hK₀ htK)⟩
  have hFn : (CFSG.generalizedFitting (RedCent p x)).Normal :=
    CFSG.LocalCores.generalized_fitting_characteristic.2
  have hNX : normalizer (((Tbar : Subgroup (RedCent p x)) ⊓
      CFSG.generalizedFitting (RedCent p x) : Subgroup (RedCent p x)) : Set (RedCent p x)) ≤
        X₀ :=
    (CFSG.PreuniquenessRankFour.Helpers.fullCore_le_iff p 2 _ _).mp hfull _ inf_le_left hrank2
  have hnotF := not_le_of_normalizer_inf_le Tbar hNX hred.ne_top
  have hnotE : ¬ CFSG.layer (RedCent p x) ≤ X₀ := fun hE => hnotF (sup_le hF hE)
  obtain ⟨K, hK, hKX₀⟩ : ∃ K, IsComponentOf K ⊤ ∧ ¬ K ≤ X₀ := by
    by_contra hall
    push Not at hall
    exact hnotE (sSup_le fun L hL => hall L ((CFSG.isComponent_iff_open L).mp hL))
  refine ⟨Tbar, K, ⟨hred, hfull, hK, hred.normal_of_isComponentOf_of_center hzc hzp hK,
    fun L hL => hred.eq_of_isComponentOf_of_center hzc hzp hL hK, hKX₀, ?_⟩, by rw [hTbar, hTeq]⟩
  by_contra hnc
  have hY2 := two_le_pRank_of_not_isCyclic hp hodd
    (Tbar.isPGroup'.to_inf_left : IsPGroup p ↥((Tbar : Subgroup (RedCent p x)) ⊓
      centralizer (K : Set (RedCent p x)))) hnc
  have hNY := (CFSG.PreuniquenessRankFour.Helpers.fullCore_le_iff p 2 _ _).mp hfull _
    inf_le_left hY2
  exact hKX₀ ((Subgroup.le_centralizer_iff.mp inf_le_right).trans
    ((Subgroup.centralizer_le_normalizer _).trans hNY))

end IsPPoint

end CFSG.LocalAnalysis.RankFourTheoremC

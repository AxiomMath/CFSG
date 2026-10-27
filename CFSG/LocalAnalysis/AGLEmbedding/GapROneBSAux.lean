module

public import CFSG.LocalAnalysis.AGLEmbedding.IIIaResidualDefs
public import CFSG.LocalAnalysis.AGLEmbeddingD2.NoXBlock
import CFSG.LocalAnalysis.AGLEmbedding.LinTwoTorusFacts
import CFSG.LocalAnalysis.AGLEmbedding.OddCoreRank
import CFSG.LocalAnalysis.AGLEmbedding.ResidualFiveOddCore
import CFSG.LocalAnalysis.AGLEmbedding.WeakBlockStructure
public import CFSG.LocalAnalysis.AGLEmbedding.TwoCoreObstruction
import CFSG.LocalAnalysis.AGLEmbedding.ComponentRank
import CFSG.LocalAnalysis.AGLEmbedding.ResidualToolsAux

public section

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.PreuniquenessRankFour.Helpers
open CFSG.AGLEmbeddingD2 (NoXBlockFor)

section Abstract

variable {Y : Type*} [Group Y] [Finite Y]

theorem pCore_le_pPrimeCore_two {l : ℕ} (hl : l.Prime) (hl2 : l ≠ 2) :
    CFSG.pCore l Y ≤ CFSG.pPrimeCore 2 Y := by
  have := Fact.mk hl
  refine le_sSup ⟨inferInstance, ?_⟩
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp (CFSG.pCore_isPGroup (p := l) (G := Y))
  rw [hk]
  exact Nat.Coprime.pow_right k ((Nat.coprime_primes Nat.prime_two hl).mpr (Ne.symm hl2))

theorem le_pCore_of_le_centralizer_components {p : ℕ} {A : Subgroup Y} (hA : IsPGroup p A)
    (hcomp : ∀ L : Subgroup Y, IsComponentOf L ⊤ → A ≤ Subgroup.centralizer (L : Set Y))
    (hcore : ∀ l : ℕ, l.Prime → A ≤ Subgroup.centralizer (CFSG.pCore l Y : Set Y)) :
    A ≤ CFSG.pCore p Y := by
  set Fs := CFSG.ComponentClassification.GeneralizedFitting.subgroup Y with hFs
  have hFsC : Fs ≤ Subgroup.centralizer (A : Set Y) := by
    refine sup_le (sSup_le fun N hN => ?_) (sSup_le fun L hL => ?_)
    · refine (CFSG.normal_nilpotent_le_sup_pCore hN.1 hN.2).trans (iSup_le fun l => ?_)
      exact Subgroup.le_centralizer_iff.mp (hcore _ (Nat.prime_of_mem_primeFactors l.1.2))
    · exact Subgroup.le_centralizer_iff.mp (hcomp L hL)
  have hAC : A ≤ Subgroup.centralizer (Fs : Set Y) := Subgroup.le_centralizer_iff.mp hFsC
  have hAF : A ≤ Fs :=
    hAC.trans (CFSG.ComponentClassification.GeneralizedFitting.centralizer_le Y)
  have : Fs.Normal := CFSG.ComponentClassification.GeneralizedFitting.normal Y
  have hWn : (Fs ⊓ Subgroup.centralizer (Fs : Set Y)).Normal := Subgroup.normal_inf_normal _ _
  exact le_pCore_of_isPGroup_of_le_commutative_normal hWn
    (fun x hx y hy => Subgroup.mem_centralizer_iff.mp hy.2 x hx.1) (le_inf hAF hAC) hA

end Abstract

section Preimage

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem preimage_subgroupOf_eq_comap {M : Subgroup G} (T : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M)) :
    ((T.comap (QuotientGroup.mk' (CFSG.pCore 2 ↥M))).map M.subtype).subgroupOf M =
      T.comap (QuotientGroup.mk' (CFSG.pCore 2 ↥M)) :=
  Subgroup.comap_map_eq_self_of_injective M.subtype_injective _

omit [Finite G] in
theorem barM_preimage {M : Subgroup G} (T : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M)) :
    barM M ((T.comap (QuotientGroup.mk' (CFSG.pCore 2 ↥M))).map M.subtype) = T := by
  rw [barM, preimage_subgroupOf_eq_comap,
    Subgroup.map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective _)]

omit [Finite G] in
theorem normal_preimage_subgroupOf {M : Subgroup G} (T : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M))
    [T.Normal] :
    (((T.comap (QuotientGroup.mk' (CFSG.pCore 2 ↥M))).map M.subtype).subgroupOf M).Normal := by
  rw [preimage_subgroupOf_eq_comap]
  exact Subgroup.Normal.comap inferInstance _

theorem TwoLocalPhaseThree.preimage_le_inf {M H : Subgroup G}
    (h : TwoLocalPhaseThree M H) {T : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M)}
    (hT : T ≤ barM M (H ⊓ M)) :
    (T.comap (QuotientGroup.mk' (CFSG.pCore 2 ↥M))).map M.subtype ≤ H ⊓ M := by
  have hQK : pCoreOf 2 M ≤ H ⊓ M :=
    le_inf ((h.twoCore_M_le h.twoCore_inf).trans (pCoreOf_le 2 H)) (pCoreOf_le 2 M)
  rintro _ ⟨m, hm, rfl⟩
  obtain ⟨k, hk, hkm⟩ := hT hm
  have h1 : QuotientGroup.mk' (CFSG.pCore 2 ↥M) (k⁻¹ * m) = 1 := by
    rw [map_mul, map_inv, hkm, inv_mul_cancel]
  have h2 : (m : G) = (k : G) * ((k⁻¹ * m : M) : G) := by simp
  show (m : G) ∈ H ⊓ M
  rw [h2]
  exact (H ⊓ M).mul_mem (Subgroup.mem_subgroupOf.mp hk)
    (hQK (coe_mem_pCoreOf_two_of_mk_eq_one _ h1))

theorem D1PhaseThree.preimage_le_inf {p : ℕ} {P : Sylow p G} {M H R : Subgroup G}
    (h : D1PhaseThree p P M H R) {T : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M)}
    (hT : T ≤ barM M (H ⊓ M)) :
    (T.comap (QuotientGroup.mk' (CFSG.pCore 2 ↥M))).map M.subtype ≤ H ⊓ M :=
  h.toTwoLocalPhaseThree.preimage_le_inf hT

theorem TwoLocalPhaseThree.preimage_le_glbPrimeCore_or_le {M H X : Subgroup G}
    (h : TwoLocalPhaseThree M H) (hK : Open.IsKGroup ↥M) {p : ℕ}
    (hdich : ∀ Y : Subgroup G, Y ≤ H ⊓ M → H ⊓ M ≤ Subgroup.normalizer (Y : Set G) →
      Y ≤ GLBPrimeCore p H ∨ X ≤ Y)
    (h84 : Asc81bEightFour) (hD2 : NoXBlockFor G) {T : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M)}
    [T.Normal] (hT : T ≤ CFSG.pPrimeCore 2 (↥M ⧸ CFSG.pCore 2 ↥M)) :
    (T.comap (QuotientGroup.mk' (CFSG.pCore 2 ↥M))).map M.subtype ≤ GLBPrimeCore p H ∨
      X ≤ (T.comap (QuotientGroup.mk' (CFSG.pCore 2 ↥M))).map M.subtype :=
  hdich _ (h.preimage_le_inf (h.le_barM_inf_of_le_centralizer
      (hT.trans (h.oddCore_le_centralizer hK h84 hD2))))
    (inf_le_right.trans ((Subgroup.normal_subgroupOf_iff_le_normalizer
      (Subgroup.map_subtype_le _)).mp (normal_preimage_subgroupOf T)))

theorem TwoLocalPhaseThree.pCore_eq_bot_or_le {M H X : Subgroup G} (h : TwoLocalPhaseThree M H)
    (hK : Open.IsKGroup ↥M) {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2)
    (hdich : ∀ Y : Subgroup G, Y ≤ H ⊓ M → H ⊓ M ≤ Subgroup.normalizer (Y : Set G) →
      Y ≤ GLBPrimeCore p H ∨ X ≤ Y)
    (h84 : Asc81bEightFour) (hD2 : NoXBlockFor G) :
    CFSG.pCore p (↥M ⧸ CFSG.pCore 2 ↥M) = ⊥ ∨
      barM M X ≤ CFSG.pCore p (↥M ⧸ CFSG.pCore 2 ↥M) := by
  have hp : p.Prime := Fact.out
  rcases h.preimage_le_glbPrimeCore_or_le hK hdich h84 hD2 (pCore_le_pPrimeCore_two hp hp2)
    with hYN | hXY
  · refine Or.inl (eq_bot_iff.mpr fun σ hσ => ?_)
    obtain ⟨m, rfl⟩ := QuotientGroup.mk'_surjective (CFSG.pCore 2 ↥M) σ
    have hmN : (m : G) ∈ GLBPrimeCore p H := hYN ⟨m, hσ, rfl⟩
    obtain ⟨k, hk⟩ := CFSG.pCore_isPGroup (p := p) (G := ↥M ⧸ CFSG.pCore 2 ↥M) ⟨_, hσ⟩
    have hord1 : orderOf (QuotientGroup.mk' (CFSG.pCore 2 ↥M) m) ∣ p ^ k :=
      orderOf_dvd_of_pow_eq_one (by simpa using congrArg Subtype.val hk)
    have hord2 : orderOf (QuotientGroup.mk' (CFSG.pCore 2 ↥M) m) ∣
        Nat.card (GLBPrimeCore p H) :=
      (orderOf_map_dvd _ _).trans (by
        rw [← Subgroup.orderOf_coe]
        exact Subgroup.orderOf_dvd_natCard _ hmN)
    exact Subgroup.mem_bot.mpr (orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes
      (Nat.Coprime.pow_left k (glbPrimeCore_coprime p H)) hord1 hord2))
  · exact Or.inr (barM_le_of_le_preimage hXY)

theorem TwoLocalPhaseThree.le_pCore_of_forall_le_centralizer {M H X : Subgroup G}
    (h : TwoLocalPhaseThree M H) (hK : Open.IsKGroup ↥M) {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2)
    (hdich : ∀ Y : Subgroup G, Y ≤ H ⊓ M → H ⊓ M ≤ Subgroup.normalizer (Y : Set G) →
      Y ≤ GLBPrimeCore p H ∨ X ≤ Y)
    (hXe : IsElemAbelian p (barM M X)) (h84 : Asc81bEightFour) (hD2 : NoXBlockFor G)
    (hcomp : ∀ Lbar : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M), IsComponentOf Lbar ⊤ →
      barM M X ≤ Subgroup.centralizer (Lbar : Set _))
    (hodd : ∀ s : ℕ, s.Prime → s ≠ 2 → s ≠ p → barM M X ≤ Subgroup.centralizer
      ((CFSG.pCore s (↥M ⧸ CFSG.pCore 2 ↥M) : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M)) : Set _)) :
    barM M X ≤ CFSG.pCore p (↥M ⧸ CFSG.pCore 2 ↥M) := by
  rcases h.pCore_eq_bot_or_le hK hp2 hdich h84 hD2 with hOp | hle
  · have hXp : IsPGroup p (barM M X) := fun x =>
      ⟨1, Subtype.ext (by simpa using hXe.2 x x.2)⟩
    refine le_pCore_of_le_centralizer_components hXp hcomp fun l hl => ?_
    by_cases hl2 : l = 2
    · rw [hl2, pCore_quotient_pCore_eq_bot']
      exact Subgroup.le_centralizer_iff.mp bot_le
    by_cases hlp : l = p
    · rw [hlp, hOp]
      exact Subgroup.le_centralizer_iff.mp bot_le
    exact hodd l hl hl2 hlp
  · exact hle

theorem D1L2Data.preimage_le_glbPrimeCore_or_le {p n : ℕ} [Fact p.Prime] {P : Sylow p G}
    {M H R X : Subgroup G} (h : D1L2Data p n P M H R X) (h84 : Asc81bEightFour)
    (hD2 : D1NoXBlock) {T : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M)} [T.Normal]
    (hT : T ≤ CFSG.pPrimeCore 2 (↥M ⧸ CFSG.pCore 2 ↥M)) :
    (T.comap (QuotientGroup.mk' (CFSG.pCore 2 ↥M))).map M.subtype ≤ GLBPrimeCore p H ∨
      X ≤ (T.comap (QuotientGroup.mk' (CFSG.pCore 2 ↥M))).map M.subtype :=
  h.ph3.toTwoLocalPhaseThree.preimage_le_glbPrimeCore_or_le h.ph3.isKGroup.1 h.normal_dichotomy
    h84 (hD2 G h.ph3.glob) hT

end Preimage

section LemmaU

variable {G : Type} [Group G] [Finite G]

theorem mem_glbBetaFour_of_le_pRank {s : ℕ} (hs : s.Prime) (hs2 : s ≠ 2) {M A : Subgroup G}
    (hM : IsTwoLocal M) (hAM : A ≤ M) (h4 : 4 ≤ Open.pRank s A) : s ∈ GLBBetaFour G := by
  have hM4 : 4 ≤ Open.pRank s M := h4.trans (pRank_mono s hs hAM)
  exact ⟨hs, hs2, prime_dvd_card_of_positive_rank s hs M (by omega),
    hM4.trans (le_csSup (twoLocalRank_bddAbove s hs) ⟨M, hM, rfl⟩)⟩

theorem D1PhaseThree.false_of_preimage_le {p : ℕ} {P : Sylow p G} {M H R : Subgroup G}
    (h : D1PhaseThree p P M H R) {s : ℕ} (hs : s.Prime) (hs2 : s ≠ 2)
    (hβ : s ∈ GLBBetaFour G) {T : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M)} [T.Normal]
    (hT : IsPGroup s T)
    (h3 : 3 ≤ Open.pRank s ((T.comap (QuotientGroup.mk' (CFSG.pCore 2 ↥M))).map M.subtype))
    {W : Subgroup G} (hWH : W ≤ H) (hWn : H ≤ Subgroup.normalizer (W : Set G)) (hWM : W ≤ M)
    (hTW : (T.comap (QuotientGroup.mk' (CFSG.pCore 2 ↥M))).map M.subtype ≤ W) : False := by
  have := Fact.mk hs
  set mk := QuotientGroup.mk' (CFSG.pCore 2 ↥M) with hmk
  set Sh : Subgroup G := (T.comap mk).map M.subtype with hSh
  have hShM : Sh ≤ M := Subgroup.map_subtype_le _
  obtain ⟨E, hESh, hE, hEcard⟩ := pRank_attained s hs Sh
  have hEM : E ≤ M := hESh.trans hShM
  obtain ⟨TM, hETM⟩ := ((IsPGroup.of_card hEcard).comap_subtype (K := M)).exists_le_sylow
  obtain ⟨Ts, hTMTs⟩ := ((TM.isPGroup').map M.subtype).exists_le_sylow
  have hETs : E ≤ Ts := fun x hx =>
    hTMTs ⟨⟨x, hEM hx⟩, hETM (Subgroup.mem_subgroupOf.mpr hx), rfl⟩
  have hrank : ∀ K : Subgroup G, E ≤ K → 3 ≤ Open.pRank s K := fun K hEK =>
    h3.trans (le_csSup (pRank_bddAbove s hs K) ⟨E, hEK, hE, hEcard⟩)
  obtain ⟨L, hL, hcoreL⟩ := (h.glob.pre s hβ).2 Ts
  obtain ⟨Ms, hLMs, hMs⟩ := exists_maximal_twoLocal hL
  have hcore : GLBWeakCore s (Ts : Subgroup G) ≤ Ms := hcoreL.trans hLMs
  have hTsMs : (Ts : Subgroup G) ≤ Ms :=
    (subgroup_le_weakCore_of_rank s hs _ (hrank _ hETs)).trans hcore
  have hQMs : pCoreOf 2 M ≤ Ms := intersecting_local_twoCore_le s hs hs2 Ts hTsMs hcore
    (hrank _ (le_inf hEM (hETs.trans hTsMs)))
  have hTTM : T ≤ (TM : Subgroup M).map mk := by
    have hle := hT.le_sylow_of_normal (TM.mapSurjective (QuotientGroup.mk'_surjective _))
    rwa [Sylow.coe_mapSurjective] at hle
  have hShMs : Sh ≤ Ms := by
    rintro _ ⟨m, hm, rfl⟩
    obtain ⟨t, ht, htm⟩ := hTTM hm
    have h1 : mk (t⁻¹ * m) = 1 := by rw [map_mul, map_inv, htm, inv_mul_cancel]
    have h2 : (m : G) = (t : G) * ((t⁻¹ * m : M) : G) := by simp
    show (m : G) ∈ Ms
    rw [h2]
    exact Ms.mul_mem (hTsMs (hTMTs ⟨t, ht, rfl⟩)) (hQMs (coe_mem_pCoreOf_two_of_mk_eq_one _ h1))
  have := normal_preimage_subgroupOf T
  have hShmap : (Sh.subgroupOf M).map M.subtype = Sh := Subgroup.map_subgroupOf_eq_of_le hShM
  have hMMs : M ≤ Ms := normal_subgroup_sylow_rank_forces_containment s hs Ts hTsMs hcore
    (Sh.subgroupOf M) (by rw [hShmap]; exact hShMs) (by rw [hShmap]; exact h3)
  have hMseq : Ms = M := h.maxTwoLocal_M.2 Ms hMs.1 hMMs
  have : (W.subgroupOf H).Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hWH).mpr hWn
  have hWmap : (W.subgroupOf H).map H.subtype = W := Subgroup.map_subgroupOf_eq_of_le hWH
  have hHMs : H ≤ Ms := normal_subgroup_sylow_rank_forces_containment s hs Ts hTsMs hcore
    (W.subgroupOf H) (by rw [hWmap, hMseq]; exact hWM)
    (by rw [hWmap]; exact h3.trans (pRank_mono s hs hTW))
  exact h.not_le (hMseq ▸ hHMs)

end LemmaU

section OddCore

variable {G : Type} [Group G] [Finite G]

theorem D1L2Data.four_le_pRank_oddCore {p n : ℕ} [Fact p.Prime] {P : Sylow p G}
    {M H R X : Subgroup G} (h : D1L2Data p n P M H R X) {s : ℕ} (hs : s.Prime) (hs2 : s ≠ 2)
    (hsp : s ≠ p)
    (hns : ¬ barM M X ≤ Subgroup.centralizer
      ((CFSG.pCore s (↥M ⧸ CFSG.pCore 2 ↥M) : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M)) : Set _)) :
    4 ≤ Open.pRank s (CFSG.pCore s (↥M ⧸ CFSG.pCore 2 ↥M)) := by
  have hp : p.Prime := Fact.out
  have := Fact.mk hs
  set mk := QuotientGroup.mk' (CFSG.pCore 2 ↥M) with hmk
  set Sg := CFSG.pCore s (↥M ⧸ CFSG.pCore 2 ↥M) with hSg
  obtain ⟨r, t, hr, hnr, -, -, -, -, htK, htX, -, -, -, hirr⟩ := stmtPPDElement h
  have hXM : X ≤ M := h.le_R.trans h.ph3.le_M
  have htM : t ∈ M := htK.2
  have hn3 := h.three_le
  have hSgN : (⊤ : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M)) ≤ Subgroup.normalizer (Sg : Set _) :=
    (Subgroup.normalizer_eq_top (H := Sg)).ge
  have hrank : r ≤ Open.pRank s Sg := by
    refine stmtOddCoreRank hs hs2 hp hsp hr Sg (barM M X) (mk ⟨t, htM⟩)
      CFSG.pCore_isPGroup (le_top.trans hSgN) h.isElemAbelian_barM ?_
      (hSgN (Subgroup.mem_top _)) (mem_normalizer_barM htM htX) (fun k hk Y₀ hY₀ hkY₀ => ?_)
      hns
    · rw [h.card_barM]
      exact Nat.pow_le_pow_right hp.pos (by omega)
    · have htk : mk ⟨t, htM⟩ ^ k = mk ⟨t ^ k, M.pow_mem htM k⟩ := by
        rw [← map_pow]
        rfl
      rw [htk] at hkY₀
      exact eq_bot_or_eq_barM_of_mem_normalizer hXM (M.pow_mem htM k)
        (Subgroup.pow_mem _ htX k) (hirr k hk) hY₀ hkY₀
  omega

theorem D1L2Data.false_of_oddCore_not_centralized {p n : ℕ} [Fact p.Prime] {P : Sylow p G}
    {M H R X : Subgroup G} (h : D1L2Data p n P M H R X) (h84 : Asc81bEightFour)
    (hD2 : D1NoXBlock) {s : ℕ} (hs : s.Prime) (hs2 : s ≠ 2) (hsp : s ≠ p)
    (hns : ¬ barM M X ≤ Subgroup.centralizer
      ((CFSG.pCore s (↥M ⧸ CFSG.pCore 2 ↥M) : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M)) : Set _)) :
    False := by
  have hp : p.Prime := Fact.out
  have := Fact.mk hs
  set Sg := CFSG.pCore s (↥M ⧸ CFSG.pCore 2 ↥M) with hSg
  set Sh : Subgroup G := (Sg.comap (QuotientGroup.mk' (CFSG.pCore 2 ↥M))).map M.subtype
    with hSh
  have h4 : 4 ≤ Open.pRank s Sh := by
    have h1 := pRank_barM_le hs hs2 M Sh (Subgroup.map_subtype_le _)
    rw [barM_preimage] at h1
    exact (h.four_le_pRank_oddCore hs hs2 hsp hns).trans h1
  have hShN : Sh ≤ GLBPrimeCore p H := by
    refine (h.preimage_le_glbPrimeCore_or_le h84 hD2
      (pCore_le_pPrimeCore_two hs hs2)).resolve_right fun hXSh => ?_
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp
      (CFSG.pCore_isPGroup (p := s) (G := ↥M ⧸ CFSG.pCore 2 ↥M))
    have hdvd := Subgroup.card_dvd_of_le (barM_le_of_le_preimage hXSh)
    rw [h.card_barM, hk] at hdvd
    have hpdvd : p ∣ s ^ k := (dvd_pow_self p (by have := h.three_le; omega)).trans hdvd
    exact hsp ((Nat.prime_dvd_prime_iff_eq hp hs).mp (hp.dvd_of_dvd_pow hpdvd)).symm
  exact h.ph3.false_of_preimage_le hs hs2
    (mem_glbBetaFour_of_le_pRank hs hs2 h.ph3.maxTwoLocal_M.1 (Subgroup.map_subtype_le _) h4)
    CFSG.pCore_isPGroup ((by norm_num : 3 ≤ 4).trans h4) (glbPrimeCore_le p H)
    (le_normalizer_glbPrimeCore p H) h.ph3.primeCore_le hShN

end OddCore

end CFSG.AGLEmbedding

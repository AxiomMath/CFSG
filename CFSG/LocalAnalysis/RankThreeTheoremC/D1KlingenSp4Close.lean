module

public import CFSG.LocalAnalysis.RankThreeTheoremC.D1KlingenSp4Defs
import CFSG.LocalAnalysis.AGLEmbedding.OneLieNormalClosure
import CFSG.LocalAnalysis.AGLEmbedding.OneSmallSPLK0H1ThmZ
import CFSG.LocalAnalysis.AGLEmbedding.SocleCompetitor
import CFSG.LocalAnalysis.RankThreeTheoremC.D1CaseThree3Families
public import CFSG.LocalAnalysis.AGLEmbedding.CaseThreeKillAux

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.PreuniquenessRankFour.Helpers
open CFSG.RankThreeCoreUniqueness.Helpers CFSG.AGLEmbedding
open CFSG.ComponentClassification.OuterAutomorphisms

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem map_nclIn_eq_of_simple {p : ℕ} [Fact p.Prime] {H R : Subgroup G} (hRH : R ≤ H)
    {K : Subgroup (H ⧸ primeComplementCore (G := H) p)} (hKn : K.Normal)
    (hKs : IsSimpleGroup K)
    (hRK : (R.subgroupOf H).map (QuotientGroup.mk' (primeComplementCore (G := H) p)) ≤ K)
    (hR1 : (R.subgroupOf H).map (QuotientGroup.mk' (primeComplementCore (G := H) p)) ≠ ⊥) :
    ((nclIn H R).subgroupOf H).map (QuotientGroup.mk' (primeComplementCore (G := H) p)) = K := by
  have hJK : nclIn H R ≤
      (K.comap (QuotientGroup.mk' (primeComplementCore (G := H) p))).map H.subtype := by
    refine nclIn_le (fun x hx => ⟨⟨x, hRH hx⟩, ?_, rfl⟩) (Subgroup.map_subtype_le _) ?_
    · exact hRK (Subgroup.mem_map_of_mem _ (show (⟨x, hRH hx⟩ : H) ∈ R.subgroupOf H from hx))
    · refine (Subgroup.normal_subgroupOf_iff_le_normalizer (Subgroup.map_subtype_le _)).mp ?_
      rw [Subgroup.subgroupOf, Subgroup.comap_map_eq_self_of_injective H.subtype_injective]
      exact hKn.comap _
  have hle : ((nclIn H R).subgroupOf H).map
      (QuotientGroup.mk' (primeComplementCore (G := H) p)) ≤ K := by
    rintro _ ⟨j, hj, rfl⟩
    obtain ⟨j', hj', hjj'⟩ := hJK hj
    rwa [← Subtype.ext hjj']
  have hnormal : (((nclIn H R).subgroupOf H).map
      (QuotientGroup.mk' (primeComplementCore (G := H) p))).Normal :=
    (nclIn_normal H R).map _ (QuotientGroup.mk'_surjective _)
  have hne : ((nclIn H R).subgroupOf H).map
      (QuotientGroup.mk' (primeComplementCore (G := H) p)) ≠ ⊥ := by
    intro hbot
    apply hR1
    rw [eq_bot_iff, ← hbot]
    exact Subgroup.map_mono (Subgroup.comap_mono (le_nclIn hRH))
  have := hKs
  have := hnormal
  refine eq_of_le_normalizer_of_isSimpleGroup hle ?_ hne
  rw [Subgroup.normalizer_eq_top]
  exact le_top

theorem exists_competitorHom_aux {p : ℕ} [Fact p.Prime] {T : Type} [Group T] {H X : Subgroup G}
    {K : Subgroup (H ⧸ primeComplementCore (G := H) p)} (e : K ≃* T)
    (hπJ : ((nclIn H X).subgroupOf H).map
      (QuotientGroup.mk' (primeComplementCore (G := H) p)) = K)
    {H' : Subgroup G} (hJH' : nclIn H X ≤ H') :
    ∃ φ : ((nclIn H X).subgroupOf H').map
        (QuotientGroup.mk' (primeComplementCore (G := H') p)) →* T,
      Function.Surjective φ ∧ p.Coprime (Nat.card φ.ker) := by
  have hJH : nclIn H X ≤ H := nclIn_le_self H X
  set ρ := (QuotientGroup.mk' (primeComplementCore (G := H') p)).subgroupMap
    ((nclIn H X).subgroupOf H')
  let θ₀ : (nclIn H X).subgroupOf H' →* H :=
    MonoidHom.codRestrict (H'.subtype.comp ((nclIn H X).subgroupOf H').subtype) H
      (fun a => hJH a.2)
  let θ : (nclIn H X).subgroupOf H' →* H ⧸ primeComplementCore (G := H) p :=
    (QuotientGroup.mk' (primeComplementCore (G := H) p)).comp θ₀
  have hθK : ∀ a, θ a ∈ K := fun a =>
    hπJ ▸ Subgroup.mem_map_of_mem _ (show θ₀ a ∈ (nclIn H X).subgroupOf H from a.2)
  let ψ : (nclIn H X).subgroupOf H' →* T := e.toMonoidHom.comp (θ.codRestrict K hθK)
  have hψker : ∀ a, a ∈ ψ.ker ↔ ((a : H') : G) ∈ GLBPrimeCore p H := by
    intro a
    have h1 : ψ a = 1 ↔ θ a = 1 := by
      simp only [ψ, MonoidHom.coe_comp, Function.comp_apply, MulEquiv.coe_toMonoidHom,
        MulEquiv.map_eq_one_iff]
      rw [← OneMemClass.coe_eq_one, MonoidHom.codRestrict_apply]
    rw [MonoidHom.mem_ker, h1]
    exact mk'_primeComplementCore_eq_one_iff p (θ₀ a)
  have hψ : Function.Surjective ψ := by
    intro l
    obtain ⟨j, hj, hjl⟩ : ((e.symm l : K) : H ⧸ primeComplementCore (G := H) p) ∈
        ((nclIn H X).subgroupOf H).map (QuotientGroup.mk' (primeComplementCore (G := H) p)) :=
      hπJ.symm ▸ (e.symm l).2
    refine ⟨⟨⟨(j : G), hJH' hj⟩, hj⟩, ?_⟩
    have h1 : θ.codRestrict K hθK ⟨⟨(j : G), hJH' hj⟩, hj⟩ = e.symm l := Subtype.ext hjl
    simp only [ψ, MonoidHom.coe_comp, Function.comp_apply, h1, MulEquiv.coe_toMonoidHom,
      MulEquiv.apply_symm_apply]
  have hker : ρ.ker ≤ ψ.ker := by
    intro a ha
    have ha' : ((a : H') : G) ∈ GLBPrimeCore p H' := by
      rw [← mk'_primeComplementCore_eq_one_iff]
      exact congrArg Subtype.val (MonoidHom.mem_ker.mp ha)
    have hN := inf_glbPrimeCore_le_glbPrimeCore p hJH' ⟨a.2, ha'⟩
    rw [glbPrimeCore_nclIn] at hN
    exact (hψker a).mpr hN.2
  obtain ⟨φ, -, hφs, hφker⟩ := exists_surjective_comp_eq ρ
    ((QuotientGroup.mk' _).subgroupMap_surjective _) ψ hψ hker
  refine ⟨φ, hφs, ?_⟩
  have hι : Function.Injective (H'.subtype.comp ((nclIn H X).subgroupOf H').subtype) :=
    H'.subtype_injective.comp (Subgroup.subtype_injective _)
  refine Nat.Coprime.coprime_dvd_right ?_ ((glbPrimeCore_coprime p H).coprime_dvd_right
    (Subgroup.card_dvd_of_le (H := ψ.ker.map (H'.subtype.comp
      ((nclIn H X).subgroupOf H').subtype)) ?_))
  · rw [hφker, Subgroup.card_map_of_injective hι]
    exact Subgroup.card_map_dvd _ _
  · rintro _ ⟨a, ha, rfl⟩
    exact (hψker a).mp ha

theorem not_hasPrimeConstraint_of_nclIn {p : ℕ} [Fact p.Prime] {H R H' : Subgroup G}
    (hRH : R ≤ H) (hRH' : R ≤ H') (hRp : IsPGroup p R) (hR1 : R ≠ ⊥)
    {K : Subgroup (H ⧸ primeComplementCore (G := H) p)}
    (hKs : IsSimpleGroup K) (hKnab : ∃ a b : K, a * b ≠ b * a)
    (hπJ : ((nclIn H R).subgroupOf H).map
      (QuotientGroup.mk' (primeComplementCore (G := H) p)) = K)
    (hJH' : nclIn H R ≤ H') (Rb : Sylow p (H' ⧸ primeComplementCore (G := H') p))
    (hRb : (Rb : Subgroup (H' ⧸ primeComplementCore (G := H') p)) =
      (R.subgroupOf H').map (QuotientGroup.mk' (primeComplementCore (G := H') p))) :
    ¬ HasPrimeConstraint (G := H') p := by
  have hp : p.Prime := Fact.out
  rintro ⟨O, hOn, hOp, hOC⟩
  set Jt := ((nclIn H R).subgroupOf H').map
    (QuotientGroup.mk' (primeComplementCore (G := H') p)) with hJt
  have hOR : O ≤ (Rb : Subgroup (H' ⧸ primeComplementCore (G := H') p)) := by
    have := hOn
    exact hOp.le_sylow_of_normal Rb
  have hRJ : (Rb : Subgroup (H' ⧸ primeComplementCore (G := H') p)) ≤ Jt := by
    rw [hRb]
    exact Subgroup.map_mono (Subgroup.comap_mono (le_nclIn hRH))
  have hOJ : O ≤ Jt := hOR.trans hRJ
  obtain ⟨φ, hφs, hφc⟩ := exists_competitorHom_aux (H := H) (X := R) (MulEquiv.refl K) hπJ hJH'
  have hO'n : (O.subgroupOf Jt).Normal := hOn.subgroupOf Jt
  have hO'p : IsPGroup p (O.subgroupOf Jt) := hOp.comap_subtype
  have hφn : ((O.subgroupOf Jt).map φ).Normal := hO'n.map φ hφs
  have hφp : IsPGroup p ((O.subgroupOf Jt).map φ) := hO'p.map φ
  have hφbot : (O.subgroupOf Jt).map φ = ⊥ := by
    have := hKs
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal ((O.subgroupOf Jt).map φ) with h | h
    · exact h
    · exfalso
      rw [h] at hφp
      have hKp : IsPGroup p K := hφp.of_equiv Subgroup.topEquiv
      have : Nontrivial K := inferInstance
      have hc : Nontrivial (Subgroup.center K) := hKp.center_nontrivial
      rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center K) with h0 | h0
      · exact (Subgroup.nontrivial_iff_ne_bot _).mp hc h0
      · obtain ⟨a, b, hab⟩ := hKnab
        exact hab (Subgroup.mem_center_iff.mp (h0 ▸ Subgroup.mem_top a) b).symm
  have hle : O.subgroupOf Jt ≤ φ.ker := by
    rw [← MonoidHom.comap_bot]
    exact Subgroup.map_le_iff_le_comap.mp hφbot.le
  have hOb : O.subgroupOf Jt = ⊥ := by
    have h1 := inf_eq_bot_of_isPGroup hp hO'p hφc
    exact (inf_eq_left.mpr hle).symm.trans h1
  have hO1 : O = ⊥ := by
    rw [eq_bot_iff]
    intro o ho
    have := (Subgroup.mem_bot.mp (hOb ▸ (show (⟨o, hOJ ho⟩ : Jt) ∈ O.subgroupOf Jt from ho)))
    exact Subgroup.mem_bot.mpr (congrArg Subtype.val this)
  have hY1 : ∀ x : H' ⧸ primeComplementCore (G := H') p, x = 1 := by
    intro x
    have hx : x ∈ Subgroup.centralizer
        (O : Set (H' ⧸ primeComplementCore (G := H') p)) := by
      rw [hO1, Subgroup.mem_centralizer_iff]
      intro g hg
      rw [SetLike.mem_coe, Subgroup.mem_bot] at hg
      simp [hg]
    exact Subgroup.mem_bot.mp (hO1 ▸ hOC hx)
  have hbot : (R.subgroupOf H').map (QuotientGroup.mk' (primeComplementCore (G := H') p)) = ⊥ :=
    eq_bot_iff.mpr fun y _ => Subgroup.mem_bot.mpr (hY1 y)
  exact map_mk_ne_bot_of_isPGroup hp hRH' hRp hR1 hbot

theorem exists_caseThree_of_config3 (hβ : KFactBetaRank2) (h1s : D1CaseOneSmall3 G)
    (h2 : D1CaseTwo3 G) {p : ℕ} {P : Sylow p G} {M H R : Subgroup G}
    {Rbar : Sylow p (H ⧸ primeComplementCore (G := H) p)}
    (hcfg : D1ComponentConfig3 p P M H R Rbar) :
    ∃ K : Subgroup (H ⧸ primeComplementCore (G := H) p), IsComponentOf K ⊤ ∧
      (∀ L : Subgroup (H ⧸ primeComplementCore (G := H) p), IsComponentOf L ⊤ → L = K) ∧
      ¬ IsCyclic ((Rbar : Subgroup (H ⧸ primeComplementCore (G := H) p)) ⊓ K :
        Subgroup (H ⧸ primeComplementCore (G := H) p)) ∧
      (∀ c ∈ (Rbar : Subgroup (H ⧸ primeComplementCore (G := H) p)) ⊓
          Subgroup.centralizer (K : Set (H ⧸ primeComplementCore (G := H) p)),
        orderOf c = p → c ∈ (Subgroup.center K).map K.subtype) := by
  have hred := hcfg.red
  by_cases hall : ∀ L : Subgroup (H ⧸ primeComplementCore (G := H) p), IsComponentOf L ⊤ →
      IsCyclic ((Rbar : Subgroup (H ⧸ primeComplementCore (G := H) p)) ⊓ L :
        Subgroup (H ⧸ primeComplementCore (G := H) p))
  · exact (h2 p P M H R Rbar hcfg hall).elim
  push Not at hall
  obtain ⟨K, hK, hnc⟩ := hall
  rcases hred.rankOne_or_center hK hnc with ⟨z, hzR, hzK, hzp, hzc, hN, hKX₀, -, hZ⟩ | hcent
  · have hAut := pRank_mulAut_le_two3 hred hcfg.pRank_rbar_eq_three.le hcfg.catalog hβ hK hZ
      hzR hzp hzK hzc hN hKX₀
    exact (h1s p P M H R Rbar hcfg K hK hZ hnc ⟨z, hzR, hzK, hzp, hzc⟩ hAut
      (hred.pRank_eq_three_of_pRank_mulAut_le_two hK hKX₀ hAut)).elim
  · exact ⟨K, hK, fun L hL => hred.eq_of_forall_mem_center hK hL hcent, hnc, hcent⟩

theorem simple_nonabelian_of_center_eq_bot {Y : Type} [Group Y] {K : Subgroup Y}
    (hK : IsComponentOf K ⊤) (hZ : Subgroup.center K = ⊥) :
    IsSimpleGroup K ∧ ∃ a b : K, a * b ≠ b * a := by
  let e : K ≃* K ⧸ Subgroup.center K :=
    QuotientGroup.quotientBot.symm.trans (QuotientGroup.quotientMulEquivOfEq hZ.symm)
  have : IsSimpleGroup (K ⧸ Subgroup.center K) := hK.2.2.2
  refine ⟨e.isSimpleGroup, ?_⟩
  obtain ⟨a, b, hab⟩ :=
    CFSG.ComponentClassification.Helpers.quasisimple_central_quotient_nonabelian K hK.2.2
  exact ⟨e.symm a, e.symm b, fun hba => hab (by simpa using congrArg e hba)⟩

theorem competitorsOn_klingen3 {p : ℕ} [Fact p.Prime] {P : Sylow p G} {M R : Subgroup G}
    (hmod : StmtKlingenModel) (hk : KFactKlingenLocal) (hβ : KFactBetaRank2)
    (h1s : D1CaseOneSmall3 G) (h2 : D1CaseTwo3 G) (h3 : D1CaseThreeNotKlingen3 G)
    (hother : D1CaseThreeKlingenOther3 G) (hS : Setting G) (hloc : D1Local3 p P M)
    (hind : ∀ q ∈ rankThreeSigmaA G, q < p → D1At3 G q) :
    D1JCompetitorsOn (fun H' => D1KlingenSocle p P M R H') R R := by
  intro H hH H' hH' hJH' hRH'
  obtain ⟨T, _, hTs, hTnab, -, h⟩ := hH
  have hp : p.Prime := Fact.out
  obtain ⟨K, hKn, ⟨e⟩, hC, hRK⟩ := h.socle
  obtain ⟨Rbar, hRbar, hred⟩ := h.ext.reducedNongeneration
  have hRH : R ≤ H := h.ext.le_H
  have hRp : IsPGroup p R := h.ext.isPGroup
  have hR1 : R ≠ ⊥ := by
    rintro rfl
    have := h.ext.three_le_pRank
    rw [pRank_bot_eq_zero hp] at this
    omega
  have : IsSimpleGroup T := hTs
  have hKs : IsSimpleGroup K := e.isSimpleGroup
  have hKnab : ∃ a b : K, a * b ≠ b * a := by
    obtain ⟨a, b, hab⟩ := hTnab
    exact ⟨e.symm a, e.symm b, fun hba => hab (by simpa using congrArg e hba)⟩
  have hRK' : (R.subgroupOf H).map (QuotientGroup.mk' (primeComplementCore (G := H) p)) ≤ K :=
    hRK.le.trans inf_le_right
  have hπR1 := map_mk_ne_bot_of_isPGroup hp hRH hRp hR1
  have hπJ := map_nclIn_eq_of_simple hRH hKn hKs hRK' hπR1
  have hH'M : ¬ H' ≤ M := by
    intro hH'M
    have := hKn
    have hrank : 3 ≤ Open.pRank p ((Rbar : Subgroup (H ⧸ primeComplementCore (G := H) p)) ⊓ K) := by
      rw [inf_eq_left.mpr (hRbar ▸ hRK')]
      exact hred.three_le_pRank
    refine not_le_of_weakCore_le hp Rbar hred.weakCore_le hred.ne_top hrank ?_
    rw [← hπJ]
    exact Subgroup.map_mono fun j hj => ⟨j.2, hH'M (hJH' hj)⟩
  have hext' : D1Extremal p P M H' R := h.ext.of_le hH' hRH' hH'M
  obtain ⟨Rb', hRb', -⟩ := hext'.reducedNongeneration
  have hcon' : ¬ HasPrimeConstraint (G := H') p :=
    not_hasPrimeConstraint_of_nclIn hRH hRH' hRp hR1 hKs hKnab hπJ hJH' Rb' hRb'
  obtain ⟨Rbar', hcfg'⟩ :=
    exists_componentConfig3 hS hloc.sigma hloc.isCoreMaxLocal hext' hcon' hind
  obtain ⟨K', hK', huniq', hnc', hcent'⟩ := exists_caseThree_of_config3 hβ h1s h2 hcfg'
  by_cases hKD' : HasKlingenData p Rbar'
      (((H' ⊓ M).subgroupOf H').map (QuotientGroup.mk' (primeComplementCore p)))
  swap
  · exact (h3 p P M H' R Rbar' hcfg' K' hK' huniq' hnc' hcent' hKD').elim
  by_cases hsp' : IsKlingenComponent p K'
  swap
  · exact (hother p P M H' R Rbar' hcfg' K' hK' huniq' hnc' hcent' hKD' hsp').elim
  obtain ⟨d', hd', ⟨e'⟩⟩ := hsp'
  have hZ' : Subgroup.center K' = ⊥ :=
    hmod.center K' p d' hloc.ne_two hd' hK'.2.2 (hcfg'.isPGroup_center hK') ⟨e'⟩
  have eK' : K' ≃* CatGroup d' :=
    (QuotientGroup.quotientBot.symm.trans (QuotientGroup.quotientMulEquivOfEq hZ'.symm)).trans e'
  have hC' := hcfg'.centralizer_eq_bot hK' huniq' hcent' hZ'
  have hKn' : K'.Normal := normal_of_forall_isComponentOf_eq hK' huniq'
  have hOut' := hk.outer p hloc.ne_two d' hd' K' ⟨eK'⟩
  have hRK'' : (R.subgroupOf H').map (QuotientGroup.mk' (primeComplementCore (G := H') p)) ≤
      K' := by
    have : Finite (MulAut K') := MulEquiv.finite_left
    intro x hx
    rw [← hcfg'.rbar] at hx
    obtain ⟨n, hn⟩ := Rbar'.isPGroup' ⟨x, hx⟩
    have hxn : x ^ p ^ n = 1 := by simpa using congrArg Subtype.val hn
    have hmem := mem_sup_centralizer_of_pow hp hOut' hxn
    rwa [hC', sup_bot_eq] at hmem
  obtain ⟨hK's, hK'nab⟩ := simple_nonabelian_of_center_eq_bot hK' hZ'
  refine ⟨⟨↥K', inferInstance, hK's, hK'nab, ⟨d', hd', ⟨eK'⟩⟩, hext', h.glob,
    le_rfl, K', hKn', ⟨MulEquiv.refl _⟩, hC', (inf_eq_left.mpr hRK'').symm⟩, ?_⟩
  calc nclIn H R = nclIn (nclIn H R) R :=
        (nclIn_nclIn_of_simple hRH hRp hR1 hKn hRK').symm
    _ ≤ nclIn H' R := nclIn_le_nclIn_of_le (le_nclIn hRH) hJH'

theorem competitorsOn_of_le_klingen {p : ℕ} [Fact p.Prime] {P : Sylow p G} {M R Z : Subgroup G}
    (hcomp : D1JCompetitorsOn (fun H' => D1KlingenSocle p P M R H') R R) (hZR : Z ≤ R)
    (hZ : Z ≠ ⊥) : D1JCompetitorsOn (fun H' => D1KlingenSocle p P M R H') R Z := by
  intro H hH H' hH' hJH' hRH'
  obtain ⟨T, _, hTs, hTnab, hTk, hS⟩ := hH
  rw [hS.nclIn_eq_of_le hTs hZR hZ] at hJH' ⊢
  obtain ⟨h', hle⟩ := hcomp H ⟨T, inferInstance, hTs, hTnab, hTk, hS⟩ H' hH' hJH'
    hRH'
  obtain ⟨T', _, hTs', hTnab', hTk', hS'⟩ := h'
  exact ⟨⟨T', inferInstance, hTs', hTnab', hTk', hS'⟩,
    hle.trans (hS'.nclIn_eq_of_le hTs' hZR hZ).ge⟩

end CFSG.LocalAnalysis.RankThreeTheoremC

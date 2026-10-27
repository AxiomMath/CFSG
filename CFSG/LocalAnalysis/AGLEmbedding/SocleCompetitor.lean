module

public import CFSG.LocalAnalysis.AGLEmbedding.SocleCompetitorHom
public import CFSG.LocalAnalysis.AGLEmbedding.JStarGenericCases
public import CFSG.LocalAnalysis.AGLEmbedding.JStarGenericThree
public import CFSG.LocalAnalysis.AGLEmbedding.LemmaJStarOn
public import CFSG.LocalAnalysis.AGLEmbedding.LinTwoDataAux

public section

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.PreuniquenessRankFour.Helpers
open CFSG.RankThreeCoreUniqueness.Helpers
open scoped commutatorElement

namespace D1SocleConfig

variable {G : Type} [Group G] [Finite G] {T : Type} [Group T] [Finite T] {p a b : ℕ}
  [Fact p.Prime] {P : Sylow p G} {M H R X : Subgroup G}

theorem not_le_of_nclIn_le (h : D1SocleConfig T p P M H R X) (hT : JStarTarget p b T)
    (hTc : JStarTargetCard p a b T) {H' : Subgroup G} (hJH' : nclIn H X ≤ H') : ¬ H' ≤ M := by
  intro hH'M
  obtain ⟨K, hKn, ⟨e⟩, -, hXK⟩ := h.socle
  obtain ⟨Rbar, -, hred⟩ := h.ext.reducedNongeneration
  have : K.Normal := hKn
  have hp : p.Prime := Fact.out
  have hrank : 3 ≤ Open.pRank p ((Rbar : Subgroup (H ⧸ primeComplementCore (G := H) p)) ⊓ K) :=
    three_le_pRank_inf_of_target hT e Rbar
  refine not_le_of_weakCore_le hp Rbar hred.weakCore_le hred.ne_top hrank ?_
  rw [← h.map_nclIn_eq hT.toBase hTc hKn ⟨e⟩ hXK]
  exact Subgroup.map_mono fun j hj => ⟨j.2, hH'M (hJH' hj)⟩

theorem card_dvd_of_isPGroup (h : D1SocleConfig T p P M H R X) (_hT : JStarTargetBase p b T)
    (hTc : JStarTargetCard p a b T) {H' : Subgroup G} (h' : D1Escape p P M H' R)
    (S : Subgroup (H' ⧸ primeComplementCore (G := H') p)) (hS : IsPGroup p S) :
    Nat.card S ∣ b := by
  obtain ⟨K, hKn, hKe, hC, -⟩ := h.socle
  obtain ⟨Rbar, hRbar, -⟩ := h.ext.reducedNongeneration
  obtain ⟨Rb, hRb, -⟩ := h'.reducedNongeneration
  have hp : p.Prime := Fact.out
  have hdvd : Nat.card (Rbar : Subgroup (H ⧸ primeComplementCore (G := H) p)) ∣ b :=
    card_dvd_of_isPGroup_of_target hTc hKn hKe hC _ Rbar.isPGroup'
  obtain ⟨T', hST⟩ := hS.exists_le_sylow
  have h1 : Nat.card (T' : Subgroup (H' ⧸ primeComplementCore (G := H') p)) =
      Nat.card (Rb : Subgroup (H' ⧸ primeComplementCore (G := H') p)) := by
    rw [T'.card_eq_multiplicity, Rb.card_eq_multiplicity]
  have h2 : Nat.card (Rb : Subgroup (H' ⧸ primeComplementCore (G := H') p)) = Nat.card R := by
    have hRp : IsPGroup p (R.subgroupOf H') := h'.isPGroup.comap_subtype
    rw [hRb, card_map_mk_of_isPGroup hp _ (primeComplementCore_coprime p) hRp,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe h'.le_H).toEquiv]
  have h3 : Nat.card (Rbar : Subgroup (H ⧸ primeComplementCore (G := H) p)) = Nat.card R := by
    have hRp : IsPGroup p (R.subgroupOf H) := h.ext.isPGroup.comap_subtype
    rw [hRbar, card_map_mk_of_isPGroup hp _ (primeComplementCore_coprime p) hRp,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe h.ext.le_H).toEquiv]
  exact (Subgroup.card_dvd_of_le hST).trans (h1 ▸ h2 ▸ h3 ▸ hdvd)

theorem exists_jStarHypOf (h : D1SocleConfig T p P M H R X) (hT : JStarTargetBase p b T)
    (hTc : JStarTargetCard p a b T) {H' : Subgroup G} (hext' : D1Extremal p P M H' R)
    (hJH' : nclIn H X ≤ H') :
    ∃ (Rb : Sylow p (H' ⧸ primeComplementCore (G := H') p))
      (φ : ((nclIn H X).subgroupOf H').map (QuotientGroup.mk' (primeComplementCore (G := H') p))
        →* T),
      (Rb : Subgroup (H' ⧸ primeComplementCore (G := H') p)) =
        (R.subgroupOf H').map (QuotientGroup.mk' (primeComplementCore (G := H') p)) ∧
      JStarHypOf p Rb
        (((H' ⊓ M).subgroupOf H').map (QuotientGroup.mk' (primeComplementCore p)))
        (((nclIn H X).subgroupOf H').map (QuotientGroup.mk' (primeComplementCore (G := H') p)))
        ((X.subgroupOf H').map (QuotientGroup.mk' (primeComplementCore (G := H') p))) T b φ := by
  obtain ⟨Rb, hRb, hred⟩ := hext'.reducedNongeneration
  obtain ⟨φ, hs, hc, hk⟩ := h.exists_competitorHom hT hTc hJH'
  refine ⟨Rb, φ, hRb, h.ext.ne_two, hred,
    (catalogSimpleSections_of_isKProper h.glob.kProper H' hext'.ne_top).quotient _, hs, hc, ?_,
    h.nclIn_map_eq hT hTc hJH', ?_, ?_, h.card_dvd_of_isPGroup hT hTc hext'.toD1Escape⟩
  · rw [hRb]
    exact Subgroup.map_mono (Subgroup.comap_mono h.le_R)
  · rw [hRb]
    exact h.map_le_normalizer_map hJH'
  · intro z hz
    rw [hRb] at hz
    exact h.faithful_of_mem_ker_iff hT hTc hJH' hk z hz

theorem map_eq_inf_of_mulEquiv (h : D1SocleConfig T p P M H R X) (hT : JStarTargetBase p b T)
    (hTc : JStarTargetCard p a b T) {H' : Subgroup G} (hJH' : nclIn H X ≤ H')
    (Rb : Sylow p (H' ⧸ primeComplementCore (G := H') p))
    (hRb : (Rb : Subgroup (H' ⧸ primeComplementCore (G := H') p)) =
      (R.subgroupOf H').map (QuotientGroup.mk' (primeComplementCore (G := H') p)))
    (hJn : (((nclIn H X).subgroupOf H').map
      (QuotientGroup.mk' (primeComplementCore (G := H') p))).Normal)
    (hJe : Nonempty (((nclIn H X).subgroupOf H').map
      (QuotientGroup.mk' (primeComplementCore (G := H') p)) ≃* T)) :
    (X.subgroupOf H').map (QuotientGroup.mk' (primeComplementCore (G := H') p)) =
      (R.subgroupOf H').map (QuotientGroup.mk' (primeComplementCore (G := H') p)) ⊓
        ((nclIn H X).subgroupOf H').map (QuotientGroup.mk' (primeComplementCore (G := H') p)) := by
  obtain ⟨e⟩ := hJe
  have := hJn
  have hcard := card_inf_of_target hTc e Rb
  rw [hRb] at hcard
  exact map_eq_inf_of_card_eq h.le_R h.le_H h.isPGroup hJH' (by rw [hcard, h.card_eq hT hTc])

theorem competitor_of_not_le (h : D1SocleConfig T p P M H R X) (hT : JStarTargetBase p b T)
    (hTc : JStarTargetCard p a b T) (hE : JStarElimOf p b T) (hβ : KFactBeta)
    (hP1L : KFactP1ThreeLie) (hP1A : KFactP1ThreeAlt) (hP1S : KFactP1ThreeSpor)
    {H' : Subgroup G} (hH' : GLBIsMaxTwoLocal H') (hJH' : nclIn H X ≤ H') (hRH' : R ≤ H')
    (hH'M : ¬ H' ≤ M) : D1SocleConfig T p P M H' R X ∧ nclIn H X ≤ nclIn H' X := by
  refine ⟨?_, h.nclIn_le_nclIn hT hTc hJH'⟩
  have hext' : D1Extremal p P M H' R := h.ext.of_le hH' hRH' hH'M
  obtain ⟨Rb, φ, hRb, hyp⟩ := h.exists_jStarHypOf hT hTc hext' hJH'
  obtain ⟨hJn, hJe, hJC⟩ := jStarConclOf_of_cases jStarOfO1 (jStarOfII hβ) jStarOfI
    (jStarOfIII hP1L hP1A hP1S) hT hE hyp fun hcon => by
      obtain ⟨L, hL, -⟩ := isKProper_not_hasPrimeConstraint_catalog_component h.glob.kProper H'
        hext'.ne_top p Fact.out hcon
      exact ⟨L, hL⟩
  exact ⟨hext', h.glob, h.le_R,
    ⟨_, hJn, hJe, hJC, h.map_eq_inf_of_mulEquiv hT hTc hJH' Rb hRb hJn hJe⟩⟩

theorem competitor (h : D1SocleConfig T p P M H R X) (hT : JStarTarget p b T)
    (hTc : JStarTargetCard p a b T) (hE : JStarElimOf p b T) (hβ : KFactBeta)
    (hP1L : KFactP1ThreeLie) (hP1A : KFactP1ThreeAlt) (hP1S : KFactP1ThreeSpor)
    {H' : Subgroup G} (hH' : GLBIsMaxTwoLocal H') (hJH' : nclIn H X ≤ H') (hRH' : R ≤ H') :
    D1SocleConfig T p P M H' R X ∧ nclIn H X ≤ nclIn H' X :=
  h.competitor_of_not_le hT.toBase hTc hE hβ hP1L hP1A hP1S hH' hJH' hRH'
    (h.not_le_of_nclIn_le hT hTc hJH')

end D1SocleConfig

section Socle2

variable {G : Type} [Group G] [Finite G]

variable {T : Type} [Group T] [Finite T] {p a b : ℕ} [Fact p.Prime] {P : Sylow p G}
  {M H R U : Subgroup G}

theorem competitorsOn_socleConfig (hT : JStarTarget p b T) (hTc : JStarTargetCard p a b T)
    (hE : JStarElimOf p b T) (hβ : KFactBeta) (hP1L : KFactP1ThreeLie)
    (hP1A : KFactP1ThreeAlt) (hP1S : KFactP1ThreeSpor) :
    D1JCompetitorsOn (D1SocleConfig T p P M · R U) R U :=
  fun _ h _ hH' hJH' hRH' => h.competitor hT hTc hE hβ hP1L hP1A hP1S hH' hJH' hRH'

omit [Finite T] in
theorem D1SocleConfig.le_nclIn_of_le (hT : IsSimpleGroup T) (h : D1SocleConfig T p P M H R U)
    {Z : Subgroup G} (hZU : Z ≤ U) (hZ : Z ≠ ⊥) : U ≤ nclIn H Z := by
  have hp : p.Prime := Fact.out
  have hUH : U ≤ H := h.le_R.trans h.ext.le_H
  have hZH : Z ≤ H := hZU.trans hUH
  have hUp : IsPGroup p U := h.ext.isPGroup.to_le h.le_R
  obtain ⟨K, hKn, ⟨e⟩, -, hUK⟩ := h.socle
  have hKs : IsSimpleGroup K := e.isSimpleGroup
  have hUK' : (U.subgroupOf H).map (QuotientGroup.mk' (primeComplementCore (G := H) p)) ≤ K :=
    hUK ▸ inf_le_right
  set J := nclIn H Z with hJdef
  have hJK : J ≤
      (K.comap (QuotientGroup.mk' (primeComplementCore (G := H) p))).map H.subtype := by
    refine nclIn_le (fun x hx => ⟨⟨x, hZH hx⟩, hUK' (Subgroup.mem_map_of_mem _
      (Subgroup.mem_subgroupOf.mpr (hZU hx))), rfl⟩) (Subgroup.map_subtype_le _) ?_
    refine (Subgroup.normal_subgroupOf_iff_le_normalizer (Subgroup.map_subtype_le _)).mp ?_
    rw [Subgroup.subgroupOf, Subgroup.comap_map_eq_self_of_injective H.subtype_injective]
    exact hKn.comap _
  have hle : (J.subgroupOf H).map (QuotientGroup.mk' (primeComplementCore (G := H) p)) ≤ K := by
    rintro _ ⟨j, hj, rfl⟩
    obtain ⟨j', hj', hjj'⟩ := hJK hj
    rwa [← Subtype.ext hjj']
  have hnormal : ((J.subgroupOf H).map
      (QuotientGroup.mk' (primeComplementCore (G := H) p))).Normal :=
    (nclIn_normal H Z).map _ (QuotientGroup.mk'_surjective _)
  have hne : (J.subgroupOf H).map (QuotientGroup.mk' (primeComplementCore (G := H) p)) ≠ ⊥ := by
    intro hbot
    have hZle : (Z.subgroupOf H).map (QuotientGroup.mk' (primeComplementCore (G := H) p)) ≤
        (J.subgroupOf H).map (QuotientGroup.mk' (primeComplementCore (G := H) p)) :=
      Subgroup.map_mono (Subgroup.comap_mono (le_nclIn hZH))
    rw [hbot, le_bot_iff] at hZle
    have hZN : Z ≤ GLBPrimeCore p H := le_glbPrimeCore_of_map_eq_bot hZH hZle
    apply hZ
    rw [← inf_eq_left.mpr hZN]
    exact inf_eq_bot_of_isPGroup hp (hUp.to_le hZU) (glbPrimeCore_coprime p H)
  have hJeq : (J.subgroupOf H).map (QuotientGroup.mk' (primeComplementCore (G := H) p)) = K := by
    have := hnormal.subgroupOf K
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (((J.subgroupOf H).map
        (QuotientGroup.mk' (primeComplementCore (G := H) p))).subgroupOf K) with hbot | htop
    · exact absurd (le_bot_iff.mp (by
        have hdisj := Subgroup.subgroupOf_eq_bot.mp hbot
        exact (le_inf le_rfl hle).trans (disjoint_iff.mp hdisj).le)) hne
    · exact le_antisymm hle (Subgroup.subgroupOf_eq_top.mp htop)
  have hUJN : U ≤ J ⊔ GLBPrimeCore p H := le_sup_glbPrimeCore_of_map_le hUH (hJeq ▸ hUK')
  exact le_of_le_sup_of_isPGroup_of_coprime hUp (glbPrimeCore_coprime p H)
    ((glbPrimeCore_le p H).trans (le_normalizer_nclIn H Z)) hUJN

omit [Finite T] in
theorem D1SocleConfig.nclIn_eq_of_le (hT : IsSimpleGroup T) (h : D1SocleConfig T p P M H R U)
    {Z : Subgroup G} (hZU : Z ≤ U) (hZ : Z ≠ ⊥) : nclIn H Z = nclIn H U := by
  have hUH : U ≤ H := h.le_R.trans h.ext.le_H
  refine le_antisymm (nclIn_le (hZU.trans (le_nclIn hUH)) (nclIn_le_self H U)
    (le_normalizer_nclIn H U)) ?_
  exact nclIn_le (h.le_nclIn_of_le hT hZU hZ) (nclIn_le_self H _) (le_normalizer_nclIn H _)

omit [Finite T] in
theorem competitorsOn_of_le (hT : IsSimpleGroup T)
    (hcomp : D1JCompetitorsOn (D1SocleConfig T p P M · R U) R U) {Z : Subgroup G}
    (hZU : Z ≤ U) (hZ : Z ≠ ⊥) : D1JCompetitorsOn (D1SocleConfig T p P M · R U) R Z := by
  intro H h H' hH' hJH' hRH'
  rw [h.nclIn_eq_of_le hT hZU hZ] at hJH' ⊢
  obtain ⟨h', hle⟩ := hcomp H h H' hH' hJH' hRH'
  exact ⟨h', hle.trans (h'.nclIn_eq_of_le hT hZU hZ).ge⟩

end Socle2

end CFSG.AGLEmbedding

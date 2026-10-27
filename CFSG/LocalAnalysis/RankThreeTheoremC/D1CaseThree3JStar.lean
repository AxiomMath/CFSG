module

public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactSections3
public import CFSG.LocalAnalysis.AGLEmbedding.JStarRankTwo
public import CFSG.LocalAnalysis.AGLEmbedding.LinTwoCompetitor
import CFSG.LocalAnalysis.AGLEmbedding.JStarReducedI
import CFSG.LocalAnalysis.AGLEmbedding.JStarReducedIII
import CFSG.LocalAnalysis.AGLEmbedding.JStarReducedO1

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open CFSG.PreuniquenessRankFour.Helpers CFSG.RankThreeCoreUniqueness.Helpers
open CFSG.AGLEmbedding

theorem pRank_mulAut_le_two_of_isCyclic3 {p : ℕ} {X : Type} [Group X] [Finite X]
    {R : Sylow p X} {X₀ : Subgroup X} (h : ReducedNongeneration p X R X₀)
    (hX : CatalogSimpleSections X) (hKF : KFactBetaRank2) {L : Subgroup X}
    (hL : IsComponentOf L ⊤) (hcyc : IsCyclic ((R : Subgroup X) ⊓ L : Subgroup X)) :
    Open.pRank p (⊤ : Subgroup (MulAut L)) ≤ 2 := by
  have hp := h.prime
  have : Fact p.Prime := ⟨hp⟩
  have hZ := h.center_eq_bot_of_isCyclic hL hcyc
  let e : L ≃* L ⧸ Subgroup.center L :=
    ((QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot).symm
  have : IsSimpleGroup (L ⧸ Subgroup.center L) := hL.2.2.2
  have hsimple : IsSimpleGroup L := e.isSimpleGroup
  have hnonab : ∃ a b : L, a * b ≠ b * a := by
    obtain ⟨a, b, hab⟩ :=
      CFSG.ComponentClassification.Helpers.quasisimple_central_quotient_nonabelian L hL.2.2
    refine ⟨e.symm a, e.symm b, fun hba => hab ?_⟩
    simpa only [map_mul, MulEquiv.apply_symm_apply] using congrArg e hba
  have hcat : IsCatalogGroup L :=
    IsCatalogGroup.of_mulEquiv e (hX.isCatalogGroup_center_quotient hL)
  obtain ⟨T, hT⟩ := CFSG.Walter.exists_sylow_map_eq_inf_of_isSubnormal R
    (ComponentClassification.Components.mathlib_subnormal_of_chain hL.2.1
      Subgroup.IsSubnormal.top)
  have hTcyc : IsCyclic (T : Subgroup L) := by
    rw [← hT] at hcyc
    exact isCyclic_of_surjective
      (Subgroup.equivMapOfInjective _ _ L.subtype_injective).symm (MulEquiv.surjective _)
  obtain ⟨t, htRL, ht, -⟩ := exists_mem_sylow_inf_component hp h.ne_two h.core_eq_bot R hL
  have hTne : (T : Subgroup L) ≠ ⊥ := by
    intro hbot
    rw [hbot, Subgroup.map_bot] at hT
    have ht1 : t ∈ (⊥ : Subgroup X) := by
      rw [hT]
      exact htRL
    rw [Subgroup.mem_bot] at ht1
    rw [ht1, orderOf_one] at ht
    exact hp.one_lt.ne ht
  have hrk : Open.pRank p (T : Subgroup L) ≤ 2 :=
    SectionRank.pRank_le hp.one_lt fun A _ hA =>
      (card_le_of_isElemAbelian_of_isCyclic_sylow T hTcyc hA).trans
        (Nat.le_self_pow (by norm_num) p)
  exact hKF L hsimple hnonab hcat p hp h.ne_two T hTne hrk (Or.inl hTcyc)

theorem _root_.CFSG.AGLEmbedding.JStarHyp.false_of_not_le_centralizer3 {Y : Type} [Group Y]
    [Finite Y] {p n : ℕ} [Fact p.Prime] {Rb : Sylow p Y} {Y₀ Jt Xt : Subgroup Y}
    {φ : Jt →* PSL2GF p n} (h : JStarHyp p n Rb Y₀ Jt Xt φ) (hβ : KFactBetaRank2)
    {L : Subgroup Y} (hL : IsComponentOf L ⊤)
    (hcyc : IsCyclic ((Rb : Subgroup Y) ⊓ L : Subgroup Y))
    (hJL : ¬ Jt ≤ Subgroup.centralizer (L : Set Y)) : False := by
  have hp : p.Prime := Fact.out
  have hker := (h.le_centralizer_or_inf_le_ker hL).resolve_left hJL
  obtain ⟨E, hEJ, hE, hEcard⟩ := h.exists_isElemAbelian
  have hEp : IsPGroup p E := fun x => ⟨1, Subtype.ext (by simpa using hE.2 x x.2)⟩
  have hEC : E ⊓ Subgroup.centralizer (L : Set Y) = ⊥ := by
    rw [eq_bot_iff, ← h.inf_ker_eq_bot hEp]
    exact le_inf inf_le_left ((inf_le_inf_right _ hEJ).trans hker)
  have hineq := pRank_le_pRank_inf_centralizer_add_pRank_mulAut hp
    (hEJ.trans (h.le_normalizer_component hL))
  rw [hEC, pRank_bot_eq_zero hp] at hineq
  have h2 := pRank_mulAut_le_two_of_isCyclic3 h.red h.catalog hβ hL hcyc
  have hn : n ≤ Open.pRank p E :=
    le_csSup (PreuniquenessRankFour.Helpers.pRank_bddAbove p hp E) ⟨E, le_rfl, hE, hEcard⟩
  have := h.three_le
  omega

theorem _root_.CFSG.AGLEmbedding.JStarHyp.false_of_forall_isCyclic3 {Y : Type} [Group Y]
    [Finite Y] {p n : ℕ} [Fact p.Prime] {Rb : Sylow p Y} {Y₀ Jt Xt : Subgroup Y}
    {φ : Jt →* PSL2GF p n} (h : JStarHyp p n Rb Y₀ Jt Xt φ) (hβ : KFactBetaRank2)
    (hE : ∃ L : Subgroup Y, IsComponentOf L ⊤)
    (hcyc : ∀ L : Subgroup Y, IsComponentOf L ⊤ →
      IsCyclic ((Rb : Subgroup Y) ⊓ L : Subgroup Y)) : False := by
  obtain ⟨L, hL⟩ := hE
  by_cases hall : ∀ K : Subgroup Y, IsComponentOf K ⊤ → Jt ≤ Subgroup.centralizer (K : Set Y)
  · exact h.false_of_forall_le_centralizer hL hall
  · push Not at hall
    obtain ⟨K, hK, hJK⟩ := hall
    exact h.false_of_not_le_centralizer3 hβ hK (hcyc K hK) hJK

theorem jStarII3 (hβ : KFactBetaRank2) : StmtJStarII := fun h hE hcyc =>
  h.false_of_forall_isCyclic3 hβ hE hcyc

theorem _root_.CFSG.AGLEmbedding.JStarHypOf.false_of_not_le_centralizer3 {Y : Type} [Group Y]
    [Finite Y] {T : Type} [Group T] [Finite T] {p B : ℕ} [Fact p.Prime] {Rb : Sylow p Y}
    {Y₀ Jt Xt : Subgroup Y} {φ : Jt →* T} (h : JStarHypOf p Rb Y₀ Jt Xt T B φ)
    (hT : JStarTargetBase p B T) (hβ : KFactBetaRank2) {L : Subgroup Y}
    (hL : IsComponentOf L ⊤) (hcyc : IsCyclic ((Rb : Subgroup Y) ⊓ L : Subgroup Y))
    (hJL : ¬ Jt ≤ Subgroup.centralizer (L : Set Y)) : False := by
  have hp : p.Prime := Fact.out
  have hker := (h.le_centralizer_or_inf_le_ker hT hL).resolve_left hJL
  have hRC : (Rb : Subgroup Y) ⊓ Subgroup.centralizer (L : Set Y) = ⊥ := by
    rw [eq_bot_iff]
    intro z hz
    exact Subgroup.mem_bot.mpr (h.eq_one_of_inf_centralizer_le_ker hL hker hz.1 hz.2)
  have hRN : (Rb : Subgroup Y) ≤ Subgroup.normalizer (L : Set Y) :=
    fun x hx => Subgroup.normalCore_le _ (h.red.sylow_le_normalCore_normalizer_component hL hx)
  have h1 := pRank_le_pRank_inf_centralizer_add_pRank_mulAut hp hRN
  rw [hRC, pRank_bot_eq_zero hp] at h1
  have h2 := pRank_mulAut_le_two_of_isCyclic3 h.red h.catalog hβ hL hcyc
  have h3 := h.red.three_le_pRank
  omega

theorem _root_.CFSG.AGLEmbedding.JStarHypOf.false_of_forall_isCyclic3 {Y : Type} [Group Y]
    [Finite Y] {T : Type} [Group T] [Finite T] {p B : ℕ} [Fact p.Prime] {Rb : Sylow p Y}
    {Y₀ Jt Xt : Subgroup Y} {φ : Jt →* T} (h : JStarHypOf p Rb Y₀ Jt Xt T B φ)
    (hT : JStarTargetBase p B T) (hβ : KFactBetaRank2)
    (hE : ∃ L : Subgroup Y, IsComponentOf L ⊤)
    (hcyc : ∀ L : Subgroup Y, IsComponentOf L ⊤ →
      IsCyclic ((Rb : Subgroup Y) ⊓ L : Subgroup Y)) : False := by
  obtain ⟨L, hL⟩ := hE
  by_cases hall : ∀ K : Subgroup Y, IsComponentOf K ⊤ → Jt ≤ Subgroup.centralizer (K : Set Y)
  · exact h.false_of_forall_le_centralizer hT hL hall
  · push Not at hall
    obtain ⟨K, hK, hJK⟩ := hall
    exact h.false_of_not_le_centralizer3 hT hβ hK (hcyc K hK) hJK

theorem jStarOfII3 (hβ : KFactBetaRank2) : StmtJStarOfII := fun hT h hE hcyc =>
  h.false_of_forall_isCyclic3 hT hβ hE hcyc

section Socle

variable {G : Type} [Group G] [Finite G] {T : Type} [Group T] [Finite T] {p a b : ℕ}
  [Fact p.Prime] {P : Sylow p G} {M H R X : Subgroup G}

theorem _root_.CFSG.AGLEmbedding.D1SocleConfig.competitor_of_not_le3
    (h : D1SocleConfig T p P M H R X) (hT : JStarTargetBase p b T)
    (hTc : JStarTargetCard p a b T) (hE : JStarElimOf p b T) (hβ : KFactBetaRank2)
    (hP1L : KFactP1ThreeLie) (hP1A : KFactP1ThreeAlt) (hP1S : KFactP1ThreeSpor)
    {H' : Subgroup G} (hH' : GLBIsMaxTwoLocal H') (hJH' : nclIn H X ≤ H') (hRH' : R ≤ H')
    (hH'M : ¬ H' ≤ M) : D1SocleConfig T p P M H' R X ∧ nclIn H X ≤ nclIn H' X := by
  refine ⟨?_, h.nclIn_le_nclIn hT hTc hJH'⟩
  have hext' : D1Extremal p P M H' R := h.ext.of_le hH' hRH' hH'M
  obtain ⟨Rb, φ, hRb, hyp⟩ := h.exists_jStarHypOf hT hTc hext' hJH'
  obtain ⟨hJn, hJe, hJC⟩ := jStarConclOf_of_cases jStarOfO1 (jStarOfII3 hβ) jStarOfI
    (jStarOfIII hP1L hP1A hP1S) hT hE hyp fun hcon => by
      obtain ⟨L, hL, -⟩ := isKProper_not_hasPrimeConstraint_catalog_component h.glob.kProper H'
        hext'.ne_top p Fact.out hcon
      exact ⟨L, hL⟩
  exact ⟨hext', h.glob, h.le_R,
    ⟨_, hJn, hJe, hJC, h.map_eq_inf_of_mulEquiv hT hTc hJH' Rb hRb hJn hJe⟩⟩

theorem _root_.CFSG.AGLEmbedding.D1SocleConfig.competitor3
    (h : D1SocleConfig T p P M H R X) (hT : JStarTarget p b T)
    (hTc : JStarTargetCard p a b T) (hE : JStarElimOf p b T) (hβ : KFactBetaRank2)
    (hP1L : KFactP1ThreeLie) (hP1A : KFactP1ThreeAlt) (hP1S : KFactP1ThreeSpor)
    {H' : Subgroup G} (hH' : GLBIsMaxTwoLocal H') (hJH' : nclIn H X ≤ H') (hRH' : R ≤ H') :
    D1SocleConfig T p P M H' R X ∧ nclIn H X ≤ nclIn H' X :=
  h.competitor_of_not_le3 hT.toBase hTc hE hβ hP1L hP1A hP1S hH' hJH' hRH'
    (h.not_le_of_nclIn_le hT hTc hJH')

theorem _root_.CFSG.AGLEmbedding.D1SocleConfig.competitorTwo3
    (h : D1SocleConfig T p P M H R X) (hT : JStarTargetTwo p b T)
    (hTc : JStarTargetCard p a b T) (hE : JStarElimOf p b T) (hβ : KFactBetaRank2)
    (hP1L : KFactP1ThreeLie) (hP1A : KFactP1ThreeAlt) (hP1S : KFactP1ThreeSpor)
    {H' : Subgroup G} (hH' : GLBIsMaxTwoLocal H') (hJH' : nclIn H X ≤ H') (hRH' : R ≤ H') :
    D1SocleConfig T p P M H' R X ∧ nclIn H X ≤ nclIn H' X :=
  h.competitor_of_not_le3 hT.toJStarTargetBase hTc hE hβ hP1L hP1A hP1S hH' hJH' hRH'
    (h.not_le_of_nclIn_le_two hT hTc hJH')

end Socle

theorem competitorsOn_socleConfig3 {G : Type} [Group G] [Finite G] {T : Type} [Group T]
    [Finite T] {p a b : ℕ} [Fact p.Prime] {P : Sylow p G} {M R U : Subgroup G}
    (hT : JStarTarget p b T) (hTc : JStarTargetCard p a b T) (hE : JStarElimOf p b T)
    (hβ : KFactBetaRank2) (hP1L : KFactP1ThreeLie) (hP1A : KFactP1ThreeAlt)
    (hP1S : KFactP1ThreeSpor) : D1JCompetitorsOn (D1SocleConfig T p P M · R U) R U :=
  fun _ h _ hH' hJH' hRH' => h.competitor3 hT hTc hE hβ hP1L hP1A hP1S hH' hJH' hRH'

theorem competitorsOn_socleConfigTwo3 {G : Type} [Group G] [Finite G] {T : Type} [Group T]
    [Finite T] {p a b : ℕ} [Fact p.Prime] {P : Sylow p G} {M R U : Subgroup G}
    (hT : JStarTargetTwo p b T) (hTc : JStarTargetCard p a b T) (hE : JStarElimOf p b T)
    (hβ : KFactBetaRank2) (hP1L : KFactP1ThreeLie) (hP1A : KFactP1ThreeAlt)
    (hP1S : KFactP1ThreeSpor) : D1JCompetitorsOn (D1SocleConfig T p P M · R U) R U :=
  fun _ h _ hH' hJH' hRH' => h.competitorTwo3 hT hTc hE hβ hP1L hP1A hP1S hH' hJH' hRH'

theorem _root_.CFSG.AGLEmbedding.D1L2Config.competitor3 {G : Type} [Group G] [Finite G] {p : ℕ}
    [Fact p.Prime] {n : ℕ} {P : Sylow p G} {M H R X : Subgroup G} (hβ : KFactBetaRank2)
    (hP1L : KFactP1ThreeLie) (hP1A : KFactP1ThreeAlt) (hP1S : KFactP1ThreeSpor)
    (hEL : KFactJStarElimLie) (hEA : KFactJStarElimAlt) (hES : KFactJStarElimSpor)
    (h : D1L2Config p n P M H R X) {H' : Subgroup G} (hH' : GLBIsMaxTwoLocal H')
    (hJH' : nclIn H X ≤ H') (hRH' : R ≤ H') :
    D1L2Config p n P M H' R X ∧ nclIn H X ≤ nclIn H' X := by
  refine ⟨?_, h.nclIn_le_nclIn hJH'⟩
  have hext' : D1Extremal p P M H' R := h.ext.of_le hH' hRH' (h.not_le_of_nclIn_le hJH')
  obtain ⟨Rb, φ, hRb, hyp⟩ := h.exists_jStarHyp hext' hJH'
  obtain ⟨hJn, hJe, hJC⟩ := jStarConcl_of_cases jStarO1 (jStarII3 hβ) jStarI
    (jStarIII hP1L hP1A hP1S hEL hEA hES) hyp fun hcon => by
      obtain ⟨L, hL, -⟩ := isKProper_not_hasPrimeConstraint_catalog_component h.glob.kProper H'
        hext'.ne_top p Fact.out hcon
      exact ⟨L, hL⟩
  exact ⟨hext', h.glob, h.three_le, h.le_R,
    ⟨_, hJn, hJe, hJC, h.map_eq_inf_of_mulEquiv hJH' Rb hRb hJn hJe⟩, h.normal_sup⟩

theorem stmtCompetitor3 (hβ : KFactBetaRank2) (hP1L : KFactP1ThreeLie) (hP1A : KFactP1ThreeAlt)
    (hP1S : KFactP1ThreeSpor) (hEL : KFactJStarElimLie) (hEA : KFactJStarElimAlt)
    (hES : KFactJStarElimSpor) : StmtCompetitor :=
  fun _ h _ hH' hJH' hRH' => h.competitor3 hβ hP1L hP1A hP1S hEL hEA hES hH' hJH' hRH'

end CFSG.LocalAnalysis.RankThreeTheoremC

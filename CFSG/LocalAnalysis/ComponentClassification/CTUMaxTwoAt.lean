module

public import CFSG.LocalAnalysis.ComponentClassification.Foote5WLemma14
public import CFSG.LocalAnalysis.ComponentClassification.Sol76RankOneClass
public import CFSG.LocalAnalysis.ComponentClassification.Sol76PclsFinal
public import CFSG.LocalAnalysis.ComponentClassification.Sol76PclsSuz
public import CFSG.LocalAnalysis.ComponentClassification.CTUMirrorL34
public import CFSG.LocalAnalysis.ComponentClassification.Sol78PSp4

public section

namespace CFSG.ComponentClassification.Sol76

open CFSG Subgroup CFSG.ComponentClassification.FooteLit
  CFSG.ComponentClassification.UnbalancedLayer
open CFSG.LocalAnalysis.ComponentInitial (SchreierFor)
open scoped commutatorElement

theorem maximalTwoComponentSimple_at_of_solomonMaximal
    (hCI : GSLit.ClassicalInvolutionInput) (hGA : TBLit.GriessMultipliersAllModels)
    {G : Type} [Group G] [Finite G] [IsSimpleGroup G]
    (hsF : IsSimpleGroup (GeneralizedFitting.subgroup G))
    (hnF : ∃ a b : GeneralizedFitting.subgroup G, a * b ≠ b * a)
    (hoF : ¬ Blueprint.OddLieType (GeneralizedFitting.subgroup G))
    (h13 : Sol76T13.SolomonThm13Simple) (hK : Assembly.KProper Blueprint.Catalog G)
    {J : Subgroup G} (hJgs : GrSLit.GSWeakMaximalComponent J) (h2 : 2 ≤ pRank 2 ↥J)
    (hpsp : ¬ ∃ (K : Type) (_ : Field K) (_ : Finite K), Odd (Nat.card K) ∧
        Nonempty (J ⧸ Open.fusionZStar J ≃*
          Assembly.LowTwoRank.StatedProj (Assembly.LowTwoRank.StatedSp 2 K)))
    (hJmax : IsSolomonMaximal J) {t : G} (ht : orderOf t = 2)
    (hJt : J ≤ centralizer ({t} : Set G)) :
    (⨆ (g : G) (_ : conjugate J g ≤ centralizer ({t} : Set G)), conjugate J g) ≤
        (pPrimeCore 2 (centralizer ({t} : Set G))).map (centralizer ({t} : Set G)).subtype ⊔
          J ∧
      (3 ≤ pRank 2 ↥J → ∀ g : G, ¬ ⁅J, conjugate J g⁆ ≤
        (pPrimeCore 2 J).map J.subtype ⊓
          (pPrimeCore 2 (conjugate J g)).map (conjugate J g).subtype) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hnab : ∃ a b : G, a * b ≠ b * a := by
    obtain ⟨a, b, hab⟩ := hnF
    exact ⟨a, b, fun h => hab (Subtype.ext h)⟩
  have hA := aschbacherRankOneInput_of_classicalInvolution hCI hGA
  have hJs : J ∈ solomonKStar G := mem_solomonKStar_of_aschbacher hA hsF hnF hoF hJmax
  obtain ⟨⟨a, -, hJa, hJap⟩, -⟩ := hJgs
  have hJtc : IsTwoComponentIn J (centralizer ({a} : Set G)) := ⟨hJa, hJap⟩
  have hJinv : ∃ b ∈ J, orderOf b = 2 := by
    have h2' := h2
    rw [SectionRank.pRank_eq_open_pRank_top, ← SectionRank.pRank_eq_pRank_top_subgroup] at h2'
    exact exists_orderOf_eq_two_of_pRank (by omega)
  have hJne : J ≠ ⊥ := by
    obtain ⟨b, hbJ, hb2⟩ := hJinv
    intro h
    rw [h, mem_bot] at hbJ
    rw [hbJ, orderOf_one] at hb2
    norm_num at hb2
  refine ⟨?_, fun h3 g hc => ?_⟩
  ·
    set C := centralizer ({t} : Set G) with hC
    set T := zpowers t with hT
    have hCT : centralizer ((T : Subgroup G) : Set G) = C := by
      rw [hT, zpowers_eq_closure, centralizer_closure]
    have hT2 : IsPGroup 2 T := IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, ht, pow_one])
    have hTne : T ≠ ⊥ := by
      intro h
      rw [hT, zpowers_eq_bot] at h
      rw [h, orderOf_one] at ht
      norm_num at ht
    have hconj : ∀ g : G, conjugate J g ≤ C →
        IsTwoComponentIn (conjugate J g) (conjugate (centralizer ({a} : Set G)) g) ∧
          IsSolomonMaximal (conjugate J g) ∧ (∃ b ∈ conjugate J g, orderOf b = 2) ∧
          conjugate J g ≤ solomonKStarOf C := by
      intro g hg
      have hJgs : conjugate J g ∈ solomonKStar G := conjugate_mem_solomonKStar hJs g
      have hJgtc : IsTwoComponentIn (conjugate J g) (conjugate (centralizer ({a} : Set G)) g) :=
        isTwoComponentIn_map (MulAut.conj g⁻¹) hJtc
      refine ⟨hJgtc, hJgs.1, ?_, ?_⟩
      · obtain ⟨b, hbJ, hb2⟩ := hJinv
        refine ⟨(MulAut.conj g⁻¹) b, ⟨b, hbJ, rfl⟩, ?_⟩
        rw [MulEquiv.orderOf_eq, hb2]
      · have hTJg : T ≤ coreActionKernel (conjugate J g) := by
          rw [hT, zpowers_le]
          exact Sol78.mem_coreActionKernel_of_commute fun j hj =>
            mem_centralizer_singleton_iff.mp (hg hj)
        have h := lemma212Input G (conjugate J g) T hJgs hTne hT2 hTJg
        rwa [hCT, inf_eq_left.mpr hg, twoLayerIn_eq_self_of_isTwoComponentIn hJgtc] at h
    have hJ1 : conjugate J 1 = J := by
      ext x
      rw [SolAltLit.mem_conjugate_iff_conj, one_mul, inv_one, mul_one]
    have hJK : J ≤ solomonKStarOf C := by
      have h := (hconj 1 (by rw [hJ1]; exact hJt)).2.2.2
      rwa [hJ1] at h
    have hKTL : solomonKStarOf C ≤ twoLayerIn C :=
      iSup₂_le fun K hK => le_twoLayerIn_of_isTwoComponentIn hK.1
    obtain ⟨M, hMC, hJM⟩ := exists_not_le_coreActionKernel hJtc hJK hJinv
    have huniq : ∀ M' : Subgroup G, M' ∈ kStarComponents C → M' = M := by
      intro M' hM'
      by_contra hne
      rcases Foote5.SolMax.isKBalanced_or_psp4_of_centralizer
          (Sol76T13.R12.Pcls.quasisimpleRankTwoSymplecticInput_of_suz
              Sol76T13.R12.Pcls.sporadicCoverRankInput_Suz) hnab hK ht hMC hM' (Ne.symm hne)
        with hbal | ⟨k, _, _, hk, ⟨eM⟩⟩
      · exact h13 G inferInstance hnab hK C hbal
      · have hequiv := solomonEquiv_of_not_le_coreActionKernel ht hJtc hJmax hJt
          (hJK.trans hKTL) hMC.1 hJM
        obtain ⟨e⟩ := nonempty_fusionZStar_equiv_of_reflTransGen hequiv.2
        exact hpsp ⟨k, inferInstance, inferInstance, hk, ⟨e.trans eM⟩⟩
    have hKM : solomonKStarOf C = M :=
      le_antisymm (iSup₂_le fun K hK => (huniq K hK).le) (le_iSup₂_of_le M hMC le_rfl)
    have hMJ : ∀ {L CL : Subgroup G}, IsTwoComponentIn L CL → IsSolomonMaximal L →
        (∃ b ∈ L, orderOf b = 2) → L ≤ C → L ≤ solomonKStarOf C → L ⊔ oddCoreIn M = M := by
      intro L CL hL hLmax hLinv hLC hLK
      have hLperf : ⁅L, L⁆ = L := UnbalancedCorr.commutator_eq_of_isPComponent hL.1 hL.2
      have hLM : L ≤ M := hKM ▸ hLK
      have hequiv := solomonEquiv_of_not_le_coreActionKernel ht hL hLmax hLC (hLK.trans hKTL)
        hMC.1 (not_le_coreActionKernel_of_le hLM hLperf hLinv)
      obtain ⟨e⟩ := nonempty_fusionZStar_equiv_of_reflTransGen hequiv.2
      exact sup_oddCoreIn_eq_of_fusionZStar hL hMC.1 hLM hLinv e.symm
    have hJM' := hMJ hJtc hJmax hJinv hJt hJK
    refine iSup₂_le fun g hg => ?_
    obtain ⟨hJgtc, hJgmax, hJginv, hJgK⟩ := hconj g hg
    have hJgM := hMJ hJgtc hJgmax hJginv hg hJgK
    calc conjugate J g ≤ M := hJgM ▸ le_sup_left
      _ = J ⊔ oddCoreIn M := hJM'.symm
      _ ≤ oddCoreIn C ⊔ J :=
        sup_le le_sup_right ((oddCoreIn_le_of_isTwoComponentIn hMC.1).trans le_sup_left)
  ·
    have hle := sup_conjugate_le_solomonKStarOf_top
      (fun N hN => absurd hN (h13 G inferInstance hnab hK N)) hJtc hJs h3 g hc
    rw [solomonKStarOf_top_eq_bot_of_fStar hsF hnF] at hle
    exact hJne (le_bot_iff.mp (le_sup_left.trans hle))

theorem maximalTwoComponentSimple_at_of_gsMirrorMaximal
    (hCI : GSLit.ClassicalInvolutionInput) (hGA : TBLit.GriessMultipliersAllModels)
    {G : Type} [Group G] [Finite G] [IsSimpleGroup G]
    (hsF : IsSimpleGroup (GeneralizedFitting.subgroup G))
    (hnF : ∃ a b : GeneralizedFitting.subgroup G, a * b ≠ b * a)
    (hoF : ¬ Blueprint.OddLieType (GeneralizedFitting.subgroup G))
    (h13 : Sol76T13.SolomonThm13Simple) (hK : Assembly.KProper Blueprint.Catalog G)
    {J : Subgroup G} (hJgs : GrSLit.GSWeakMaximalComponent J) (h2 : 2 ≤ pRank 2 ↥J)
    (hpsp : ¬ ∃ (K : Type) (_ : Field K) (_ : Finite K), Odd (Nat.card K) ∧
        Nonempty (J ⧸ Open.fusionZStar J ≃*
          Assembly.LowTwoRank.StatedProj (Assembly.LowTwoRank.StatedSp 2 K)))
    (hJM : GSMirrorMaximal J) {t : G} (ht : orderOf t = 2)
    (hJt : J ≤ centralizer ({t} : Set G)) :
    (⨆ (g : G) (_ : conjugate J g ≤ centralizer ({t} : Set G)), conjugate J g) ≤
        (pPrimeCore 2 (centralizer ({t} : Set G))).map (centralizer ({t} : Set G)).subtype ⊔
          J ∧
      (3 ≤ pRank 2 ↥J → ∀ g : G, ¬ ⁅J, conjugate J g⁆ ≤
        (pPrimeCore 2 J).map J.subtype ⊓
          (pPrimeCore 2 (conjugate J g)).map (conjugate J g).subtype) := by
  obtain ⟨⟨a, ha, hJa, hJap⟩, -⟩ := id hJgs
  exact maximalTwoComponentSimple_at_of_solomonMaximal hCI hGA hsF hnF hoF h13 hK hJgs h2 hpsp
    (Foote5.SolMax.isSolomonMaximal_of_gsMirrorMaximal hsF hnF ha ⟨hJa, hJap⟩ hJM) ht hJt

theorem maximalTwoComponentSimple_l34
    (hCI : GSLit.ClassicalInvolutionInput) (hGA : TBLit.GriessMultipliersAllModels)
    (h13 : Sol76T13.SolomonThm13Simple) (hS : SchreierFor Blueprint.Catalog)
    (hCT : GrSLit.L34ProperFixedCenterTrivial) (hPFS : GrSLit.L34ProperFixedSimpleRank)
    (hEx : GrSLit.L34Sec5S.L34CyclicPumpUpExclusion) {G : Type} [Group G] [Finite G]
    (hG : GrSLit.L34BaseSetting G) (hsF : IsSimpleGroup (GeneralizedFitting.subgroup G))
    (hnF : ∃ a b : GeneralizedFitting.subgroup G, a * b ≠ b * a)
    (hoF : ¬ Blueprint.OddLieType (GeneralizedFitting.subgroup G))
    {J : Subgroup G} (hJgs : GrSLit.GSWeakMaximalComponent J) (h2 : 2 ≤ pRank 2 ↥J)
    (htype : GrSLit.IsL34Type (J ⧸ Open.fusionZStar J)) {t : G} (ht : orderOf t = 2)
    (hJt : J ≤ centralizer ({t} : Set G)) :
    (⨆ (g : G) (_ : conjugate J g ≤ centralizer ({t} : Set G)), conjugate J g) ≤
        (pPrimeCore 2 (centralizer ({t} : Set G))).map (centralizer ({t} : Set G)).subtype ⊔
          J ∧
      (3 ≤ pRank 2 ↥J → ∀ g : G, ¬ ⁅J, conjugate J g⁆ ≤
        (pPrimeCore 2 J).map J.subtype ⊓
          (pPrimeCore 2 (conjugate J g)).map (conjugate J g).subtype) := by
  obtain ⟨hsimple, -, hK, -⟩ := id hG
  have := hsimple
  exact maximalTwoComponentSimple_at_of_gsMirrorMaximal hCI hGA hsF hnF hoF h13 hK hJgs h2
    (Sol78.not_psp4_of_l34 htype)
    (GrSLit.L34Sec5S.gsMirrorMaximal_of_cyclicExclusion hS hCT hPFS hEx hG htype) ht hJt

end CFSG.ComponentClassification.Sol76

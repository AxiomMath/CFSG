module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34SuzStdOddDefs
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34SuzStdRank
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34SuzStdDefs

public section

namespace CFSG.ComponentClassification.GrSLit.L34Sec5S

open CFSG Subgroup

variable {G : Type} [Group G] [Finite G]

theorem l34SuzOddSetting_of_isPComponent_suz
    (hSch : LocalAnalysis.ComponentInitial.SchreierFor Blueprint.Catalog)
    (hC4 : SuzONanNotProperFixedCatalog) (hCI : GSLit.ClassicalInvolutionInput)
    (hGA : TBLit.GriessMultipliersAllModels) (h13 : Sol76T13.SolomonThm13Simple)
    (hCSuz : L34SuzCoreStepMirror) (hEven : L34SuzEvenStandardExclusion)
    (hAS : RankTwoSporadic.SporadicCaseOdd .Suz)
    (hCIT : StandardRecognition.ClassicalInvolutionTheoremModels)
    (h25 : EvenSporadicStandard.Finkelstein77.Asc76Lemma25) (hG : L34BaseSetting G) {b : G}
    (hb : orderOf b = 2) {M : Subgroup G} (hMb : M ≤ centralizer ({b} : Set G))
    (hM : IsPComponent 2 (M.subgroupOf (centralizer ({b} : Set G))))
    (hMs : Blueprint.NativeSporadic.IsSporadic (↥M ⧸ Open.fusionZStar ↥M) .Suz)
    (hMr : 3 ≤ pRank 2 ↥M) : L34SuzOddSetting M b := by
  obtain ⟨hsimple, hna, hK, -, hU, -, -, -⟩ := id hG
  have := hsimple
  obtain ⟨hsF, hnF, hoF⟩ := GrS5.fstar_facts hG
  have hMcomp : FooteLit.IsTwoComponentIn M (centralizer ({b} : Set G)) := ⟨hMb, hM⟩
  have hMs' : SuzONanFieldType (M ⧸ Open.fusionZStar M) := Or.inl hMs
  have hJw : GSWeakMaximalComponent M :=
    gsWeakMaximalComponent_of_suzONan hSch hC4 hG hb hMb hM (Or.inl hMs)
  have hJmm : FooteLit.GSMirrorMaximal M :=
    Foote5.SolMax.gsMirrorMaximal_of_suzONan hSch hC4 hna hK (Or.inl hMs)
  have hJsol : FooteLit.IsSolomonMaximal M :=
    Foote5.SolMax.isSolomonMaximal_of_suzONan hSch hC4 hna hsF hnF hK hb hMcomp (Or.inl hMs)
  obtain ⟨c, hc, hJc, hJcp⟩ := hJw.1
  have hT9 := fun (t : G) (ht : orderOf t = 2) (hJt : M ≤ centralizer ({t} : Set G)) =>
    Sol76.maximalTwoComponentSimple_at_of_solomonMaximal hCI hGA hsF hnF hoF h13 hK hJw
      (by omega) (not_psp4_of_suzONanFieldType hMs') hJsol ht hJt
  have hZ : ∀ g : G, g ≠ 1 → g ∉ center G := fun g hg hgZ =>
    hg (by rwa [CatLeaf.center_eq_bot_of_simple hna, mem_bot] at hgZ)
  obtain ⟨hst, hO⟩ := GrS5.isStandardSubgroup_of_cor211 hSch hK hZ hc hJc hJcp
    (fun t ht hJt => (hT9 t ht hJt).1) ((hT9 c hc hJc).2 hMr)
    (hCSuz G hG M hJmm hMs)
  have hq : IsQuasisimple ↥M := hst.1
  have hO' : pPrimeCore 2 ↥M ≤ center ↥M := by
    intro x hx
    obtain ⟨y, hy, hyx⟩ := hO ⟨x, hx, rfl⟩
    rwa [← Subtype.ext hyx]
  have heq := GrS5.fusionZStar_eq_center_of_le hq.1.commutator_eq_top hO'
  obtain ⟨e⟩ := hMs
  have hSuzCenter : Blueprint.NativeSporadic.IsSporadic (↥M ⧸ center ↥M) .Suz :=
    ⟨(QuotientGroup.quotientMulEquivOfEq heq.symm).trans e⟩
  rcases Nat.even_or_odd (Nat.card (center ↥M)) with he | ho
  · exact (hEven G hG M hst hSuzCenter he).elim
  · have hbM : b ∈ centralizer (M : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro m hm
      exact Subgroup.mem_centralizer_singleton_iff.mp (hMb hm)
    exact
      { base := hG
        standard := hst
        suz := hSuzCenter
        odd_card_center := ho
        card_sylow := fun S =>
          card_sylow_centralizer_eq_two_of_suz hAS hCIT h25 hna hK hU hst hSuzCenter S
        orderOf_t := hb
        t_mem := hbM }

end CFSG.ComponentClassification.GrSLit.L34Sec5S

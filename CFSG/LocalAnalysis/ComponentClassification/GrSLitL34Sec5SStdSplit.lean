module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec5SStdSolMax
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec5SCoreMirror
public import CFSG.LocalAnalysis.ComponentClassification.CTUMaxTwoAt
public import CFSG.LocalAnalysis.ComponentClassification.GoldschmidtTDGriess
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec5Cor211
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec5SStdCatL3Holds
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec5SStdCatSuzHolds
public import CFSG.RankThree.PartOne.SPOR.Final

public section

namespace CFSG.ComponentClassification.GrSLit.L34Sec5S

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer
open CFSG.EvenSporadicStandard.Induction (Sol78Thm46 Sol78Remark11 Sol78Thm11SuzONan)
open CFSG.LocalAnalysis.ComponentInitial (SchreierFor)

@[expose] def L34StandardExclusionAt (τ : ∀ (X : Type) [Group X], Prop) : Prop :=
  ∀ (G : Type) [Group G] [Finite G], L34BaseSetting G → ∀ (b : G) (J : Subgroup G),
    orderOf b = 2 → J ≤ centralizer ({b} : Set G) →
    IsPComponent 2 (J.subgroupOf (centralizer ({b} : Set G))) →
    τ (J ⧸ Open.fusionZStar J) → IsStandardSubgroup J →
    oddIn J ≤ (center ↥J).map J.subtype → False

@[expose] def L34SuzStandardExclusion : Prop :=
  L34StandardExclusionAt fun X _ => Blueprint.NativeSporadic.IsSporadic X .Suz

@[expose] def L34ONanStandardExclusion : Prop :=
  L34StandardExclusionAt fun X _ => Blueprint.NativeSporadic.IsSporadic X .ONan

@[expose] def L34FieldStandardExclusion : Prop :=
  L34StandardExclusionAt fun X _ => ∃ n : ℕ, 4 ≤ n ∧ Even n ∧ Blueprint.LieModel X .PSL 3 2 n

theorem l34StandardExclusionAt_of_split (hSuz : L34SuzStandardExclusion)
    (hON : L34ONanStandardExclusion) (hField : L34FieldStandardExclusion) :
    L34StandardExclusionAt SuzONanFieldType := by
  intro G _ _ hG b J hb hJb hJp hτ hst hO
  rcases hτ with h | h | h
  · exact hSuz G hG b J hb hJb hJp h hst hO
  · exact hON G hG b J hb hJb hJp h hst hO
  · exact hField G hG b J hb hJb hJp h hst hO

variable {G : Type} [Group G] [Finite G]

section Certified

theorem false_of_solomonMaximal_of_standardExclusion (hS : SchreierFor Blueprint.Catalog)
    (hCI : GSLit.ClassicalInvolutionInput) (hGA : TBLit.GriessMultipliersAllModels)
    (h13 : Sol76T13.SolomonThm13Simple) (hstd : L34StandardExclusionAt SuzONanFieldType)
    (hG : L34BaseSetting G) {J : Subgroup G} (hJw : GSWeakMaximalComponent J)
    (hJsol : FooteLit.IsSolomonMaximal J) (hJtype : SuzONanFieldType (J ⧸ Open.fusionZStar J))
    (hJrank : 3 ≤ pRank 2 ↥J)
    (hcore : ∀ b t : G, orderOf b = 2 → J ≤ centralizer ({b} : Set G) →
      IsPComponent 2 (J.subgroupOf (centralizer ({b} : Set G))) → orderOf t = 2 →
      b * t = t * b → J ≤ centralizer ({t} : Set G) →
      oddIn (pumpUp J t) ≤ (center ↥J).map J.subtype) : False := by
  obtain ⟨hsimple, hna, hK, -, -, -, -, -⟩ := id hG
  have := hsimple
  obtain ⟨hsF, hnF, hoF⟩ := GrS5.fstar_facts hG
  obtain ⟨c, hc, hJc, hJcp⟩ := hJw.1
  have hT9 := fun (t : G) (ht : orderOf t = 2) (hJt : J ≤ centralizer ({t} : Set G)) =>
    Sol76.maximalTwoComponentSimple_at_of_solomonMaximal hCI hGA hsF hnF hoF h13 hK hJw
      (by omega) (not_psp4_of_suzONanFieldType hJtype) hJsol ht hJt
  have hZ : ∀ g : G, g ≠ 1 → g ∉ center G := fun g hg hgZ =>
    hg (by rwa [CatLeaf.center_eq_bot_of_simple hna, mem_bot] at hgZ)
  obtain ⟨hst, hO⟩ := GrS5.isStandardSubgroup_of_cor211 hS hK hZ hc hJc hJcp
    (fun t ht hJt => (hT9 t ht hJt).1) ((hT9 c hc hJc).2 hJrank) hcore
  exact hstd G hG c J hc hJc hJcp hJtype hst hO

theorem l34SuzONanFieldPumpUpExclusion_of_mirrors
    (hS : SchreierFor Blueprint.Catalog) (hCI : GSLit.ClassicalInvolutionInput)
    (hGA : TBLit.GriessMultipliersAllModels) (h13 : Sol76T13.SolomonThm13Simple)
    (hC4 : SuzONanNotProperFixedCatalog) (hC5 : L3TwoPowProperFixedCatalog)
    (hstd : L34StandardExclusionAt SuzONanFieldType) (hcore : L34SuzONanFieldCoreStepMirror) :
    L34SuzONanFieldPumpUpExclusion := by
  intro G _ _ hG a b M T ha hb hab hMb hMp hMa hTM hTp hlt htype hrank hM
  obtain ⟨J, hJmm, hJw, hJsol, hJtype, hJrank⟩ :=
    exists_mirror_solomon_suzONanField hS hC4 hC5 hG hb hMb hMp hTM htype hM
  exact false_of_solomonMaximal_of_standardExclusion hS hCI hGA h13 hstd hG hJw hJsol hJtype
    hJrank (hcore G hG J hJmm hJtype)

section Holds

theorem l34SuzONanFieldPumpUpExclusion_of_residuals
    (hCI : GSLit.ClassicalInvolutionInput) (h13 : Sol76T13.SolomonThm13Simple)
    (hSSuz : L34SuzStandardExclusion) (hSON : L34ONanStandardExclusion)
    (hSField : L34FieldStandardExclusion) (hCSuz : L34SuzCoreStepMirror)
    (hCON : L34ONanCoreStepMirror) (hCField : L34FieldCoreStepMirror) :
    L34SuzONanFieldPumpUpExclusion :=
  l34SuzONanFieldPumpUpExclusion_of_mirrors RankThree.PartOne.SPOR.schreierFor_catalog hCI
    TBLit.griessMultipliersAllModels_holds h13 suzONanNotProperFixedCatalog_holds
    l3TwoPowProperFixedCatalog_holds (l34StandardExclusionAt_of_split hSSuz hSON hSField)
    (l34SuzONanFieldCoreStepMirror_of_split hCSuz hCON hCField)

end Holds

end Certified

end CFSG.ComponentClassification.GrSLit.L34Sec5S

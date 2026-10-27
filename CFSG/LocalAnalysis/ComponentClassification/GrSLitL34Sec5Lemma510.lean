module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec5Branch510
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec5Conj510
public import CFSG.LocalAnalysis.ComponentClassification.HSFLitL34InvStep
public import CFSG.LocalAnalysis.ComponentClassification.HSFLitL34UniqStep

public section

namespace CFSG.ComponentClassification.GrSLit.GrS5

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer
  CFSG.ComponentClassification.UnbalancedCorr CFSG.ComponentClassification.UnbalancedGS
open CFSG.LocalAnalysis.ComponentInitial (SchreierFor)

variable {G : Type} [Group G] [Finite G]

theorem false_of_unbalancing_max
    (hS : SchreierFor Blueprint.Catalog)
    (hU : CatalogueU.CatalogAlmostSimpleUnbalancedOutcome) (hheld : KProperRelativeB.HeldInput)
    (hSol : SolomonCommutingCoreInput) (hGW : GorensteinWalterConnectedInput)
    (hMax : MaximalTwoComponentInput) (hL34 : L34InvolutionCentralizerFact)
    (h58 : L34Lemma58) (h59 : L34Lemma59) (hElem : L34ElementaryCenterSylowFact)
    (hERank : L34ElementaryRankFact) (hMaxE : L34MaxElementaryThreeFact)
    (hUnit : L34UnbalancingUnitaryStep) (hUA : L34UnitaryAutFact)
    (hComp : L34Cor217ComponentStep)
    (hL2 : L2UnbalancingAutFact) (hLift : L34SylowCentralLiftFact) (hSC : L34AutSylowCenterFact)
    (hStd : GSThmB.L34StandardEvenInput) (h41 : L34Prop41)
    (hCen : L34Lemma510CentralStep)
    (hBd : L34Lemma510OTwoBoundStep) (hType : HSFLit.L34Inv.L34Lemma55TypeStep)
    (hCenter : HSFLit.L34Uniq.L34Lemma511CenterStep) (hPair : HSFLit.L34Uniq.L34Lemma511PairStep)
    {L : Subgroup G} {t : G} {S T : Subgroup G} (hset : L34Sec5Setting G L t S T) {u : G}
    (hu : u ∈ L34UnbalancingSet L t S)
    (hmax : ∀ v ∈ L34UnbalancingSet L t S, Nat.card ↥(oddIn L ⊓ centralizer ({v} : Set G)) ≤
      Nat.card ↥(oddIn L ⊓ centralizer ({u} : Set G))) : False := by
  have hInv := HSFLit.L34Inv.l34Lemma510InvolutionStep_of_inputs hS hU hheld hSol hGW hMax hL34 h59
    hType
  have hUniq := HSFLit.L34Uniq.l34Lemma511UniqueStep_of_inputs hS hU hheld hSol hGW hMax hL34 h58
    h59 hSC hCenter hPair
  obtain ⟨u', hu', huc, hmax'⟩ := exists_central_unbalancing_of_facts hS hU hheld hSol hGW h58 h59
    hLift hCen hset hu hmax
  obtain ⟨-, hLt, hLpt⟩ := eq_of_mem_inf_centralizer hS hU hheld hSol hGW hset
  have hZS := mem_center_of_setting hS hU hheld hSol hGW hset
  have hset' := hset
  obtain ⟨hbase, ⟨⟨-, -, -, -, -, hto, -, -⟩, -⟩, -, -, htS, -, -⟩ := hset'
  have hu'' := hu'
  obtain ⟨huS₀, hu2, hun⟩ := hu''
  have huS : u' ∈ S := (sup_le inf_le_left (zpowers_le.mpr htS) : S ⊓ L ⊔ zpowers t ≤ S) huS₀
  have htu : t * u' = u' * t := (hZS u' huS).symm
  have hYD : oddIn L ⊓ centralizer ({u'} : Set G) ≤
      oddIn (centralizer ({t} : Set G)) ⊓ centralizer ({u'} : Set G) :=
    inf_le_inf_right _ (GSLit.map_pPrimeCore_le_of_isPComponent hLt hLpt)
  have hall : ∀ K₁ : Subgroup G, K₁ ≤ centralizer ({u'} : Set G) →
      IsPComponent 2 (K₁.subgroupOf (centralizer ({u'} : Set G))) →
      ¬ ⁅K₁, oddIn L ⊓ centralizer ({u'} : Set G)⁆ ≤ oddIn K₁ →
      IsL2Type 5 (K₁ ⧸ pPrimeCore 2 K₁) ∨ IsL2Type 7 (K₁ ⧸ pPrimeCore 2 K₁) := by
    intro K₁ hK₁u hK₁p hK₁n
    rcases hbase.2.2.2.2.2.2.2 u' t K₁
      (gsUnbalancingTriple_of_not_le hSol hto hu2 htu hK₁u hK₁p hYD hK₁n) with h | h | h
    · exact Or.inl h
    · exact Or.inr h
    · exact (false_of_isL34Type_component_central hS hU hheld hSol hGW hMax hL34 h58 h59 hElem
        hERank hMaxE hUnit hUA hComp hStd h41 hBd hInv hset hu' huc hmax' hK₁u hK₁p hK₁n
        h).elim
  obtain ⟨K₁, hK₁u, hK₁p, hK₁n⟩ := exists_isPComponent_not_le hSol hto hu2 htu hYD hun
  exact false_of_isL2Type_component_central hS hU hheld hSol hGW hMax hL34 h58 h59 hElem hERank
    hMaxE hL2 hInv hUniq hset hu' huc hmax' hall hK₁u hK₁p hK₁n

theorem l34Lemma510_of_inputs
    (hS : SchreierFor Blueprint.Catalog)
    (hU : CatalogueU.CatalogAlmostSimpleUnbalancedOutcome) (hheld : KProperRelativeB.HeldInput)
    (hSol : SolomonCommutingCoreInput) (hGW : GorensteinWalterConnectedInput)
    (hMax : MaximalTwoComponentInput) (hL34 : L34InvolutionCentralizerFact)
    (h58 : L34Lemma58) (h59 : L34Lemma59) (hElem : L34ElementaryCenterSylowFact)
    (hERank : L34ElementaryRankFact) (hMaxE : L34MaxElementaryThreeFact)
    (hUnit : L34UnbalancingUnitaryStep) (hUA : L34UnitaryAutFact)
    (hComp : L34Cor217ComponentStep)
    (hL2 : L2UnbalancingAutFact) (hLift : L34SylowCentralLiftFact) (hSC : L34AutSylowCenterFact)
    (hStd : GSThmB.L34StandardEvenInput) (h41 : L34Prop41)
    (hCen : L34Lemma510CentralStep)
    (hBd : L34Lemma510OTwoBoundStep) (hType : HSFLit.L34Inv.L34Lemma55TypeStep)
    (hCenter : HSFLit.L34Uniq.L34Lemma511CenterStep)
    (hPair : HSFLit.L34Uniq.L34Lemma511PairStep) : L34Lemma510 := by
  intro G _ _ L t S T hset u hu hmax
  exact (false_of_unbalancing_max hS hU hheld hSol hGW hMax hL34 h58 h59 hElem hERank hMaxE hUnit
    hUA hComp hL2 hLift hSC hStd h41 hCen hBd hType hCenter hPair hset hu hmax).elim

theorem l34Lemma511_of_inputs
    (hS : SchreierFor Blueprint.Catalog)
    (hU : CatalogueU.CatalogAlmostSimpleUnbalancedOutcome) (hheld : KProperRelativeB.HeldInput)
    (hSol : SolomonCommutingCoreInput) (hGW : GorensteinWalterConnectedInput)
    (hMax : MaximalTwoComponentInput) (hL34 : L34InvolutionCentralizerFact)
    (h58 : L34Lemma58) (h59 : L34Lemma59) (hElem : L34ElementaryCenterSylowFact)
    (hERank : L34ElementaryRankFact) (hMaxE : L34MaxElementaryThreeFact)
    (hUnit : L34UnbalancingUnitaryStep) (hUA : L34UnitaryAutFact)
    (hComp : L34Cor217ComponentStep)
    (hL2 : L2UnbalancingAutFact) (hLift : L34SylowCentralLiftFact) (hSC : L34AutSylowCenterFact)
    (hStd : GSThmB.L34StandardEvenInput) (h41 : L34Prop41)
    (hCen : L34Lemma510CentralStep)
    (hBd : L34Lemma510OTwoBoundStep) (hType : HSFLit.L34Inv.L34Lemma55TypeStep)
    (hCenter : HSFLit.L34Uniq.L34Lemma511CenterStep)
    (hPair : HSFLit.L34Uniq.L34Lemma511PairStep) : L34Lemma511 := by
  intro G _ _ L t S T hset u hu hmax _
  exact false_of_unbalancing_max hS hU hheld hSol hGW hMax hL34 h58 h59 hElem hERank hMaxE hUnit
    hUA hComp hL2 hLift hSC hStd h41 hCen hBd hType hCenter hPair hset hu hmax

end CFSG.ComponentClassification.GrSLit.GrS5

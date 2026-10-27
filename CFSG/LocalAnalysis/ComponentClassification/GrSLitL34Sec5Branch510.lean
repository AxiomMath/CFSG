module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec5Central510
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec5OTwo510
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec5Cor217Invt

public section

namespace CFSG.ComponentClassification.GrSLit.GrS5

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer
  CFSG.ComponentClassification.UnbalancedCorr CFSG.ComponentClassification.UnbalancedGS
open CFSG.LocalAnalysis.ComponentInitial (SchreierFor)

variable {G : Type} [Group G] [Finite G]

theorem false_of_isL34Type_component_central
    (hS : SchreierFor Blueprint.Catalog)
    (hU : CatalogueU.CatalogAlmostSimpleUnbalancedOutcome) (hheld : KProperRelativeB.HeldInput)
    (hSol : SolomonCommutingCoreInput) (hGW : GorensteinWalterConnectedInput)
    (hMax : MaximalTwoComponentInput) (hL34 : L34InvolutionCentralizerFact)
    (h58 : L34Lemma58) (h59 : L34Lemma59) (hElem : L34ElementaryCenterSylowFact)
    (hERank : L34ElementaryRankFact) (hMaxE : L34MaxElementaryThreeFact)
    (hUnit : L34UnbalancingUnitaryStep) (hUA : L34UnitaryAutFact)
    (hComp : L34Cor217ComponentStep) (hStd : GSThmB.L34StandardEvenInput)
    (h41 : L34Prop41) (hBd : L34Lemma510OTwoBoundStep) (hInv : L34Lemma510InvolutionStep)
    {L : Subgroup G} {t : G} {S T : Subgroup G} (hset : L34Sec5Setting G L t S T) {u : G}
    (hu : u ∈ L34UnbalancingSet L t S) (huc : ∀ s ∈ S, s * u = u * s)
    (hmax : ∀ v ∈ L34UnbalancingSet L t S, Nat.card ↥(oddIn L ⊓ centralizer ({v} : Set G)) ≤
      Nat.card ↥(oddIn L ⊓ centralizer ({u} : Set G))) {K₁ : Subgroup G}
    (hK₁u : K₁ ≤ centralizer ({u} : Set G))
    (hK₁p : IsPComponent 2 (K₁.subgroupOf (centralizer ({u} : Set G))))
    (hK₁n : ¬ ⁅K₁, oddIn L ⊓ centralizer ({u} : Set G)⁆ ≤ oddIn K₁)
    (htype₁ : IsL34Type (K₁ ⧸ Open.fusionZStar K₁)) : False := by
  obtain ⟨-, hLt, hLpt⟩ := eq_of_mem_inf_centralizer hS hU hheld hSol hGW hset
  have hZS := mem_center_of_setting hS hU hheld hSol hGW hset
  have hset' := hset
  obtain ⟨-, ⟨⟨-, -, -, -, -, hto, -, -⟩, -⟩, -, hSyl, htS, -, -⟩ := hset'
  have hS2 : IsPGroup 2 S := IsSylowTwoIn.isPGroup hSyl
  have hu' := hu
  obtain ⟨huS₀, hu2, -⟩ := hu'
  have huS : u ∈ S := (sup_le inf_le_left (zpowers_le.mpr htS) : S ⊓ L ⊔ zpowers t ≤ S) huS₀
  have htu : t * u = u * t := (hZS u huS).symm
  have hYD : oddIn L ⊓ centralizer ({u} : Set G) ≤
      oddIn (centralizer ({t} : Set G)) ⊓ centralizer ({u} : Set G) :=
    inf_le_inf_right _ (GSLit.map_pPrimeCore_le_of_isPComponent hLt hLpt)
  have hT₁ := gsUnbalancingTriple_of_not_le hSol hto hu2 htu hK₁u hK₁p hYD hK₁n
  have hRN :=
    l34Sec5ComponentInvariantStep_of_comp hMax hComp G L t S T hset u huS₀ hu2 K₁ hK₁u hK₁p hK₁n
      htype₁
  have hSN : S ≤ normalizer (K₁ : Set G) := fun s hs =>
    hRN (mem_inf.mpr ⟨hs, mem_centralizer_singleton_iff.mpr (huc s hs)⟩)
  obtain ⟨-, hrk, -⟩ := hUA G K₁ S t (GSThmB.commutator_eq_self_of_isPComponent hK₁u hK₁p)
    htype₁ (hUnit G u t K₁ hT₁ htype₁) hS2
    (le_inf hSN fun s hs => mem_centralizer_singleton_iff.mpr (hZS s hs))
  exact false_of_component_of_central hS hU hheld hSol hGW hMax hL34 h58 h59 hElem hERank hMaxE
    hInv hset hu huc hmax hK₁u hK₁p hK₁n hSN hrk fun hO =>
      Or.inl ⟨htype₁, l34Lemma510OTwoStep_of_inputs hS hU hheld hSol hGW hMax hStd h58 h59 hUnit
        hUA hComp h41 hElem hBd G L t S T hset u hu huc hmax K₁ hK₁u hK₁p hK₁n htype₁ hO⟩

theorem false_of_isL2Type_component_central
    (hS : SchreierFor Blueprint.Catalog)
    (hU : CatalogueU.CatalogAlmostSimpleUnbalancedOutcome) (hheld : KProperRelativeB.HeldInput)
    (hSol : SolomonCommutingCoreInput) (hGW : GorensteinWalterConnectedInput)
    (hMax : MaximalTwoComponentInput) (hL34 : L34InvolutionCentralizerFact)
    (h58 : L34Lemma58) (h59 : L34Lemma59) (hElem : L34ElementaryCenterSylowFact)
    (hERank : L34ElementaryRankFact) (hMaxE : L34MaxElementaryThreeFact)
    (hL2 : L2UnbalancingAutFact) (hInv : L34Lemma510InvolutionStep)
    (hUniq : L34Lemma511UniqueStep)
    {L : Subgroup G} {t : G} {S T : Subgroup G} (hset : L34Sec5Setting G L t S T) {u : G}
    (hu : u ∈ L34UnbalancingSet L t S) (huc : ∀ s ∈ S, s * u = u * s)
    (hmax : ∀ v ∈ L34UnbalancingSet L t S, Nat.card ↥(oddIn L ⊓ centralizer ({v} : Set G)) ≤
      Nat.card ↥(oddIn L ⊓ centralizer ({u} : Set G)))
    (hall : ∀ K₁ : Subgroup G, K₁ ≤ centralizer ({u} : Set G) →
      IsPComponent 2 (K₁.subgroupOf (centralizer ({u} : Set G))) →
      ¬ ⁅K₁, oddIn L ⊓ centralizer ({u} : Set G)⁆ ≤ oddIn K₁ →
      IsL2Type 5 (K₁ ⧸ pPrimeCore 2 K₁) ∨ IsL2Type 7 (K₁ ⧸ pPrimeCore 2 K₁)) {K₁ : Subgroup G}
    (hK₁u : K₁ ≤ centralizer ({u} : Set G))
    (hK₁p : IsPComponent 2 (K₁.subgroupOf (centralizer ({u} : Set G))))
    (hK₁n : ¬ ⁅K₁, oddIn L ⊓ centralizer ({u} : Set G)⁆ ≤ oddIn K₁) : False := by
  obtain ⟨-, hLt, hLpt⟩ := eq_of_mem_inf_centralizer hS hU hheld hSol hGW hset
  have hZS := mem_center_of_setting hS hU hheld hSol hGW hset
  have hset' := hset
  obtain ⟨-, ⟨⟨-, -, -, -, -, hto, -, -⟩, -⟩, -, -, htS, -, -⟩ := hset'
  have hu' := hu
  obtain ⟨huS₀, hu2, -⟩ := hu'
  have huS : u ∈ S := (sup_le inf_le_left (zpowers_le.mpr htS) : S ⊓ L ⊔ zpowers t ≤ S) huS₀
  have htu : t * u = u * t := (hZS u huS).symm
  have hYD : oddIn L ⊓ centralizer ({u} : Set G) ≤
      oddIn (centralizer ({t} : Set G)) ⊓ centralizer ({u} : Set G) :=
    inf_le_inf_right _ (GSLit.map_pPrimeCore_le_of_isPComponent hLt hLpt)
  have hT₁ := gsUnbalancingTriple_of_not_le hSol hto hu2 htu hK₁u hK₁p hYD hK₁n
  have htype := hall K₁ hK₁u hK₁p hK₁n
  have hSN := hUniq G L t S T hset u hu huc hmax hall K₁ hK₁u hK₁p hK₁n
  have hrk : ∀ E : Subgroup G, E ≤ S → IsElemTwo E →
      Nat.card E ≤ 8 * Nat.card ↥(E ⊓ coreActionKernel K₁) := by
    intro E hES hEl
    obtain ⟨h1, -⟩ := hL2 G u t K₁ E hT₁ htype hEl.isPGroup
    obtain ⟨-, h2⟩ := h1 fun e he =>
      mem_inf.mpr ⟨hSN (hES he), mem_centralizer_singleton_iff.mpr (hZS e (hES he))⟩
    omega
  exact false_of_component_of_central hS hU hheld hSol hGW hMax hL34 h58 h59 hElem hERank hMaxE
    hInv hset hu huc hmax hK₁u hK₁p hK₁n hSN hrk fun _ => Or.inr htype

end CFSG.ComponentClassification.GrSLit.GrS5

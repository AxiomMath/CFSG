module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec5Third510
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec5Comp510
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec5Inputs510
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec4Basic

public section

namespace CFSG.ComponentClassification.GrSLit.GrS5

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer
  CFSG.ComponentClassification.UnbalancedCorr CFSG.ComponentClassification.UnbalancedGS
open CFSG.LocalAnalysis.ComponentInitial (SchreierFor)

variable {G : Type} [Group G] [Finite G]

theorem false_of_component_of_central
    (hS : SchreierFor Blueprint.Catalog)
    (hU : CatalogueU.CatalogAlmostSimpleUnbalancedOutcome) (hheld : KProperRelativeB.HeldInput)
    (hSol : SolomonCommutingCoreInput) (hGW : GorensteinWalterConnectedInput)
    (hMax : MaximalTwoComponentInput) (hL34 : L34InvolutionCentralizerFact)
    (h58 : L34Lemma58) (h59 : L34Lemma59) (hElem : L34ElementaryCenterSylowFact)
    (hERank : L34ElementaryRankFact) (hMaxE : L34MaxElementaryThreeFact)
    (hInv : L34Lemma510InvolutionStep)
    {L : Subgroup G} {t : G} {S T : Subgroup G} (hset : L34Sec5Setting G L t S T) {u : G}
    (hu : u ∈ L34UnbalancingSet L t S) (huc : ∀ s ∈ S, s * u = u * s)
    (hmax : ∀ v ∈ L34UnbalancingSet L t S, Nat.card ↥(oddIn L ⊓ centralizer ({v} : Set G)) ≤
      Nat.card ↥(oddIn L ⊓ centralizer ({u} : Set G))) {K₁ : Subgroup G}
    (hK₁u : K₁ ≤ centralizer ({u} : Set G))
    (hK₁p : IsPComponent 2 (K₁.subgroupOf (centralizer ({u} : Set G))))
    (hK₁n : ¬ ⁅K₁, oddIn L ⊓ centralizer ({u} : Set G)⁆ ≤ oddIn K₁)
    (hSN : S ≤ normalizer (K₁ : Set G))
    (hrk : ∀ E : Subgroup G, E ≤ S → IsElemTwo E →
      Nat.card E ≤ 8 * Nat.card ↥(E ⊓ coreActionKernel K₁))
    (htype : (∀ x ∈ oddIn K₁, ∀ k ∈ K₁, x * k = k * x) →
      ((IsL34Type (K₁ ⧸ Open.fusionZStar K₁) ∧ Odd (Nat.card ↥(zStarIn K₁))) ∨
        IsL2Type 5 (K₁ ⧸ pPrimeCore 2 K₁) ∨ IsL2Type 7 (K₁ ⧸ pPrimeCore 2 K₁))) : False := by
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
  have hO := oddIn_le_center_of_component hS hU hheld hSol hGW h58 h59 hElem hset hu2 huc hK₁u
    hK₁p hSN hrk
  obtain ⟨z₁, hz₁Q, hz₁o, hz₁t, hz₁K⟩ :=
    hInv G L t S T hset u hu huc hmax K₁ hK₁u hK₁p hK₁n hSN hO (htype hO)
  have hinv := conj_eq_inv_of_setting hS hU hheld hSol hGW hMax hL34 hset hz₁Q hz₁o hz₁t
  obtain ⟨hDN, -⟩ := (solomon_involutions hSol hto hu2 htu).2 K₁ hK₁u hK₁p
  have hodd : Odd (Nat.card ↥(oddIn L ⊓ centralizer ({u} : Set G))) := by
    have h1 : Odd (Nat.card (oddIn L)) := by
      rw [oddIn, card_map_of_injective (subtype_injective _)]
      exact Nat.coprime_two_left.mp pPrimeCore_coprime_card
    exact Odd.of_dvd_nat h1 (Subgroup.card_dvd_of_le inf_le_left)
  have hXK : oddIn L ⊓ centralizer ({u} : Set G) ≤ K₁ :=
    le_of_conj_eq_inv hz₁K (fun d hd => hDN (hYD hd)) (fun d hd => hinv d (mem_inf.mp hd).1) hodd
  exact false_of_oddIn_inf_le_component hS hU hheld hSol hGW h58 hERank hMaxE hset hmax
    (GSThmB.commutator_eq_self_of_isPComponent hK₁u hK₁p) hO (GrS4.not_mem_coreActionKernel hT₁)
    hrk hXK

end CFSG.ComponentClassification.GrSLit.GrS5

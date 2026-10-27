module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec5SBadEight
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec5InputsBadEight
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec5SCoverStep

public section

namespace CFSG.ComponentClassification.GrSLit.GrS5S

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer
  CFSG.ComponentClassification.UnbalancedCorr CFSG.ComponentClassification.UnbalancedGS
  CFSG.ComponentClassification.GrSLit CFSG.ComponentClassification.GrSLit.GrS5
open CFSG.LocalAnalysis.ComponentInitial (SchreierFor)

variable {G : Type} [Group G] [Finite G]

theorem false_of_cover_involution
    (hS : SchreierFor Blueprint.Catalog)
    (hU : CatalogueU.CatalogAlmostSimpleUnbalancedOutcome) (hheld : KProperRelativeB.HeldInput)
    (hSol : SolomonCommutingCoreInput) (hGW : GorensteinWalterConnectedInput)
    (hMax : MaximalTwoComponentInput) (hL34 : L34InvolutionCentralizerFact) (h58 : L34Lemma58)
    (hERank : L34ElementaryRankFact) (hMaxE : L34MaxElementaryThreeFact)
    (hUnit : L34UnbalancingUnitaryStep) (hUA : L34UnitaryAutFact)
    {L : Subgroup G} {t : G} {S T : Subgroup G} (hset : L34Sec5Setting G L t S T) {u : G}
    (hu : u ∈ L34UnbalancingSet L t S)
    (hmax : ∀ v ∈ L34UnbalancingSet L t S, Nat.card ↥(oddIn L ⊓ centralizer ({v} : Set G)) ≤
      Nat.card ↥(oddIn L ⊓ centralizer ({u} : Set G))) {K₁ : Subgroup G}
    (hK₁u : K₁ ≤ centralizer ({u} : Set G))
    (hK₁p : IsPComponent 2 (K₁.subgroupOf (centralizer ({u} : Set G))))
    (hK₁n : ¬ ⁅K₁, oddIn L ⊓ centralizer ({u} : Set G)⁆ ≤ oddIn K₁)
    (htype₁ : IsL34Type (K₁ ⧸ Open.fusionZStar K₁)) (hO : ∀ x ∈ oddIn K₁, ∀ k ∈ K₁, x * k = k * x)
    (hSN : S ≤ normalizer (K₁ : Set G)) {z₁ : G} (hz₁Q : z₁ ∈ S ⊓ coreActionKernel L)
    (hz₁o : orderOf z₁ = 2) (hz₁t : z₁ ≠ t) (hz₁K : z₁ ∈ K₁) : False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
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
  have hYodd : Odd (Nat.card ↥(oddIn L ⊓ centralizer ({u} : Set G))) := by
    have h1 : Odd (Nat.card (oddIn L)) := by
      rw [oddIn, card_map_of_injective (subtype_injective _)]
      exact Nat.coprime_two_left.mp pPrimeCore_coprime_card
    exact Odd.of_dvd_nat h1 (Subgroup.card_dvd_of_le inf_le_left)
  have hT₁ := gsUnbalancingTriple_of_not_le hSol hto hu2 htu hK₁u hK₁p hYD hK₁n
  have hperf₁ : ⁅K₁, K₁⁆ = K₁ := GSThmB.commutator_eq_self_of_isPComponent hK₁u hK₁p
  have hunit := hUnit G u t K₁ hT₁ htype₁
  obtain ⟨-, hrk, -⟩ := hUA G K₁ S t hperf₁ htype₁ hunit hS2
    (le_inf hSN fun s hs => mem_centralizer_singleton_iff.mpr (hZS s hs))
  obtain ⟨hDN, -⟩ := (solomon_involutions hSol hto hu2 htu).2 K₁ hK₁u hK₁p
  have hinv := conj_eq_inv_of_setting hS hU hheld hSol hGW hMax hL34 hset hz₁Q hz₁o hz₁t
  have hXK : oddIn L ⊓ centralizer ({u} : Set G) ≤ K₁ :=
    le_of_conj_eq_inv hz₁K (fun d hd => hDN (hYD hd)) (fun d hd => hinv d (mem_inf.mp hd).1)
      hYodd
  exact false_of_oddIn_inf_le_component hS hU hheld hSol hGW h58 hERank hMaxE hset hmax hperf₁
    hO (fun h => hunit.2.2.1 (mem_sup_right h)) hrk hXK

theorem l34Lemma510BadEightStep_of_cover
    (hS : SchreierFor Blueprint.Catalog)
    (hU : CatalogueU.CatalogAlmostSimpleUnbalancedOutcome) (hheld : KProperRelativeB.HeldInput)
    (hSol : SolomonCommutingCoreInput) (hGW : GorensteinWalterConnectedInput)
    (hMax : MaximalTwoComponentInput) (hL34 : L34InvolutionCentralizerFact) (h58 : L34Lemma58)
    (h59 : L34Lemma59) (hSC : L34AutSylowCenterFact) (hUnit : L34UnbalancingUnitaryStep)
    (hUA : L34UnitaryAutFact) (hERank : L34ElementaryRankFact)
    (hMaxE : L34MaxElementaryThreeFact) (hCov : L34Lemma510CoverInvolutionStep) :
    L34Lemma510BadEightStep := by
  intro G _ _ L t S T hset u hu huc hmax K₁ hK₁u hK₁p hK₁n htype₁ hO S₁ hS₁ hSS₁ b hb hbo hbc
    _ hW v₀ hv₀ hK₁v₀ hfam hsup hne h1 h2 h3
  exfalso
  by_cases hbu : b = u
  · obtain ⟨z₁, hz₁Q, hz₁o, hz₁t, hz₁K⟩ := hCov G L t S T hset u hu huc hmax K₁ hK₁u hK₁p hK₁n
      htype₁ hO S₁ hS₁ hSS₁ (by rw [← hbu]; exact (mem_inf.mp hb).2) (by rw [← hbu]; exact hbc)
      hW v₀ hv₀ hK₁v₀ hfam hsup (by rw [← hbu]; exact hne) h1 h2 h3
    exact false_of_cover_involution hS hU hheld hSol hGW hMax hL34 h58 hERank hMaxE hUnit hUA hset
      hu hmax hK₁u hK₁p hK₁n htype₁ hO (hSS₁.trans hS₁.1) hz₁Q hz₁o hz₁t hz₁K
  · exact false_of_bad_ne hS hU hheld hSol hGW hMax hL34 h58 h59 hSC hUnit hset hu hmax hK₁u
      hK₁p hK₁n htype₁ hO hS₁ hSS₁ hb hbo hbc h1 h3 hbu

end CFSG.ComponentClassification.GrSLit.GrS5S

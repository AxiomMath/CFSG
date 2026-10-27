module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec5Tools582
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec5InputsCov
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec4Basic

public section

namespace CFSG.ComponentClassification.GrSLit.GrS5

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer
  CFSG.ComponentClassification.UnbalancedCorr CFSG.ComponentClassification.UnbalancedGS
open CFSG.LocalAnalysis.ComponentInitial (SchreierFor)

variable {G : Type} [Group G] [Finite G]

theorem not_mem_coreActionKernel_of_involution
    (hS : SchreierFor Blueprint.Catalog)
    (hU : CatalogueU.CatalogAlmostSimpleUnbalancedOutcome) (hheld : KProperRelativeB.HeldInput)
    (hSol : SolomonCommutingCoreInput) (hGW : GorensteinWalterConnectedInput)
    (hMax : MaximalTwoComponentInput) (hL34 : L34InvolutionCentralizerFact)
    {L : Subgroup G} {t : G} {S T : Subgroup G} (hset : L34Sec5Setting G L t S T) {u : G}
    (hu2 : orderOf u = 2) (htu : t * u = u * t) {K₁ : Subgroup G}
    (hK₁u : K₁ ≤ centralizer ({u} : Set G))
    (hK₁p : IsPComponent 2 (K₁.subgroupOf (centralizer ({u} : Set G))))
    (hK₁n : ¬ ⁅K₁, oddIn L ⊓ centralizer ({u} : Set G)⁆ ≤ oddIn K₁) {w : G}
    (hwQ : w ∈ S ⊓ coreActionKernel L) (hw : orderOf w = 2) : w ∉ coreActionKernel K₁ := by
  obtain ⟨-, hLt, hLpt⟩ := eq_of_mem_inf_centralizer hS hU hheld hSol hGW hset
  have hset' := hset
  obtain ⟨-, ⟨⟨-, -, -, -, -, hto, -, -⟩, -⟩, -⟩ := hset'
  have hYD : oddIn L ⊓ centralizer ({u} : Set G) ≤
      oddIn (centralizer ({t} : Set G)) ⊓ centralizer ({u} : Set G) :=
    inf_le_inf_right _ (GSLit.map_pPrimeCore_le_of_isPComponent hLt hLpt)
  by_cases hwt : w = t
  · rw [hwt]
    exact GrS4.not_mem_coreActionKernel
      (gsUnbalancingTriple_of_not_le hSol hto hu2 htu hK₁u hK₁p hYD hK₁n)
  · intro hwK
    have hinv := conj_eq_inv_of_setting hS hU hheld hSol hGW hMax hL34 hset hwQ hw hwt
    obtain ⟨hDN, -⟩ := (solomon_involutions hSol hto hu2 htu).2 K₁ hK₁u hK₁p
    have hodd : Odd (Nat.card (oddIn L)) := by
      rw [oddIn, card_map_of_injective (subtype_injective _)]
      exact Nat.coprime_two_left.mp pPrimeCore_coprime_card
    apply hK₁n
    rw [commutator_le]
    intro k hk d hd
    have hdX : d ∈ oddIn L := (mem_inf.mp hd).1
    have hdo : Odd (orderOf d) := by
      have h1 := orderOf_dvd_natCard (⟨d, hdX⟩ : oddIn L)
      rw [Subgroup.orderOf_mk] at h1
      exact Odd.of_dvd_nat hodd h1
    have hdK := mem_coreActionKernel_of_conj_eq_inv (hDN (hYD hd)) hdo hwK (hinv d hdX)
    have h1 := (mem_coreActionKernel.mp (inv_mem hdK)).2 k⁻¹ (inv_mem hk)
    rw [inv_inv, inv_inv] at h1
    rwa [commutatorElement_def]

theorem false_of_isL2Type_of_mem_normalizer
    (hS : SchreierFor Blueprint.Catalog)
    (hU : CatalogueU.CatalogAlmostSimpleUnbalancedOutcome) (hheld : KProperRelativeB.HeldInput)
    (hSol : SolomonCommutingCoreInput) (hGW : GorensteinWalterConnectedInput)
    (hMax : MaximalTwoComponentInput) (hL34 : L34InvolutionCentralizerFact)
    (hL2 : L2UnbalancingAutFact)
    {L : Subgroup G} {t : G} {S T : Subgroup G} (hset : L34Sec5Setting G L t S T) {u : G}
    (hu2 : orderOf u = 2) (htu : t * u = u * t) {K₁ : Subgroup G}
    (hK₁u : K₁ ≤ centralizer ({u} : Set G))
    (hK₁p : IsPComponent 2 (K₁.subgroupOf (centralizer ({u} : Set G))))
    (hK₁n : ¬ ⁅K₁, oddIn L ⊓ centralizer ({u} : Set G)⁆ ≤ oddIn K₁)
    (htype : IsL2Type 5 (K₁ ⧸ pPrimeCore 2 K₁) ∨ IsL2Type 7 (K₁ ⧸ pPrimeCore 2 K₁)) {y : G}
    (hyQ : y ∈ S ⊓ coreActionKernel L) (hy4 : orderOf y = 4)
    (hyN : y ∈ normalizer (K₁ : Set G)) : False := by
  obtain ⟨-, hLt, hLpt⟩ := eq_of_mem_inf_centralizer hS hU hheld hSol hGW hset
  have hZS := mem_center_of_setting hS hU hheld hSol hGW hset
  have hset' := hset
  obtain ⟨-, ⟨⟨-, -, -, -, -, hto, -, -⟩, -⟩, -, hSyl, -, -, -⟩ := hset'
  have hYD : oddIn L ⊓ centralizer ({u} : Set G) ≤
      oddIn (centralizer ({t} : Set G)) ⊓ centralizer ({u} : Set G) :=
    inf_le_inf_right _ (GSLit.map_pPrimeCore_le_of_isPComponent hLt hLpt)
  have hT₁ := gsUnbalancingTriple_of_not_le hSol hto hu2 htu hK₁u hK₁p hYD hK₁n
  have hyS : y ∈ S := (mem_inf.mp hyQ).1
  have hyt : y ∈ centralizer ({t} : Set G) := mem_centralizer_singleton_iff.mpr (hZS y hyS)
  have hR2 : IsPGroup 2 (zpowers y) :=
    (IsSylowTwoIn.isPGroup hSyl).to_le (zpowers_le.mpr hyS)
  obtain ⟨h1, -⟩ := hL2 G u t K₁ (zpowers y) hT₁ htype hR2
  obtain ⟨h2, -⟩ := h1 (zpowers_le.mpr (mem_inf.mpr ⟨hyN, hyt⟩))
  have hyy2 : orderOf (y * y) = 2 := by
    rw [← pow_two, orderOf_pow' y two_ne_zero, hy4]
    norm_num
  exact not_mem_coreActionKernel_of_involution hS hU hheld hSol hGW hMax hL34 hset hu2 htu hK₁u
    hK₁p hK₁n (mul_mem hyQ hyQ) hyy2 (h2 y (mem_zpowers y))

end CFSG.ComponentClassification.GrSLit.GrS5

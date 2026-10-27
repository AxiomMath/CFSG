module

public import CFSG.LocalAnalysis.ComponentClassification.HSFLitL34InvCore
public import CFSG.LocalAnalysis.ComponentClassification.HSFLitL34InvL34
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec5Inputs510
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34FactsUnbal
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34FactsSec5Unit

public section

namespace CFSG.ComponentClassification.HSFLit.L34Inv

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer
  CFSG.ComponentClassification.UnbalancedCorr CFSG.ComponentClassification.UnbalancedGS
  CFSG.ComponentClassification.GrSLit CFSG.ComponentClassification.GrSLit.GrS5
open CFSG.LocalAnalysis.ComponentInitial (SchreierFor)

theorem l34Lemma510InvolutionStep_of_inputs
    (hS : SchreierFor Blueprint.Catalog)
    (hU : CatalogueU.CatalogAlmostSimpleUnbalancedOutcome) (hheld : KProperRelativeB.HeldInput)
    (hSol : SolomonCommutingCoreInput) (hGW : GorensteinWalterConnectedInput)
    (hMax : MaximalTwoComponentInput) (hL34 : L34InvolutionCentralizerFact) (h59 : L34Lemma59)
    (hType : L34Lemma55TypeStep) : L34Lemma510InvolutionStep := by
  intro G _ _ L t S T hset u hu huc _ K₁ hK₁u hK₁p hK₁n hSN hO htype
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨-, hLt, hLpt⟩ := eq_of_mem_inf_centralizer hS hU hheld hSol hGW hset
  have hZS := mem_center_of_setting hS hU hheld hSol hGW hset
  have hCN := centralizer_le_normalizer_of_setting hS hU hheld hSol hGW hMax hset
  have hset' := hset
  obtain ⟨-, ⟨⟨-, -, -, -, -, hto, -, -⟩, -⟩, -, hSyl, htS, -, -⟩ := hset'
  have ht2 : t * t = 1 := by rw [← pow_two, ← hto, pow_orderOf_eq_one]
  have hu' := hu
  obtain ⟨huS₀, hu2, -⟩ := hu'
  have huS : u ∈ S := (sup_le inf_le_left (zpowers_le.mpr htS) : S ⊓ L ⊔ zpowers t ≤ S) huS₀
  have htu : t * u = u * t := (hZS u huS).symm
  have hYD : oddIn L ⊓ centralizer ({u} : Set G) ≤
      oddIn (centralizer ({t} : Set G)) ⊓ centralizer ({u} : Set G) :=
    inf_le_inf_right _ (GSLit.map_pPrimeCore_le_of_isPComponent hLt hLpt)
  have hT₁ := gsUnbalancingTriple_of_not_le hSol hto hu2 htu hK₁u hK₁p hYD hK₁n
  have hperf : ⁅K₁, K₁⁆ = K₁ := GSThmB.commutator_eq_self_of_isPComponent hK₁u hK₁p
  have htN : t ∈ normalizer (K₁ : Set G) := hSN htS
  obtain ⟨z, hz, hzt, hΩ, -, -⟩ := h59 G L t S T hset
  have hzΩ : z ∈ omegaOne (S ⊓ coreActionKernel L) := by
    rw [hΩ]; exact mem_sup_right (mem_zpowers z)
  have htzΩ : t * z ∈ omegaOne (S ⊓ coreActionKernel L) := by
    rw [hΩ]; exact mul_mem (mem_sup_left (mem_zpowers t)) (mem_sup_right (mem_zpowers z))
  have hzS : z ∈ S := (mem_inf.mp (omegaOne_le _ hzΩ)).1
  have hz1 : z ≠ 1 := by rintro rfl; simp at hz
  have htz1 : t * z ≠ 1 := fun h => hzt (by
    calc z = t⁻¹ * (t * z) := by group
      _ = t := by rw [h, mul_one, inv_eq_of_mul_eq_one_right ht2])
  have htzt : t * z ≠ t := fun h => hz1 (by
    calc z = t⁻¹ * (t * z) := by group
      _ = 1 := by rw [h, inv_mul_cancel])
  have hinner_of : (∃ z₀ ∈ ({z, t * z} : Set G), ∃ j ∈ K₁, j⁻¹ * z₀ ∈ coreActionKernel K₁) →
      ∃ z₀ ∈ omegaOne (S ⊓ coreActionKernel L), z₀ ≠ 1 ∧ z₀ ≠ t ∧
        ∃ j ∈ K₁, j⁻¹ * z₀ ∈ coreActionKernel K₁ := by
    rintro ⟨z₀, hz₀, j, hj, hjz⟩
    rcases hz₀ with rfl | rfl
    · exact ⟨z₀, hzΩ, hz1, hzt, j, hj, hjz⟩
    · exact ⟨t * z, htzΩ, htz1, htzt, j, hj, hjz⟩
  rcases htype with ⟨htL, hZodd⟩ | h5 | h7
  ·
    have hunit := L34Facts.l34UnbalancingUnitaryStep G u t K₁ hT₁ htL
    have houter : ∀ j ∈ K₁, j⁻¹ * t ∉ coreActionKernel K₁ := fun j hj h => hunit.2.2.1 (by
      have h1 : j * (j⁻¹ * t) ∈ withKernel K₁ := mul_mem (mem_sup_left hj) (mem_sup_right h)
      rwa [mul_inv_cancel_left] at h1)
    obtain ⟨P, hP, hSP, hPZ, heq, h8, hQ8⟩ := exists_sylow_l34 L34Facts.l34UnitaryCentralizerFact
      hperf htL hunit hZodd hSN hSyl hCN htS hZS
    have hSC : S ≤ centralizer ({t} : Set G) := fun s hs =>
      mem_centralizer_singleton_iff.mpr (hZS s hs)
    obtain ⟨hz2, hzc⟩ := conj_eq_or_of_mem_omegaOne hS hU hheld hSol hGW h59 hset hzΩ hz1 hzt
    have hinner := exists_inner_l34 hperf htL hZodd hunit (GrS5.IsSylowTwoIn.isPGroup hSyl) hSN hSC
      inf_le_left inf_le_right h8 hzS hz2 fun q hq => hzc q (mem_inf.mp hq).1
    refine exists_involution_of_inner hS hU hheld hSol hGW hMax hL34 h59 hType hset hu hK₁u hK₁p
      hK₁n hSN hO (fun c hc hcC => odd_orderOf_of_mem_centralizer hZodd hc hcC) houter
      (hinner_of hinner) fun z₁ hz₁ hz₁2 hz₁1 _ => ?_
    rw [heq] at hz₁
    exact exists_conj_l34 L34Facts.unitaryCenter hperf htL hunit hP (hSP htS) hPZ hQ8 hz₁ hz₁2
      hz₁1
  all_goals
    have htype2 : IsL2Type 5 (K₁ ⧸ pPrimeCore 2 K₁) ∨ IsL2Type 7 (K₁ ⧸ pPrimeCore 2 K₁) := by
      first | exact Or.inl ‹_› | exact Or.inr ‹_›
    have houter := AutL2.l2UnbalancingOuter G u t K₁ hT₁ htype2
    exact exists_involution_of_inner hS hU hheld hSol hGW hMax hL34 h59 hType hset hu hK₁u hK₁p
      hK₁n hSN hO (fun c hc hcC => odd_orderOf_l2 htype2 hc hcC) houter
      (hinner_of (exists_inner_l2 hT₁ htype2 htN (hSN hzS))) fun z₁ hz₁ hz₁2 hz₁1 hz₁t =>
        exists_conj_l2 hT₁ htype2 hperf htN ht2 (mem_inf.mp hz₁).2 hz₁2 hz₁1 hz₁t

end CFSG.ComponentClassification.HSFLit.L34Inv

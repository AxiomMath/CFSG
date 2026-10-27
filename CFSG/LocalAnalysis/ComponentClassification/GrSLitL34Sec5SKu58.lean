module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec5Lemma582
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec5SKu55
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34FactsTransfer
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec5Extremal582
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec5Lemma58
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec5Unitary582

public section

namespace CFSG.ComponentClassification.GrSLit.GrS5

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer
  CFSG.ComponentClassification.UnbalancedCorr CFSG.ComponentClassification.UnbalancedGS
open CFSG.LocalAnalysis.ComponentInitial (SchreierFor)

variable {G : Type} [Group G] [Finite G]

theorem omegaOne_eq_of_inputs_ku
    (hS : SchreierFor Blueprint.Catalog)
    (hU : CatalogueU.CatalogAlmostSimpleUnbalancedOutcome) (hheld : KProperRelativeB.HeldInput)
    (hSol : SolomonCommutingCoreInput) (hGW : GorensteinWalterConnectedInput)
    (hMax : MaximalTwoComponentInput) (hL34 : L34InvolutionCentralizerFact)
    (hKu : GrS5S.L34Sec5KuOddStep)
    (hFour : L34UnbalancingFourFact)
    (hOrb : L34Lemma58OrbitStep) (hElem : L34ElementaryCenterSylowFact)
    (hNE : L34NonelementaryCenterCommutatorFact) (hL2 : L2UnbalancingAutFact)
    (hUnit : L34UnbalancingUnitaryStep) (hUA : L34UnitaryAutFact)
    (hInvt : L34Sec5ComponentInvariantStep)
    {L : Subgroup G} {t : G} {S T : Subgroup G} (hset : L34Sec5Setting G L t S T)
    (hZ : S ⊓ coreActionKernel L ⊓ L ≠ ⊥) :
    S ⊓ coreActionKernel L = omegaOne (S ⊓ coreActionKernel L) ∧
      ∀ y ∈ S ⊓ coreActionKernel L ⊓ L, y * y = 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hE, -⟩ :=
    isElemTwo_omegaOne_of_setting_ku hS hU hheld hSol hGW hMax hL34 hKu hFour hset
  obtain ⟨-, hLt, hLpt⟩ := eq_of_mem_inf_centralizer hS hU hheld hSol hGW hset
  have hZS := mem_center_of_setting hS hU hheld hSol hGW hset
  have hset' := hset
  obtain ⟨hbase, ⟨⟨-, -, -, -, -, hto, -, -⟩, -⟩, -, hSyl, htS, -, -⟩ := hset'
  have hS2 : IsPGroup 2 S := IsSylowTwoIn.isPGroup hSyl
  have hSQ : S ≤ normalizer ((S ⊓ coreActionKernel L : Subgroup G) : Set G) := fun s hs =>
    mem_normalizer_inf (le_normalizer hs)
      (normalizer_le_normalizer_coreActionKernel L (hSyl.1 hs))
  have hQΩ : S ⊓ coreActionKernel L = omegaOne (S ⊓ coreActionKernel L) := by
    by_contra hne
    obtain ⟨y, hyQ, hy4, -, hyc⟩ :=
      exists_orderOf_four_of_ne_omegaOne hS2 inf_le_left hSQ hE hne
    obtain ⟨u, hu, ⟨w, hwΩ, hw1, hwc⟩, hsyl⟩ :=
      exists_unbalancing_commutator_sylow hS hU hheld hSol hGW hMax hElem hNE hset hZ
    obtain ⟨K₁, hK₁u, hK₁p, hK₁n, hK₁⟩ :=
      hOrb G L t S T hset u hu hsyl ⟨w, hwΩ, hw1, hwc⟩ y hyQ hy4 hyc
    obtain ⟨huS₀, hu2, -⟩ := hu
    have huS : u ∈ S :=
      (sup_le inf_le_left (zpowers_le.mpr htS) : S ⊓ L ⊔ zpowers t ≤ S) huS₀
    have htu : t * u = u * t := (hZS u huS).symm
    have hYD : oddIn L ⊓ centralizer ({u} : Set G) ≤
        oddIn (centralizer ({t} : Set G)) ⊓ centralizer ({u} : Set G) :=
      inf_le_inf_right _ (GSLit.map_pPrimeCore_le_of_isPComponent hLt hLpt)
    have hT₁ := gsUnbalancingTriple_of_not_le hSol hto hu2 htu hK₁u hK₁p hYD hK₁n
    have hL2' : IsL2Type 5 (K₁ ⧸ pPrimeCore 2 K₁) ∨ IsL2Type 7 (K₁ ⧸ pPrimeCore 2 K₁) →
        False := fun h => by
      rcases hK₁ with h' | h'
      · exact h' h
      · exact false_of_isL2Type_of_mem_normalizer hS hU hheld hSol hGW hMax hL34 hL2 hset hu2
          htu hK₁u hK₁p hK₁n h hyQ hy4 h'
    rcases hbase.2.2.2.2.2.2.2 u t K₁ hT₁ with h | h | h
    · exact hL2' (Or.inl h)
    · exact hL2' (Or.inr h)
    · exact false_of_isL34Type_component hS hU hheld hSol hGW hMax hL34 hUnit hUA hInvt hset hE
        huS₀ hu2 hwΩ hw1 hwc hyQ hy4 hK₁u hK₁p hK₁n h
  refine ⟨hQΩ, fun y hy => ?_⟩
  have h1 : y ∈ S ⊓ coreActionKernel L := (mem_inf.mp hy).1
  rw [hQΩ] at h1
  exact hE.2 y h1

theorem l34Lemma58_of_inputs_ku
    (hS : SchreierFor Blueprint.Catalog)
    (hU : CatalogueU.CatalogAlmostSimpleUnbalancedOutcome) (hheld : KProperRelativeB.HeldInput)
    (hSol : SolomonCommutingCoreInput) (hGW : GorensteinWalterConnectedInput)
    (hMax : MaximalTwoComponentInput) (hL34 : L34InvolutionCentralizerFact)
    (h56 : L34Lemma56) (hAut : L34AutRankOneNormalFact)
    (hKu : GrS5S.L34Sec5KuOddStep)
    (hFour : L34UnbalancingFourFact)
    (hOrb : L34Lemma58OrbitStep) (hElem : L34ElementaryCenterSylowFact)
    (hNE : L34NonelementaryCenterCommutatorFact) (hL2 : L2UnbalancingAutFact)
    (hUnit : L34UnbalancingUnitaryStep) (hUA : L34UnitaryAutFact)
    (hInvt : L34Sec5ComponentInvariantStep) : L34Lemma58 := by
  intro G _ _ L t S T hset
  exact ⟨eq_zpowers_of_omegaOne_eq hS hU hheld hSol hGW hMax h56 hAut hset,
    omegaOne_eq_of_inputs_ku hS hU hheld hSol hGW hMax hL34 hKu hFour hOrb hElem hNE
      hL2 hUnit hUA hInvt hset⟩

end CFSG.ComponentClassification.GrSLit.GrS5

module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec5Comp582
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec5Inputs217

public section

namespace CFSG.ComponentClassification.GrSLit.GrS5

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer
  CFSG.ComponentClassification.UnbalancedCorr CFSG.ComponentClassification.UnbalancedGS
open CFSG.LocalAnalysis.ComponentInitial (SchreierFor)

variable {G : Type} [Group G] [Finite G]

theorem false_of_isL34Type_component
    (hS : SchreierFor Blueprint.Catalog)
    (hU : CatalogueU.CatalogAlmostSimpleUnbalancedOutcome) (hheld : KProperRelativeB.HeldInput)
    (hSol : SolomonCommutingCoreInput) (hGW : GorensteinWalterConnectedInput)
    (hMax : MaximalTwoComponentInput) (hL34 : L34InvolutionCentralizerFact)
    (hUnit : L34UnbalancingUnitaryStep) (hUA : L34UnitaryAutFact)
    (hInvt : L34Sec5ComponentInvariantStep)
    {L : Subgroup G} {t : G} {S T : Subgroup G} (hset : L34Sec5Setting G L t S T)
    (hE : IsElemTwo (omegaOne (S ⊓ coreActionKernel L))) {u : G} (huS : u ∈ S ⊓ L ⊔ zpowers t)
    (hu2 : orderOf u = 2) {w : G} (hwΩ : w ∈ omegaOne (S ⊓ coreActionKernel L)) (hw1 : w ≠ 1)
    (hwc : w ∈ ⁅S ⊓ L ⊓ centralizer ({u} : Set G), S ⊓ L ⊓ centralizer ({u} : Set G)⁆) {y : G}
    (hyQ : y ∈ S ⊓ coreActionKernel L) (hy4 : orderOf y = 4) {K₁ : Subgroup G}
    (hK₁u : K₁ ≤ centralizer ({u} : Set G))
    (hK₁p : IsPComponent 2 (K₁.subgroupOf (centralizer ({u} : Set G))))
    (hK₁n : ¬ ⁅K₁, oddIn L ⊓ centralizer ({u} : Set G)⁆ ≤ oddIn K₁)
    (htype₁ : IsL34Type (K₁ ⧸ Open.fusionZStar K₁)) : False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨-, hLt, hLpt⟩ := eq_of_mem_inf_centralizer hS hU hheld hSol hGW hset
  have hZS := mem_center_of_setting hS hU hheld hSol hGW hset
  have hset' := hset
  obtain ⟨-, ⟨⟨-, -, -, -, -, hto, -, -⟩, -⟩, -, hSyl, htS, -, -⟩ := hset'
  have hS2 : IsPGroup 2 S := IsSylowTwoIn.isPGroup hSyl
  have hYD : oddIn L ⊓ centralizer ({u} : Set G) ≤
      oddIn (centralizer ({t} : Set G)) ⊓ centralizer ({u} : Set G) :=
    inf_le_inf_right _ (GSLit.map_pPrimeCore_le_of_isPComponent hLt hLpt)
  have hS₀tS : S ⊓ L ⊔ zpowers t ≤ S := sup_le inf_le_left (zpowers_le.mpr htS)
  have huS' : u ∈ S := hS₀tS huS
  have htu : t * u = u * t := (hZS u huS').symm
  have hT₁ := gsUnbalancingTriple_of_not_le hSol hto hu2 htu hK₁u hK₁p hYD hK₁n
  have hRN := hInvt G L t S T hset u huS hu2 K₁ hK₁u hK₁p hK₁n htype₁
  have hyS : y ∈ S := (mem_inf.mp hyQ).1
  have hyK : y ∈ coreActionKernel L := (mem_inf.mp hyQ).2
  have hyS₀ : ∀ s ∈ S ⊓ L, s * y = y * s := fun s hs =>
    (commute_of_mem_coreActionKernel hS2 hyS hyK (mem_inf.mp hs).1 (mem_inf.mp hs).2).symm
  have hyu : u * y = y * u := by
    have hle : S ⊓ L ⊔ zpowers t ≤ centralizer ({y} : Set G) := sup_le
      (fun s hs => mem_centralizer_singleton_iff.mpr (hyS₀ s hs))
      (zpowers_le.mpr (mem_centralizer_singleton_iff.mpr (hZS y hyS).symm))
    exact mem_centralizer_singleton_iff.mp (hle huS)
  set R := S ⊓ centralizer ({u} : Set G) with hR
  have hR2 : IsPGroup 2 R := hS2.to_le inf_le_left
  have hRle : R ≤ normalizer (K₁ : Set G) ⊓ centralizer ({t} : Set G) := fun r hr =>
    mem_inf.mpr ⟨hRN hr,
      mem_centralizer_singleton_iff.mpr (hZS r (mem_inf.mp hr).1)⟩
  obtain ⟨-, -, hab⟩ := hUA G K₁ R t (GSThmB.commutator_eq_self_of_isPComponent hK₁u hK₁p)
    htype₁ (hUnit G u t K₁ hT₁ htype₁) hR2 hRle
  have hyR : y ∈ R := mem_inf.mpr ⟨hyS, mem_centralizer_singleton_iff.mpr hyu.symm⟩
  have hyy : y * y ∉ coreActionKernel K₁ := by
    have hyy2 : orderOf (y * y) = 2 := by
      rw [← pow_two, orderOf_pow' y two_ne_zero, hy4]
      norm_num
    exact not_mem_coreActionKernel_of_involution hS hU hheld hSol hGW hMax hL34 hset hu2 htu hK₁u
      hK₁p hK₁n (mul_mem hyQ hyQ) hyy2
  have hC₀R : ∀ a ∈ S ⊓ L ⊓ centralizer ({u} : Set G), a ∈ R ∧ a * y = y * a := fun a ha =>
    ⟨mem_inf.mpr ⟨(mem_inf.mp (mem_inf.mp ha).1).1, (mem_inf.mp ha).2⟩, hyS₀ a (mem_inf.mp ha).1⟩
  have hder : ⁅S ⊓ L ⊓ centralizer ({u} : Set G), S ⊓ L ⊓ centralizer ({u} : Set G)⁆ ≤
      coreActionKernel K₁ := by
    rw [commutator_le]
    intro a ha b hb
    obtain ⟨haR, hay⟩ := hC₀R a⁻¹ (inv_mem ha)
    obtain ⟨hbR, hby⟩ := hC₀R b⁻¹ (inv_mem hb)
    have h1 := hab y hyR hyy a⁻¹ haR b⁻¹ hbR hay hby
    rw [inv_inv, inv_inv] at h1
    rwa [commutatorElement_def]
  have hwQ : w ∈ S ⊓ coreActionKernel L := omegaOne_le _ hwΩ
  have hw2 : orderOf w = 2 := orderOf_eq_prime (by rw [pow_two]; exact hE.2 w hwΩ) hw1
  exact not_mem_coreActionKernel_of_involution hS hU hheld hSol hGW hMax hL34 hset hu2 htu hK₁u
    hK₁p hK₁n hwQ hw2 (hder hwc)

end CFSG.ComponentClassification.GrSLit.GrS5

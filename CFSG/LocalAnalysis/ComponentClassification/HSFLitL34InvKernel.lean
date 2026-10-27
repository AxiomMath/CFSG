module

public import CFSG.LocalAnalysis.ComponentClassification.HSFLitL34InvInputs
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec5Lemma551

public section

namespace CFSG.ComponentClassification.HSFLit.L34Inv

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer
  CFSG.ComponentClassification.UnbalancedCorr CFSG.ComponentClassification.UnbalancedGS
  CFSG.ComponentClassification.GrSLit CFSG.ComponentClassification.GrSLit.GrS5
open CFSG.LocalAnalysis.ComponentInitial (SchreierFor)

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem mem_coreActionKernel_of_centralizes {M T : Subgroup G} (hTM : T ≤ M)
    (hTO : T ⊔ oddIn M = M) {c : G} (hcN : c ∈ normalizer (M : Set G))
    (hcT : ∀ y ∈ T, c * y = y * c) : c ∈ coreActionKernel M := by
  refine mem_coreActionKernel.mpr ⟨hcN, fun m hm => ?_⟩
  have hTN : T ≤ normalizer (oddIn M : Set G) := fun x hx =>
    normalizer_le_normalizer_oddIn M (le_normalizer (hTM hx))
  have hm' : m ∈ ((T ⊔ oddIn M : Subgroup G) : Set G) := by rw [hTO]; exact hm
  rw [coe_mul_of_left_le_normalizer_right T (oddIn M) hTN] at hm'
  obtain ⟨y, hy, o, ho, rfl⟩ := hm'
  have hON : c ∈ normalizer (oddIn M : Set G) := normalizer_le_normalizer_oddIn M hcN
  have h1 : c⁻¹ * o * c⁻¹⁻¹ ∈ oddIn M := (mem_normalizer_iff.mp (inv_mem hON) o).mp ho
  rw [inv_inv] at h1
  have hyc : y⁻¹ * c⁻¹ * y = c⁻¹ := by
    have h2 : y⁻¹ * c * y = c := by rw [mul_assoc, hcT y hy]; group
    rw [show y⁻¹ * c⁻¹ * y = (y⁻¹ * c * y)⁻¹ by group, h2]
  have e : (y * o)⁻¹ * c⁻¹ * (y * o) * c = o⁻¹ * (c⁻¹ * o * c) := by
    calc (y * o)⁻¹ * c⁻¹ * (y * o) * c = o⁻¹ * (y⁻¹ * c⁻¹ * y) * o * c := by group
      _ = o⁻¹ * (c⁻¹ * o * c) := by rw [hyc]; group
  rw [e]
  exact mul_mem (inv_mem ho) h1

theorem mem_coreActionKernel_of_conj
    (hS : SchreierFor Blueprint.Catalog)
    (hU : CatalogueU.CatalogAlmostSimpleUnbalancedOutcome) (hheld : KProperRelativeB.HeldInput)
    (hSol : SolomonCommutingCoreInput) (hGW : GorensteinWalterConnectedInput)
    (hMax : MaximalTwoComponentInput) (hL34 : L34InvolutionCentralizerFact)
    (hType : L34Lemma55TypeStep) {L : Subgroup G} {t : G} {S T : Subgroup G}
    (hset : L34Sec5Setting G L t S T) {z₀ : G} (hz₀Q : z₀ ∈ S ⊓ coreActionKernel L)
    (hz₀ : orderOf z₀ = 2) {c v : G} (hct : c * t = t * c) (hvz : v * z₀ = z₀ * v)
    (hv : v⁻¹ * t * v = t * c) : c ∈ coreActionKernel L := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨-, hLt, hLpt⟩ := eq_of_mem_inf_centralizer hS hU hheld hSol hGW hset
  have hZS := mem_center_of_setting hS hU hheld hSol hGW hset
  have hCN := centralizer_le_normalizer_of_setting hS hU hheld hSol hGW hMax hset
  have hset' := hset
  obtain ⟨hbase, ⟨⟨-, -, -, -, -, hto, -, -⟩, -⟩, -, -, -, -, -⟩ := hset'
  obtain ⟨hsimple, hnonab, hK, -, -, -, -, -⟩ := hbase
  have : IsSimpleGroup G := hsimple
  obtain ⟨hz₀S, hz₀K⟩ := mem_inf.mp hz₀Q
  have htz : t * z₀ = z₀ * t := (hZS z₀ hz₀S).symm
  have hz1 : z₀ ≠ 1 := by rintro rfl; simp at hz₀
  have hzZ : z₀ ∉ center G := not_mem_center_of_ne_one hnonab hz1
  obtain ⟨hTtz, hTpc, hTE, hTset, -, -⟩ := gsFixedLayer_facts hS hK hto hz₀ htz hzZ hLt hLpt hz₀K
  set T₀ := gsFixedLayer L z₀ with hT₀
  obtain ⟨M, hMz, hMp, hTMM, hTMpc⟩ :=
    UGSChain.exists_orbit_component_of_le_pLayer hto htz hTtz hTpc hTE
  have hTK : T₀ ≤ (M ⊔ conjugate M t) ⊓ centralizer ({t} : Set G) :=
    le_inf hTMM (hTtz.trans inf_le_left)
  have hMt : conjugate M t = M :=
    conjugate_eq_of_fixedLayer hS hU hheld hSol hGW hMax hset hz₀ htz hz₀K hMz hMp hTK hTMpc
  have hTM : T₀ ≤ M := by
    rw [hMt, sup_idem] at hTMM
    exact hTMM
  have htypeM := hType G L t S T hset z₀ hz₀Q hz₀ M hMz hMp hMt hTM
  obtain ⟨-, hTO, hMn, -, -⟩ := isPComponent_eq_of_setting hS hU hheld hSol hGW hMax hL34 hset
    hz₀Q hz₀ hMz hMp (Or.inr htypeM)
  have htM : t ∈ coreActionKernel M :=
    mem_coreActionKernel_of_centralizes hTM hTO (mem_normalizer_of_conjugate_eq hMt)
      fun y hy => (mem_centralizer_singleton_iff.mp (mem_inf.mp (hTtz hy)).1).symm
  have hvN : v⁻¹ ∈ normalizer (M : Set G) :=
    inv_mem (mem_normalizer_of_conjugate_eq (hMn v (mem_centralizer_singleton_iff.mpr hvz)))
  have htcM : t * c ∈ coreActionKernel M := by
    have h1 := conj_mem_coreActionKernel hvN htM
    rwa [inv_inv, hv] at h1
  have hcM : c ∈ coreActionKernel M := by
    have h1 := mul_mem (inv_mem htM) htcM
    rwa [inv_mul_cancel_left] at h1
  have hOM : oddIn M ≤ oddIn (centralizer ({z₀} : Set G)) :=
    GSLit.map_pPrimeCore_le_of_isPComponent hMz hMp
  have hcN : c ∈ normalizer (L : Set G) := hCN (mem_centralizer_singleton_iff.mpr hct)
  exact mem_coreActionKernel_of_fixedLayer ((gsFixedLayer_le_inf L z₀).trans inf_le_left)
    (hTtz.trans inf_le_right) hTset hcN fun y hy =>
      hOM (conj_mem_oddIn_of_mem_coreActionKernel hcM y (hTM hy))

end CFSG.ComponentClassification.HSFLit.L34Inv

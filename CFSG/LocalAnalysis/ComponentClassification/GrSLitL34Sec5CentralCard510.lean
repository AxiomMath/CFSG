module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec5ConjTools510
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec5InputsCard510

public section

namespace CFSG.ComponentClassification.GrSLit.GrS5

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer
  CFSG.ComponentClassification.UnbalancedCorr CFSG.ComponentClassification.UnbalancedGS
open CFSG.LocalAnalysis.ComponentInitial (SchreierFor)

theorem l34Lemma510CentralStep_of_card
    (hS : SchreierFor Blueprint.Catalog)
    (hU : CatalogueU.CatalogAlmostSimpleUnbalancedOutcome) (hheld : KProperRelativeB.HeldInput)
    (hSol : SolomonCommutingCoreInput) (hGW : GorensteinWalterConnectedInput)
    (hMax : MaximalTwoComponentInput) (hL34 : L34InvolutionCentralizerFact)
    (hCard : L34Lemma510CentralCardStep) : L34Lemma510CentralStep := by
  intro G _ _ L t S T hset hexp hΩ hZnc _ _ _
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hset' := hset
  obtain ⟨y, hySL, hyZ, hy2, hyc, hycard⟩ := hCard G L t S T hset hexp hΩ hZnc
  obtain ⟨-, hLt, -⟩ := eq_of_mem_inf_centralizer hS hU hheld hSol hGW hset
  have hZS := mem_center_of_setting hS hU hheld hSol hGW hset
  have h53 := l34Lemma53_of_inputs hS hU hheld hSol hGW
  obtain ⟨-, ⟨⟨-, -, -, -, -, hto, -, -⟩, htype, -⟩, -, hSyl, htS, -, -⟩ := hset'
  have ht2 : t * t = 1 := by rw [← pow_two, ← hto, pow_orderOf_eq_one]
  obtain ⟨hyS, hyL⟩ := mem_inf.mp hySL
  have hS₀ : IsSylowTwoIn (S ⊓ L) L := isSylowTwoIn_inf_of_isSubnormal hSyl le_normalizer
    (Subgroup.Normal.isSubnormal Subgroup.normal_in_normalizer)
  have hZsub : ∀ w ∈ S ⊓ L ⊓ zStarIn L, w ∈ S ⊓ coreActionKernel L ⊓ L := fun w hw =>
    mem_inf.mpr ⟨mem_inf.mpr ⟨(mem_inf.mp (mem_inf.mp hw).1).1,
      zStarIn_le_coreActionKernel L (mem_inf.mp hw).2⟩, (mem_inf.mp (mem_inf.mp hw).1).2⟩
  have hXt : ∀ i : ℤ, oddIn L ≤ centralizer ({t ^ i} : Set G) := fun i x hx =>
    mem_centralizer_singleton_iff.mpr
      (Commute.zpow_right (mem_centralizer_singleton_iff.mp (hLt (map_subtype_le _ hx))) i).eq
  have hbound : ∀ v ∈ L34UnbalancingSet L t S, Nat.card ↥(oddIn L ⊓ centralizer ({v} : Set G)) ≤
      Nat.card ↥(oddIn L ⊓ centralizer ({y} : Set G)) := by
    intro v hv
    obtain ⟨i, s, hs, rfl, hs2, hsZ⟩ :=
      exists_eq_zpow_mul_of_mem_unbalancingSet hS hU hheld hSol hGW hMax hL34 hset hv
    rw [inf_centralizer_mul_eq_of_le_centralizer (hXt i) s]
    obtain ⟨l, hl, z', hz', he⟩ := exists_conj_eq_mul_of_involution htype hS₀
      (fun w hw => hexp w (hZsub w hw)) hyL hyZ hy2
      (fun w hw => (hyc w (mem_inf.mp (mem_inf.mp hw).1).1).symm) (mem_inf.mp hs).2 hs2 hsZ
    rw [← card_inf_centralizer_conj hl s, he]
    exact hycard z' (hZsub z' hz')
  have hy1 : y ≠ 1 := fun h => hyZ (h ▸ one_mem _)
  have hyo : orderOf y = 2 := orderOf_eq_prime (by rw [pow_two, hy2]) hy1
  have hyK : y ∉ coreActionKernel L := fun hK =>
    hyZ (inf_coreActionKernel_le_zStarIn L (mem_inf.mpr ⟨hyL, hK⟩))
  obtain ⟨-, u₁, hu₁, hu₁n⟩ := h53 G L t S T hset y hyS hyo hyK (mem_sup_left hyL)
  have hyt : y * t = t * y := hZS y hyS
  rcases hu₁ with rfl | rfl
  · exact ⟨u₁, ⟨mem_sup_left hySL, hyo, hu₁n⟩, hyc, hbound⟩
  · have htK : t ∈ coreActionKernel L := mem_coreActionKernel_of_commute fun l hl =>
      (mem_centralizer_singleton_iff.mp (hLt hl) : l * t = t * l).symm
    have hyne : y ≠ t := fun h => hyK (h ▸ htK)
    have hyto : orderOf (y * t) = 2 := by
      refine orderOf_eq_prime ?_ ?_
      · calc (y * t) ^ 2 = y * (t * y) * t := by rw [pow_two]; group
          _ = y * y * (t * t) := by rw [← hyt]; group
          _ = 1 := by rw [hy2, ht2, one_mul]
      · intro h
        apply hyne
        rw [mul_eq_one_iff_eq_inv.mp h, inv_eq_of_mul_eq_one_right ht2]
    have hcard : Nat.card ↥(oddIn L ⊓ centralizer ({y * t} : Set G)) =
        Nat.card ↥(oddIn L ⊓ centralizer ({y} : Set G)) := by
      rw [hyt, show t = t ^ (1 : ℤ) from (zpow_one t).symm,
        inf_centralizer_mul_eq_of_le_centralizer (hXt 1) y]
    refine ⟨y * t, ⟨mul_mem (mem_sup_left hySL) (mem_sup_right (mem_zpowers t)), hyto, hu₁n⟩,
      fun s hs => ?_, fun v hv => hcard ▸ hbound v hv⟩
    calc s * (y * t) = (s * y) * t := by group
      _ = y * (s * t) := by rw [hyc s hs]; group
      _ = y * (t * s) := by rw [hZS s hs]
      _ = y * t * s := by group

theorem l34Lemma510CentralCardStep_of_centralStep
    (hS : SchreierFor Blueprint.Catalog)
    (hU : CatalogueU.CatalogAlmostSimpleUnbalancedOutcome) (hheld : KProperRelativeB.HeldInput)
    (hSol : SolomonCommutingCoreInput) (hGW : GorensteinWalterConnectedInput)
    (hMax : MaximalTwoComponentInput) (hL34 : L34InvolutionCentralizerFact)
    (hCen : L34Lemma510CentralStep) : L34Lemma510CentralCardStep := by
  intro G _ _ L t S T hset hexp hΩ hZnc
  have hset' := hset
  obtain ⟨-, hLt, -⟩ := eq_of_mem_inf_centralizer hS hU hheld hSol hGW hset
  have hZS := mem_center_of_setting hS hU hheld hSol hGW hset
  have h53 := l34Lemma53_of_inputs hS hU hheld hSol hGW
  obtain ⟨-, ⟨⟨-, -, -, -, -, hto, -, -⟩, -⟩, -, -, htS, -, -⟩ := hset'
  have ht2 : t * t = 1 := by rw [← pow_two, ← hto, pow_orderOf_eq_one]
  have hXt : ∀ i : ℤ, oddIn L ≤ centralizer ({t ^ i} : Set G) := fun i x hx =>
    mem_centralizer_singleton_iff.mpr
      (Commute.zpow_right (mem_centralizer_singleton_iff.mp (hLt (map_subtype_le _ hx))) i).eq
  have htK : t ∈ coreActionKernel L := mem_coreActionKernel_of_commute fun l hl =>
    (mem_centralizer_singleton_iff.mp (hLt hl) : l * t = t * l).symm
  obtain ⟨u₀, hu₀, hmax₀⟩ := Set.exists_max_image (L34UnbalancingSet L t S)
    (fun v => Nat.card ↥(oddIn L ⊓ centralizer ({v} : Set G))) (Set.toFinite _)
    (l34UnbalancingSetNonempty_of_inputs hS hU hheld hSol hGW G L t S T hset)
  obtain ⟨u', hu', hu'c, hu'max⟩ := hCen G L t S T hset hexp hΩ hZnc u₀ hu₀ hmax₀
  obtain ⟨i, y, hy, hu'eq, hy2, hyZ⟩ :=
    exists_eq_zpow_mul_of_mem_unbalancingSet hS hU hheld hSol hGW hMax hL34 hset hu'
  obtain ⟨hyS, hyL⟩ := mem_inf.mp hy
  have hu'card : Nat.card ↥(oddIn L ⊓ centralizer ({u'} : Set G)) =
      Nat.card ↥(oddIn L ⊓ centralizer ({y} : Set G)) := by
    rw [hu'eq, inf_centralizer_mul_eq_of_le_centralizer (hXt i) y]
  have hyc : ∀ s ∈ S, s * y = y * s := by
    intro s hs
    have h1 := hu'c s hs
    rw [hu'eq] at h1
    have hst : s * t ^ i = t ^ i * s := (Commute.zpow_right (hZS s hs) i).eq
    have h2 : t ^ i * (s * y) = t ^ i * (y * s) := by
      calc t ^ i * (s * y) = s * t ^ i * y := by rw [hst]; group
        _ = s * (t ^ i * y) := by group
        _ = t ^ i * y * s := h1
        _ = t ^ i * (y * s) := by group
    exact mul_left_cancel h2
  refine ⟨y, hy, hyZ, hy2, hyc, fun z' hz' => ?_⟩
  obtain ⟨⟨hz'S, hz'K⟩, hz'L⟩ := mem_inf.mp hz'
  have hz'Z : z' ∈ zStarIn L := inf_coreActionKernel_le_zStarIn L (mem_inf.mpr ⟨hz'L, hz'K⟩)
  have hz'2 : z' * z' = 1 := hexp z' hz'
  have hyz' : z' * y = y * z' := hyc z' hz'S
  set w := y * z' with hw
  have hwS : w ∈ S := mul_mem hyS hz'S
  have hwL : w ∈ L := mul_mem hyL hz'L
  have hwZ : w ∉ zStarIn L := by
    intro h
    apply hyZ
    have : y = w * z'⁻¹ := by rw [hw, mul_inv_cancel_right]
    rw [this]
    exact mul_mem h (inv_mem hz'Z)
  have hw2 : w * w = 1 := by
    calc w * w = y * (z' * y) * z' := by rw [hw]; group
      _ = y * (y * z') * z' := by rw [hyz']
      _ = (y * y) * (z' * z') := by group
      _ = 1 := by rw [hy2, hz'2, one_mul]
  have hw1 : w ≠ 1 := fun h => hwZ (h ▸ one_mem _)
  have hwo : orderOf w = 2 := orderOf_eq_prime (by rw [pow_two, hw2]) hw1
  have hwK : w ∉ coreActionKernel L := fun hK =>
    hwZ (inf_coreActionKernel_le_zStarIn L (mem_inf.mpr ⟨hwL, hK⟩))
  have hwU : w ∈ S ⊓ L ⊔ zpowers t := mem_sup_left (mem_inf.mpr ⟨hwS, hwL⟩)
  obtain ⟨-, u₁, hu₁, hu₁n⟩ := h53 G L t S T hset w hwS hwo hwK (mem_sup_left hwL)
  rcases hu₁ with rfl | rfl
  · exact (hu'max w ⟨hwU, hwo, hu₁n⟩).trans hu'card.le
  · have hwt : w * t = t * w := hZS w hwS
    have hwne : w ≠ t := fun h => hwK (h ▸ htK)
    have hwto : orderOf (w * t) = 2 := by
      refine orderOf_eq_prime ?_ ?_
      · calc (w * t) ^ 2 = w * (t * w) * t := by rw [pow_two]; group
          _ = w * w * (t * t) := by rw [← hwt]; group
          _ = 1 := by rw [hw2, ht2, one_mul]
      · intro h
        apply hwne
        rw [mul_eq_one_iff_eq_inv.mp h, inv_eq_of_mul_eq_one_right ht2]
    have hcard : Nat.card ↥(oddIn L ⊓ centralizer ({w * t} : Set G)) =
        Nat.card ↥(oddIn L ⊓ centralizer ({w} : Set G)) := by
      rw [hwt, show t = t ^ (1 : ℤ) from (zpow_one t).symm,
        inf_centralizer_mul_eq_of_le_centralizer (hXt 1) w]
    have hle := hu'max (w * t)
      ⟨mul_mem hwU (mem_sup_right (mem_zpowers t)), hwto, hu₁n⟩
    rw [hcard] at hle
    exact hle.trans hu'card.le

end CFSG.ComponentClassification.GrSLit.GrS5

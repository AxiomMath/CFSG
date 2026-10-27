module

public import CFSG.LocalAnalysis.ComponentClassification.HSFLitL34PairIndex
public import CFSG.LocalAnalysis.ComponentClassification.HSFLitL34UniqComp

public section

namespace CFSG.ComponentClassification.HSFLit.L34Uniq

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer
  CFSG.ComponentClassification.UnbalancedCorr CFSG.ComponentClassification.UnbalancedGS
  CFSG.ComponentClassification.GrSLit CFSG.ComponentClassification.GrSLit.GrS5
open CFSG.LocalAnalysis.ComponentInitial (SchreierFor)

variable {G : Type} [Group G] [Finite G]

theorem parity_of_component
    (hS : SchreierFor Blueprint.Catalog)
    (hU : CatalogueU.CatalogAlmostSimpleUnbalancedOutcome) (hheld : KProperRelativeB.HeldInput)
    (hSol : SolomonCommutingCoreInput) (hGW : GorensteinWalterConnectedInput)
    (hMax : MaximalTwoComponentInput) (hL34 : L34InvolutionCentralizerFact) {L : Subgroup G}
    {t : G} {S T : Subgroup G} (hset : L34Sec5Setting G L t S T) {u : G}
    (hu : u ∈ L34UnbalancingSet L t S) {K : Subgroup G} (hKu : K ≤ centralizer ({u} : Set G))
    (hKp : IsPComponent 2 (K.subgroupOf (centralizer ({u} : Set G))))
    (hKn : ¬ ⁅K, oddIn L ⊓ centralizer ({u} : Set G)⁆ ≤ oddIn K)
    (htype : IsL2Type 5 (K ⧸ pPrimeCore 2 K) ∨ IsL2Type 7 (K ⧸ pPrimeCore 2 K)) :
    (∀ x ∈ S ⊓ normalizer (K : Set G), ∀ y ∈ S ⊓ normalizer (K : Set G),
      (x * y ∈ coreActionKernel K ∨ x * y * t ∈ coreActionKernel K) ↔
        ((x ∈ coreActionKernel K ∨ x * t ∈ coreActionKernel K) ↔
          (y ∈ coreActionKernel K ∨ y * t ∈ coreActionKernel K))) ∧
    (∀ q ∈ S ⊓ coreActionKernel L,
      (q ∈ coreActionKernel K ∨ q * t ∈ coreActionKernel K) ↔ (q = 1 ∨ q = t)) ∧
    ∀ e ∈ S ⊓ K, orderOf e = 2 → ¬ (e ∈ coreActionKernel K ∨ e * t ∈ coreActionKernel K) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hset' := hset
  obtain ⟨-, ⟨⟨-, -, -, -, -, hto, -, -⟩, -⟩, -, hSyl, htS, -, -⟩ := hset'
  have hS2 : IsPGroup 2 S := GrS5.IsSylowTwoIn.isPGroup hSyl
  obtain ⟨-, hLt, hLpt⟩ := eq_of_mem_inf_centralizer hS hU hheld hSol hGW hset
  have hZS := mem_center_of_setting hS hU hheld hSol hGW hset
  have ht2 : t * t = 1 := by rw [← pow_two, ← hto, pow_orderOf_eq_one]
  have hu' := hu
  obtain ⟨huS₀, hu2, -⟩ := hu'
  have huS : u ∈ S := (sup_le inf_le_left (zpowers_le.mpr htS) : S ⊓ L ⊔ zpowers t ≤ S) huS₀
  have htu : t * u = u * t := (hZS u huS).symm
  have hYD : oddIn L ⊓ centralizer ({u} : Set G) ≤
      oddIn (centralizer ({t} : Set G)) ⊓ centralizer ({u} : Set G) :=
    inf_le_inf_right _ (GSLit.map_pPrimeCore_le_of_isPComponent hLt hLpt)
  have hT := gsUnbalancingTriple_of_not_le hSol hto hu2 htu hKu hKp hYD hKn
  have htC : t ∉ coreActionKernel K := by
    simpa using AutL2.l2UnbalancingOuter G u t K hT htype 1 (one_mem _)
  have htN : t ∈ normalizer (K : Set G) := (((solomon_involutions hSol hto hu2 htu).2 K hKu
    hKp).2 fun h => hKn ((commutator_mono le_rfl hYD).trans h)).1
  have htN' : t ∈ S ⊓ normalizer (K : Set G) := mem_inf.mpr ⟨htS, htN⟩
  have htc : ∀ n ∈ S ⊓ normalizer (K : Set G), n * t = t * n := fun n hn =>
    hZS n (mem_inf.mp hn).1
  have hle : S ⊓ normalizer (K : Set G) ≤ normalizer (K : Set G) ⊓ centralizer ({t} : Set G) :=
    fun n hn => mem_inf.mpr ⟨(mem_inf.mp hn).2, mem_centralizer_singleton_iff.mpr (htc n hn)⟩
  obtain ⟨-, h4⟩ := (AutL2.l2UnbalancingAutFact G u t K _ hT htype (hS2.to_le inf_le_left)).1 hle
  have htCL : t ∈ centralizer (L : Set G) := mem_centralizer_iff.mpr fun h hh =>
    mem_centralizer_singleton_iff.mp (hLt hh)
  have htL : t ∈ coreActionKernel L := by
    refine mem_coreActionKernel.mpr ⟨centralizer_le_normalizer _ htCL, fun j hj => ?_⟩
    have hjt : j * t = t * j := mem_centralizer_singleton_iff.mp (hLt hj)
    rw [show j⁻¹ * t⁻¹ * j * t = 1 by
      calc j⁻¹ * t⁻¹ * j * t = j⁻¹ * t⁻¹ * (j * t) := by group
        _ = j⁻¹ * t⁻¹ * (t * j) := by rw [hjt]
        _ = 1 := by group]
    exact one_mem _
  have hQK := inf_coreActionKernel_eq_bot hS hU hheld hSol hGW hMax hL34 hset hu hKu hKp hKn
    htype
  refine ⟨fun x hx y hy => twoClass_mul htN' ht2 htc htC h4 hx hy, fun q hq => ?_,
    fun e he heo => ?_⟩
  · have hbot : ∀ x ∈ S ⊓ coreActionKernel L, x ∈ coreActionKernel K → x = 1 := by
      intro x hx hxK
      have h1 : x ∈ S ⊓ coreActionKernel L ⊓ coreActionKernel K := mem_inf.mpr ⟨hx, hxK⟩
      rw [hQK] at h1
      exact h1
    constructor
    · rintro (h | h)
      · exact Or.inl (hbot q hq h)
      · right
        have h1 := hbot _ (mul_mem hq (mem_inf.mpr ⟨htS, htL⟩)) h
        calc q = q * t * t := by rw [mul_assoc, ht2, mul_one]
          _ = t := by rw [h1, one_mul]
    · rintro (h | h) <;> rw [h]
      · exact Or.inl (one_mem _)
      · exact Or.inr (by rw [ht2]; exact one_mem _)
  · have he2 : e * e = 1 := by rw [← pow_two, ← heo, pow_orderOf_eq_one]
    rintro (h | h)
    · have h1 := odd_orderOf_inner_l2 htype (mem_inf.mp he).2 h
      rw [heo] at h1
      exact absurd h1 (by decide)
    · apply AutL2.l2UnbalancingOuter G u t K hT htype e (mem_inf.mp he).2
      rw [inv_eq_of_mul_eq_one_right he2]
      exact h

theorem not_mem_coreActionKernel_of_unbalancing
    (hS : SchreierFor Blueprint.Catalog)
    (hU : CatalogueU.CatalogAlmostSimpleUnbalancedOutcome) (hheld : KProperRelativeB.HeldInput)
    (hSol : SolomonCommutingCoreInput) (hGW : GorensteinWalterConnectedInput)
    (hMax : MaximalTwoComponentInput) (hL34 : L34InvolutionCentralizerFact) {L : Subgroup G}
    {t : G} {S T : Subgroup G} (hset : L34Sec5Setting G L t S T) {u : G}
    (hu : u ∈ L34UnbalancingSet L t S) :
    u ∉ coreActionKernel L := by
  intro huQ
  obtain ⟨-, hLt, hLpt⟩ := eq_of_mem_inf_centralizer hS hU hheld hSol hGW hset
  have hset' := hset
  obtain ⟨-, -, -, -, htS, -, -⟩ := hset'
  obtain ⟨huS₀, hu2, hun⟩ := hu
  have huS : u ∈ S := (sup_le inf_le_left (zpowers_le.mpr htS) : S ⊓ L ⊔ zpowers t ≤ S) huS₀
  by_cases hut : u = t
  · subst hut
    exact hun (inf_le_left.trans (GSLit.map_pPrimeCore_le_of_isPComponent hLt hLpt))
  · have hinv := conj_eq_inv_of_setting hS hU hheld hSol hGW hMax hL34 hset
      (mem_inf.mpr ⟨huS, huQ⟩) hu2 hut
    apply hun
    intro y hy
    obtain ⟨hyX, hyC⟩ := mem_inf.mp hy
    have h1 : u * y * u⁻¹ = y := by
      rw [← mem_centralizer_singleton_iff.mp hyC, mul_inv_cancel_right]
    have h2 : y = y⁻¹ := h1.symm.trans (hinv y hyX)
    have hodd : Odd (orderOf y) := by
      have h3 : Odd (Nat.card (oddIn L)) := by
        rw [oddIn, card_map_of_injective (subtype_injective _)]
        exact Nat.coprime_two_left.mp pPrimeCore_coprime_card
      exact Odd.of_dvd_nat h3 (Subgroup.orderOf_dvd_natCard _ hyX)
    have hy1 : y = 1 := by
      have h4 : y * y = 1 := by
        calc y * y = y * y⁻¹ := by rw [← h2]
          _ = 1 := mul_inv_cancel y
      have h5 : orderOf y ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact h4)
      rcases (Nat.dvd_prime Nat.prime_two).mp h5 with h6 | h6
      · exact orderOf_eq_one_iff.mp h6
      · rw [h6] at hodd
        exact absurd hodd (by decide)
    rw [hy1]
    exact one_mem _

theorem exists_mul_center_of_unbalancing
    (hS : SchreierFor Blueprint.Catalog)
    (hU : CatalogueU.CatalogAlmostSimpleUnbalancedOutcome) (hheld : KProperRelativeB.HeldInput)
    (hSol : SolomonCommutingCoreInput) (hGW : GorensteinWalterConnectedInput)
    (hMax : MaximalTwoComponentInput) (hL34 : L34InvolutionCentralizerFact) {L : Subgroup G}
    {t : G} {S T : Subgroup G} (hset : L34Sec5Setting G L t S T) {u : G}
    (hu : u ∈ L34UnbalancingSet L t S) (huc : ∀ s ∈ S, s * u = u * s) :
    ∃ (i : ℤ) (a : G), u = t ^ i * a ∧ t ^ i ∈ S ⊓ coreActionKernel L ∧
      a ∈ S ⊓ L ⊓ centralizer ((S ⊓ L : Subgroup G) : Set G) ∧ a * a = 1 ∧
      a ∉ coreActionKernel L := by
  have hset' := hset
  obtain ⟨-, ⟨⟨-, -, -, -, -, hto, -, -⟩, -⟩, -, -, htS, -, -⟩ := hset'
  obtain ⟨-, hLt, -⟩ := eq_of_mem_inf_centralizer hS hU hheld hSol hGW hset
  have hZS := mem_center_of_setting hS hU hheld hSol hGW hset
  have ht2 : t * t = 1 := by rw [← pow_two, ← hto, pow_orderOf_eq_one]
  have hu' := hu
  obtain ⟨huS₀, hu2, -⟩ := hu'
  have hu2' : u * u = 1 := by rw [← pow_two, ← hu2, pow_orderOf_eq_one]
  have huS : u ∈ S := (sup_le inf_le_left (zpowers_le.mpr htS) : S ⊓ L ⊔ zpowers t ≤ S) huS₀
  have huQ := not_mem_coreActionKernel_of_unbalancing hS hU hheld hSol hGW hMax hL34 hset hu
  have htCL : t ∈ centralizer (L : Set G) := mem_centralizer_iff.mpr fun h hh =>
    mem_centralizer_singleton_iff.mp (hLt hh)
  have htL : t ∈ coreActionKernel L := by
    refine mem_coreActionKernel.mpr ⟨centralizer_le_normalizer _ htCL, fun j hj => ?_⟩
    have hjt : j * t = t * j := mem_centralizer_singleton_iff.mp (hLt hj)
    rw [show j⁻¹ * t⁻¹ * j * t = 1 by
      calc j⁻¹ * t⁻¹ * j * t = j⁻¹ * t⁻¹ * (j * t) := by group
        _ = j⁻¹ * t⁻¹ * (t * j) := by rw [hjt]
        _ = 1 := by group]
    exact one_mem _
  rw [sup_comm] at huS₀
  obtain ⟨i, a, haSL, hua⟩ := mem_zpowers_sup (fun y hy => (hZS y (mem_inf.mp hy).1).symm) huS₀
  have hti : t ^ i = 1 ∨ t ^ i = t := by
    obtain ⟨k, rfl | rfl⟩ := Int.even_or_odd' i
    · left
      rw [zpow_mul, zpow_two, ht2, one_zpow]
    · right
      rw [zpow_add, zpow_mul, zpow_two, ht2, one_zpow, one_mul, zpow_one]
  have htiS : t ^ i ∈ S := zpow_mem htS i
  have htiL : t ^ i ∈ coreActionKernel L := zpow_mem htL i
  have haS : a ∈ S := (mem_inf.mp haSL).1
  have hac : ∀ y ∈ S, y * a = a * y := by
    intro y hy
    have h1 := huc y hy
    rw [hua] at h1
    have h2 : y * t ^ i = t ^ i * y := by
      rcases hti with h | h <;> rw [h]
      · rw [one_mul, mul_one]
      · exact hZS y hy
    have h3 : t ^ i * (y * a) = t ^ i * (a * y) := by
      calc t ^ i * (y * a) = y * (t ^ i * a) := by rw [← mul_assoc, ← h2, mul_assoc]
        _ = t ^ i * a * y := h1
        _ = t ^ i * (a * y) := mul_assoc _ _ _
    exact mul_left_cancel h3
  have ha : a ∈ S ⊓ L ⊓ centralizer ((S ⊓ L : Subgroup G) : Set G) :=
    mem_inf.mpr ⟨haSL, mem_centralizer_iff.mpr fun y hy => hac y (mem_inf.mp hy).1⟩
  have ha2 : a * a = 1 := by
    rw [hua] at hu2'
    rcases hti with h | h <;> rw [h] at hu2'
    · simpa using hu2'
    · have h1 : t * a * (t * a) = t * t * (a * a) := by
        calc t * a * (t * a) = t * (a * t) * a := by group
          _ = t * (t * a) * a := by rw [hZS a haS]
          _ = t * t * (a * a) := by group
      rw [h1, ht2, one_mul] at hu2'
      exact hu2'
  have haQ : a ∉ coreActionKernel L := fun h => huQ (hua ▸ mul_mem htiL h)
  exact ⟨i, a, hua, mem_inf.mpr ⟨htiS, htiL⟩, ha, ha2, haQ⟩

omit [Finite G] in
theorem decomp_four_involutions {e₁ e₂ e₃ e₄ x : G} (h1 : e₁ * e₁ = 1) (h2 : e₂ * e₂ = 1)
    (h3 : e₃ * e₃ = 1) (h4 : e₄ * e₄ = 1) (h12 : e₁ * e₂ = e₂ * e₁) (h13 : e₁ * e₃ = e₃ * e₁)
    (h14 : e₁ * e₄ = e₄ * e₁) (h23 : e₂ * e₃ = e₃ * e₂) (h24 : e₂ * e₄ = e₄ * e₂)
    (h34 : e₃ * e₄ = e₄ * e₃) (hx : x ∈ zpowers e₁ ⊔ (zpowers e₂ ⊔ (zpowers e₃ ⊔ zpowers e₄))) :
    ∃ ε₁ ε₂ ε₃ ε₄ : G, (ε₁ = 1 ∨ ε₁ = e₁) ∧ (ε₂ = 1 ∨ ε₂ = e₂) ∧ (ε₃ = 1 ∨ ε₃ = e₃) ∧
      (ε₄ = 1 ∨ ε₄ = e₄) ∧ x = ε₁ * (ε₂ * (ε₃ * ε₄)) := by
  have hz : ∀ {e : G}, e * e = 1 → ∀ i : ℤ, e ^ i = 1 ∨ e ^ i = e := by
    intro e he i
    obtain ⟨k, rfl | rfl⟩ := Int.even_or_odd' i
    · left
      rw [zpow_mul, zpow_two, he, one_zpow]
    · right
      rw [zpow_add, zpow_mul, zpow_two, he, one_zpow, one_mul, zpow_one]
  have hc : ∀ {a : G} {H : Subgroup G}, H ≤ centralizer ({a} : Set G) → ∀ y ∈ H,
      a * y = y * a := fun hH y hy => (mem_centralizer_singleton_iff.mp (hH hy)).symm
  have hcz : ∀ {a b : G}, a * b = b * a → zpowers b ≤ centralizer ({a} : Set G) := fun h =>
    zpowers_le.mpr (mem_centralizer_singleton_iff.mpr h.symm)
  obtain ⟨i, w, hw, rfl⟩ := mem_zpowers_sup (hc (sup_le (hcz h12) (sup_le (hcz h13) (hcz h14))))
    hx
  obtain ⟨j, w', hw', rfl⟩ := mem_zpowers_sup (hc (sup_le (hcz h23) (hcz h24))) hw
  obtain ⟨k, w'', hw'', rfl⟩ := mem_zpowers_sup (hc (hcz h34)) hw'
  obtain ⟨l, rfl⟩ := mem_zpowers_iff.mp hw''
  exact ⟨e₁ ^ i, e₂ ^ j, e₃ ^ k, e₄ ^ l, hz h1 i, hz h2 j, hz h3 k, hz h4 l, rfl⟩

omit [Finite G] in
theorem exists_of_three_avoiding {α : Type*} {x₁ x₂ x₃ : α} (h12 : x₁ ≠ x₂) (h13 : x₁ ≠ x₃)
    (h23 : x₂ ≠ x₃) (a b : α) : (x₁ ≠ a ∧ x₁ ≠ b) ∨ (x₂ ≠ a ∧ x₂ ≠ b) ∨ (x₃ ≠ a ∧ x₃ ≠ b) := by
  by_cases h1a : x₁ = a
  · subst h1a
    by_cases h2b : x₂ = b
    · subst h2b
      exact Or.inr (Or.inr ⟨h13.symm, h23.symm⟩)
    · exact Or.inr (Or.inl ⟨h12.symm, h2b⟩)
  · by_cases h1b : x₁ = b
    · subst h1b
      by_cases h2a : x₂ = a
      · subst h2a
        exact Or.inr (Or.inr ⟨h23.symm, h13.symm⟩)
      · exact Or.inr (Or.inl ⟨h2a, h12.symm⟩)
    · exact Or.inl ⟨h1a, h1b⟩

end CFSG.ComponentClassification.HSFLit.L34Uniq

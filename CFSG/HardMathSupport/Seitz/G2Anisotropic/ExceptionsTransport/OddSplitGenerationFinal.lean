module

public import CFSG.HardMathSupport.Seitz.G2Anisotropic.ExceptionsTransport.OddSplitGeneration

set_option linter.unusedSectionVars false

public noncomputable section

namespace CFSG.HardMathSupport.Seitz.G2Anisotropic.ExceptionsTransport

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
  RootOps
open scoped commutatorElement

section Final

variable
  {K : Type} [Field K]

theorem sARA_a : (sA * sR * sA) • gA = -gC := by
  rw [mul_smul, mul_smul, simple_smul, simple_smul, simple_smul]
  exact List.ofFn_injective (by decide +kernel)

theorem sARA_c : (sA * sR * sA) • gC = -gA := by
  rw [mul_smul, mul_smul, simple_smul, simple_smul, simple_smul]
  exact List.ofFn_injective (by decide +kernel)

theorem Xna_mem_of (H : Subgroup (ModGL .G2 K))
    (hCm : ∀ t : K, pinnedX .G2 K (-gC) t ∈ H) (hB : ∀ t : K, pinnedX .G2 K gB t ∈ H) (t : K) :
    pinnedX .G2 K (-gA) t ∈ H := by
  obtain ⟨εf, hε, h⟩ := commutatorElement_pinnedX_signed (τ := .G2)
    (r := (7, 10, 12, [(1, 1, 11, 1)])) (by decide) (sA * sR * sA)
  have key : ∀ y : K, pinnedX .G2 K (-gA) (((εf (1, 1, 11, 1) : ℤ) : K) * y) ∈ H := by
    intro y
    have := @h K _ (-gC) gB (by rw [pos7]; exact sARA_a) (by rw [pos10]; exact sARA_b) 1 y
    simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one, pos11,
      sARA_c, pow_one] at this
    have hm : ⁅pinnedX .G2 K (-gC) 1, pinnedX .G2 K gB y⁆ ∈ H := by
      rw [commutatorElement_def]
      exact H.mul_mem (H.mul_mem (H.mul_mem (hCm 1) (hB y)) (H.inv_mem (hCm 1))) (H.inv_mem (hB y))
    rw [this] at hm
    simpa using hm
  rcases hε (1, 1, 11, 1) with he | he
  · simpa [he] using key t
  · have := key (-t)
    simpa [he] using this

theorem gA_eq : gA = Pi.single iA 1 := by funext j; fin_cases j <;> rfl

theorem xUnit_iA (c : K) : xUnit .G2 K iA c = pinnedX .G2 K gA c := by
  rw [gA_eq, pinnedX_single]

theorem yUnit_iA (c : K) : yUnit .G2 K iA c = pinnedX .G2 K (-gA) c := by
  rw [gA_eq, pinnedX_neg_single]

theorem yUnit_iR (c : K) : yUnit .G2 K iR c = pinnedX .G2 K (-gR) c := by
  rw [gR_eq, pinnedX_neg_single]

theorem adjointGroup_le_of_centralizer (H : Subgroup (ModGL .G2 K))
    (hX : ∀ t : K, xUnit .G2 K iR t ∈ H) (hY : ∀ t : K, yUnit .G2 K iR t ∈ H)
    (hC : ∀ t : K, pinnedX .G2 K gC t ∈ H) (hCm : ∀ t : K, pinnedX .G2 K (-gC) t ∈ H)
    (hcent : ∀ g ∈ Qg K, zr K * g * (zr K)⁻¹ = g → g ∈ H)
    (ht : ∃ t₀ : K, t₀ ≠ 0 ∧ t₀ ≠ 1) (h3 : (3 : K) ≠ 0) : adjointGroup .G2 K ≤ H := by
  have hXr : ∀ t : K, pinnedX .G2 K gR t ∈ H := fun t => by rw [← xUnit_iR]; exact hX t
  have hB : ∀ t : K, pinnedX .G2 K gB t ∈ H := fun t => by
    by_cases h2 : (2 : K) = 0
    · obtain ⟨t₀, h0, h1⟩ := ht
      have hc : 3 * t₀ * (t₀ - 1) ≠ 0 := mul_ne_zero (mul_ne_zero h3 h0) (sub_ne_zero.2 h1)
      have := Xb_mem_of_two H hXr hC hcent h2 h3 t₀ (t / (3 * t₀ * (t₀ - 1)))
      rwa [mul_div_cancel₀ _ hc] at this
    · have h6 : (6 : K) ≠ 0 := by
        have : (6 : K) = 2 * 3 := by norm_num
        rw [this]; exact mul_ne_zero h2 h3
      have := Xb_mem_of H hXr hC hcent h3 (t / 6)
      rwa [mul_div_cancel₀ _ h6] at this
  have hn : weylElt .G2 K iR 1 ∈ H := by
    rw [weylElt_one_eq]
    exact H.mul_mem (H.mul_mem (hX 1) (hY (-1))) (hX 1)
  have hA : ∀ t : K, pinnedX .G2 K gA t ∈ H := fun t => by
    have := H.mul_mem (H.mul_mem hn (hB (-t))) (H.inv_mem hn)
    rwa [nR_b, neg_neg] at this
  have hNA := Xna_mem_of H hCm hB
  refine (Subgroup.closure_le _).2 ?_
  rintro g ⟨i, c, hg⟩
  fin_cases i
  · rcases hg with hg | hg
    · have : g = xUnit .G2 K iA c := Units.ext hg
      rw [this, xUnit_iA]; exact hA c
    · have : g = yUnit .G2 K iA c := Units.ext hg
      rw [this, yUnit_iA]; exact hNA c
  · rcases hg with hg | hg
    · have : g = xUnit .G2 K iR c := Units.ext hg
      rw [this]; exact hX c
    · have : g = yUnit .G2 K iR c := Units.ext hg
      rw [this]; exact hY c

end Final

end CFSG.HardMathSupport.Seitz.G2Anisotropic.ExceptionsTransport

module

public import CFSG.HardMathSupport.Seitz.G2Anisotropic.ExceptionsTransport.G2VecAction

public section

namespace CFSG.LocalAnalysis.AGL81TheoremCD.Section7.G2Max

open CFSG.HardMathSupport.Seitz.G2Anisotropic.ExceptionsTransport

variable {K : Type} [Field K]

private theorem sq_add_mul_add_sq_ne_zero (hK : ∀ s : K, s ^ 2 + s + 1 ≠ 0) {x y : K}
    (h : x ≠ 0 ∨ y ≠ 0) : x ^ 2 + x * y + y ^ 2 ≠ 0 := by
  by_cases hy : y = 0
  · subst hy
    have hx : x ≠ 0 := h.resolve_right (not_not.2 rfl)
    simpa using hx
  · intro h0
    apply hK (x / y)
    have e : (x / y) ^ 2 + x / y + 1 = (x ^ 2 + x * y + y ^ 2) / y ^ 2 := by
      field_simp
    rw [e, h0, zero_div]

private theorem kernel_mem_of_mem (hK : ∀ s : K, s ^ 2 + s + 1 ≠ 0) {W : Set (K × K × K × K)}
    (hadd : ∀ d ∈ W, ∀ d' ∈ W, d + d' ∈ W) (hsmul : ∀ (k : K) (d), d ∈ W → k • d ∈ W)
    (hA : ∀ d ∈ W, Nmat (Xmat 1 d) ∈ W) {α β : K} (hαβ : β - α ≠ 0 ∨ β ≠ 0)
    (hw : ((α, β, β, α - 3 * β) : K × K × K × K) ∈ W) (k₁ k₂ : K) :
    ((k₁, k₂, k₂, k₁ - 3 * k₂) : K × K × K × K) ∈ W := by
  obtain ⟨Q, hQdef⟩ : ∃ Q : K, Q = (β - α) ^ 2 + (β - α) * β + β ^ 2 := ⟨_, rfl⟩
  have hQ : Q ≠ 0 := hQdef ▸ sq_add_mul_add_sq_ne_zero hK hαβ
  have := hadd _ (hsmul ((k₂ * (-2 * α + 3 * β) - k₁ * (β - α)) / Q) _ hw) _
    (hsmul ((β * k₁ - α * k₂) / Q) _ (hA _ hw))
  convert this using 1
  simp only [Xmat, Nmat, Prod.smul_mk, Prod.mk_add_mk, smul_eq_mul, Prod.mk.injEq]
  refine ⟨?_, ?_, ?_, ?_⟩ <;> (field_simp; rw [hQdef]; ring)

theorem forall_mem_of_ne_fixedA (hK : ∀ s : K, s ^ 2 + s + 1 ≠ 0) {W : Set (K × K × K × K)}
    (hadd : ∀ d ∈ W, ∀ d' ∈ W, d + d' ∈ W) (hsmul : ∀ (k : K) (d), d ∈ W → k • d ∈ W)
    (hA : ∀ d ∈ W, Nmat (Xmat 1 d) ∈ W) (hC : ∀ d, Nmat (Xmat 1 d) = d → d ∈ W)
    {w : K × K × K × K} (hw : w ∈ W) (hwA : Nmat (Xmat 1 w) ≠ w) (d : K × K × K × K) :
    d ∈ W := by
  have h3 : (3 : K) ≠ 0 := by
    have h := hK 1
    rwa [show (1 : K) ^ 2 + 1 + 1 = 3 by norm_num] at h
  have hfix : ∀ d : K × K × K × K, ((3 * d.2.1 - 3 * d.2.2.1, -d.1 + 3 * d.2.1 + d.2.2.2,
      -d.1 + 3 * d.2.2.1 + d.2.2.2, 3 * d.2.1 - 3 * d.2.2.1) : K × K × K × K) ∈ W := by
    intro d
    refine hC _ ?_
    simp only [Xmat, Nmat, Prod.mk.injEq]
    refine ⟨?_, ?_, ?_, ?_⟩ <;> first | ring | trivial
  obtain ⟨w₁, w₂, w₃, w₄⟩ := w
  have hw' : ((3 * w₁ - 3 * w₂ + 3 * w₃, w₁ - w₄, w₁ - w₄,
      3 * w₁ - 3 * w₂ + 3 * w₃ - 3 * (w₁ - w₄)) : K × K × K × K) ∈ W := by
    have := hadd _ (hsmul 3 _ hw) _ (hsmul (-1) _ (hfix (w₁, w₂, w₃, w₄)))
    convert this using 1
    simp only [Prod.smul_mk, Prod.mk_add_mk, smul_eq_mul, Prod.mk.injEq]
    refine ⟨?_, ?_, ?_, ?_⟩ <;> ring
  have hne : w₁ - w₄ - (3 * w₁ - 3 * w₂ + 3 * w₃) ≠ 0 ∨ w₁ - w₄ ≠ 0 := by
    by_contra h
    push Not at h
    obtain ⟨h1, h2⟩ := h
    apply hwA
    have h14 : w₄ = w₁ := by linear_combination -h2
    have h123 : w₂ = w₁ + w₃ := mul_left_cancel₀ h3 (by linear_combination h1 - h2)
    subst h14 h123
    simp only [Xmat, Nmat, Prod.mk.injEq]
    refine ⟨?_, ?_, ?_, ?_⟩ <;> first | ring | trivial
  have hker := kernel_mem_of_mem hK hadd hsmul hA hne hw'
  have h3d : (3 : K) • d ∈ W := by
    have := hadd _ (hfix d) _ (hker (3 * d.1 - 3 * d.2.1 + 3 * d.2.2.1) (d.1 - d.2.2.2))
    convert this using 1
    obtain ⟨d₁, d₂, d₃, d₄⟩ := d
    simp only [Prod.smul_mk, Prod.mk_add_mk, smul_eq_mul, Prod.mk.injEq]
    refine ⟨?_, ?_, ?_, ?_⟩ <;> ring
  have := hsmul (3 : K)⁻¹ _ h3d
  rwa [smul_smul, inv_mul_cancel₀ h3, one_smul] at this

theorem forall_mem_of_ne_fixedD (h3 : (3 : K) ≠ 0) {ω : K} (hω : ω ^ 2 + ω + 1 = 0)
    {W : Set (K × K × K × K)}
    (hadd : ∀ d ∈ W, ∀ d' ∈ W, d + d' ∈ W) (hsmul : ∀ (k : K) (d), d ∈ W → k • d ∈ W)
    (hD : ∀ d ∈ W, (d.1, ω ^ 2 * d.2.1, ω * d.2.2.1, d.2.2.2) ∈ W)
    (hN : ∀ d ∈ W, Nmat d ∈ W) (ha : ((1, 0, 0, 0) : K × K × K × K) ∈ W)
    {w : K × K × K × K} (hw : w ∈ W) (hw0 : w.2.1 ≠ 0 ∨ w.2.2.1 ≠ 0) (d : K × K × K × K) :
    d ∈ W := by
  have hω3 : ω ^ 3 = 1 := by linear_combination (ω - 1) * hω
  obtain ⟨w₁, w₂, w₃, w₄⟩ := w
  have hD' := hD _ hw
  have hD2 := hD _ hD'
  dsimp only at hw0 hD' hD2
  have hp2 : ((0, 3 * w₂, 0, 0) : K × K × K × K) ∈ W := by
    have := hadd _ (hadd _ hw _ (hsmul ω _ hD')) _ (hsmul (ω ^ 2) _ hD2)
    convert this using 1
    simp only [Prod.smul_mk, Prod.mk_add_mk, smul_eq_mul, Prod.mk.injEq]
    refine ⟨?_, ?_, ?_, ?_⟩
    · linear_combination (-w₁) * hω
    · linear_combination (-w₂ * (2 + ω ^ 3)) * hω3
    · linear_combination (-w₃) * hω + (-w₃ * ω) * hω3
    · linear_combination (-w₄) * hω
  have hp3 : ((0, 0, 3 * w₃, 0) : K × K × K × K) ∈ W := by
    have := hadd _ (hadd _ hw _ (hsmul (ω ^ 2) _ hD')) _ (hsmul ω _ hD2)
    convert this using 1
    simp only [Prod.smul_mk, Prod.mk_add_mk, smul_eq_mul, Prod.mk.injEq]
    refine ⟨?_, ?_, ?_, ?_⟩
    · linear_combination (-w₁) * hω
    · linear_combination (-w₂) * hω + (-w₂ * (ω + ω ^ 2)) * hω3
    · linear_combination (-2 * w₃) * hω3
    · linear_combination (-w₄) * hω
  obtain ⟨e2, e3⟩ : ((0, 1, 0, 0) : K × K × K × K) ∈ W ∧ ((0, 0, 1, 0) : K × K × K × K) ∈ W := by
    rcases hw0 with h2 | h3'
    · have e2 : ((0, 1, 0, 0) : K × K × K × K) ∈ W := by
        convert hsmul (3 * w₂)⁻¹ _ hp2 using 1
        simp only [Prod.smul_mk, smul_eq_mul, mul_zero, inv_mul_cancel₀ (mul_ne_zero h3 h2)]
      refine ⟨e2, ?_⟩
      convert hN _ e2 using 1
      simp only [Nmat, neg_zero]
    · have e3 : ((0, 0, 1, 0) : K × K × K × K) ∈ W := by
        convert hsmul (3 * w₃)⁻¹ _ hp3 using 1
        simp only [Prod.smul_mk, smul_eq_mul, mul_zero, inv_mul_cancel₀ (mul_ne_zero h3 h3')]
      refine ⟨?_, e3⟩
      convert hsmul (-1) _ (hN _ e3) using 1
      simp only [Nmat, Prod.smul_mk, smul_eq_mul, neg_zero, mul_zero, neg_mul, one_mul, neg_neg]
  have e4 : ((0, 0, 0, 1) : K × K × K × K) ∈ W := by
    convert hN _ ha using 1
    simp only [Nmat, neg_zero]
  obtain ⟨d₁, d₂, d₃, d₄⟩ := d
  have := hadd _ (hadd _ (hadd _ (hsmul d₁ _ ha) _ (hsmul d₂ _ e2)) _ (hsmul d₃ _ e3)) _
    (hsmul d₄ _ e4)
  convert this using 1
  simp only [Prod.smul_mk, Prod.mk_add_mk, smul_eq_mul, mul_zero, mul_one, add_zero, zero_add]

end CFSG.LocalAnalysis.AGL81TheoremCD.Section7.G2Max

module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Aschbacher.ML1.CoreDerived

public section

namespace CFSG.EvenSporadicStandard.HNRecog.ML1

open CFSG.EvenSporadicStandard.HNRecog.Fpf

variable {L L' : Type} [Group L] [Group L'] {N : Subgroup L} {N' : Subgroup L'}
  {θ : L →* A5 × A5} {θ' : L' →* A5 × A5} {ψ : A5 × A5 ≃* A5 × A5} {φ : L → L'} {z : L}

theorem CoreHyp.mem_fibre_z [N.Normal] (h : CoreHyp N N' θ θ' ψ φ z) :
    (z, (1 : L')) ∈ fibre θ θ' ψ N φ := by
  rw [mem_fibre_iff]
  refine ⟨by simp [map_one, (h.ker z).mpr h.z_mem], ?_⟩
  intro x hx
  simp only [one_mul, inv_one, mul_one]
  rw [(h.z_central x).symm, mul_assoc, mul_inv_cancel, mul_one]

theorem CoreHyp.mem_fibre_z' [N.Normal] (h : CoreHyp N N' θ θ' ψ φ z) :
    ((1 : L), φ z) ∈ fibre θ θ' ψ N φ := by
  rw [mem_fibre_iff]
  refine ⟨by simp [map_one, (h.ker' (φ z)).mpr (h.iso.mem z h.z_mem)], ?_⟩
  intro x hx
  simp only [one_mul, inv_one, mul_one]
  have hcomm : φ z * φ x = φ x * φ z := by
    rw [← h.iso.map_mul z h.z_mem x hx, ← h.iso.map_mul x hx z h.z_mem, h.z_central x]
  rw [hcomm, mul_assoc, mul_inv_cancel, mul_one]

theorem CoreHyp.mem_fibre_zz' [N.Normal] (h : CoreHyp N N' θ θ' ψ φ z) :
    (z, φ z) ∈ fibre θ θ' ψ N φ := by
  rw [mem_fibre_iff]
  refine ⟨by simp [map_one, (h.ker z).mpr h.z_mem, (h.ker' (φ z)).mpr (h.iso.mem z h.z_mem)], ?_⟩
  intro x hx
  have hcomm : φ z * φ x = φ x * φ z := by
    rw [← h.iso.map_mul z h.z_mem x hx, ← h.iso.map_mul x hx z h.z_mem, h.z_central x]
  rw [show z * x * z⁻¹ = x by rw [(h.z_central x).symm, mul_assoc, mul_inv_cancel, mul_one],
      show φ z * φ x * (φ z)⁻¹ = φ x by rw [hcomm, mul_assoc, mul_inv_cancel, mul_one]]

theorem CoreHyp.fibre_proj₁ [N.Normal] (h : CoreHyp N N' θ θ' ψ φ z) :
    ∀ l : L, ∃ l' : L', (l, l') ∈ fibre θ θ' ψ N φ := by
  intro l
  obtain ⟨l', hl'⟩ := h.exists_compat l
  exact ⟨l', (mem_fibre_iff θ θ' ψ N φ l l').mpr hl'⟩

theorem CoreHyp.fibre_proj₂ [N.Normal] (h : CoreHyp N N' θ θ' ψ φ z) :
    ∀ l' : L', ∃ l : L, (l, l') ∈ fibre θ θ' ψ N φ := by
  intro l'
  obtain ⟨l, hl⟩ := h.exists_compat' l'
  exact ⟨l, (mem_fibre_iff θ θ' ψ N φ l l').mpr hl⟩

theorem CoreHyp.fibre_kernel₁ [N.Normal] (h : CoreHyp N N' θ θ' ψ φ z) :
    ∀ l' : L', ((1 : L), l') ∈ fibre θ θ' ψ N φ → l' = 1 ∨ l' = φ z := by
  intro l' hmem
  rw [mem_fibre_iff] at hmem
  obtain ⟨h1, h2⟩ := hmem
  have hN' : l' ∈ N' := (h.ker' l').mp (by rw [h1]; simp)
  apply h.centre' l' hN'
  intro y hy
  obtain ⟨x, hxN, rfl⟩ := h.iso.surj y hy
  have hcx := h2 x hxN
  simp only [one_mul, inv_one, mul_one] at hcx
  exact (mul_inv_eq_iff_eq_mul).mp hcx.symm

theorem CoreHyp.fibre_kernel₂ [N.Normal] (h : CoreHyp N N' θ θ' ψ φ z) :
    ∀ l : L, (l, (1 : L')) ∈ fibre θ θ' ψ N φ → l = 1 ∨ l = z := by
  intro l hmem
  rw [mem_fibre_iff] at hmem
  obtain ⟨h1, h2⟩ := hmem
  have hθ : θ l = 1 := ψ.injective (by rw [← h1]; simp)
  have hlN : l ∈ N := (h.ker l).mp hθ
  apply h.centre l hlN
  intro x hx
  have hcx := h2 x hx
  simp only [one_mul, inv_one, mul_one] at hcx
  have hx' : l * x * l⁻¹ ∈ N := (inferInstance : N.Normal).conj_mem x hx l
  exact (mul_inv_eq_iff_eq_mul).mp (h.iso.inj (l * x * l⁻¹) hx' x hx hcx)

theorem CoreHyp.fibre_central [N.Normal] (h : CoreHyp N N' θ θ' ψ φ z) :
    (⟨(z, 1), h.mem_fibre_z⟩ : fibre θ θ' ψ N φ) ∈ Subgroup.center (fibre θ θ' ψ N φ) := by
  rw [Subgroup.mem_center_iff]
  intro g
  apply Subtype.ext
  apply Prod.ext
  · exact h.z_central g.1.1
  · simp

end CFSG.EvenSporadicStandard.HNRecog.ML1

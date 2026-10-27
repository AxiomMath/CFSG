module

public import Mathlib.FieldTheory.Finite.Basic
public import Mathlib.LinearAlgebra.BilinearForm.Orthogonal
public import Mathlib.LinearAlgebra.QuadraticForm.Basic

public section

namespace CFSG.ClassicalGroups.Orthogonal

open QuadraticMap

section Auxiliary

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

private theorem exists_polar_ne_zero_of_codim_le_two [FiniteDimensional K V]
    {Q : QuadraticForm K V} (hQ : (polarBilin Q).Nondegenerate) (h6 : 6 ≤ Module.finrank K V)
    {W : Submodule K V} (hW : Module.finrank K V ≤ Module.finrank K W + 2) :
    ∃ a ∈ W, ∃ b ∈ W, polar Q a b ≠ 0 := by
  by_contra hcon
  push Not at hcon
  have hle : W ≤ LinearMap.BilinForm.orthogonal (polarBilin Q) W := by
    intro v hv
    rw [LinearMap.BilinForm.mem_orthogonal_iff]
    intro m hm
    rw [polarBilin_apply_apply]
    exact hcon m hm v hv
  have h1 := Submodule.finrank_mono hle
  have h2 := LinearMap.BilinForm.finrank_orthogonal hQ W
  omega

private theorem exists_singular_add_smul [Finite K] [CharP K 2] {Q : QuadraticForm K V}
    {d v : V} (hd : Q d ≠ 0) (hv : polar Q d v = 0) :
    ∃ α : K, Q (v + α • d) = 0 := by
  obtain ⟨α, hα⟩ := FiniteField.isSquare_of_char_two (ringChar.eq K 2) (Q v / Q d)
  refine ⟨α, ?_⟩
  have hαd : α * α * Q d = Q v := by
    rw [← hα, div_mul_cancel₀ _ hd]
  have hvd : polar Q v d = 0 := by
    rw [polar_comm]
    exact hv
  rw [QuadraticMap.map_add Q v (α • d), QuadraticMap.map_smul, polar_smul_right, hvd,
    smul_zero, add_zero, smul_eq_mul, hαd]
  exact CharTwo.add_self_eq_zero _

end Auxiliary

theorem exists_singular_pair_of_le_perp {ι : Type} [Fintype ι] [DecidableEq ι] {K : Type}
    [Field K] [Finite K] [CharP K 2] {Q' : QuadraticForm K (ι → K)}
    (hQ : (QuadraticMap.polarBilin Q').Nondegenerate) (h6 : 6 ≤ Module.finrank K (ι → K))
    {d : ι → K} (hd : Q' d ≠ 0) (U : Submodule K (ι → K)) (hdU : d ∈ U)
    (hUd : ∀ x ∈ U, QuadraticMap.polar Q' d x = 0)
    (hdim : Module.finrank K (ι → K) ≤ Module.finrank K U + 2) :
    ∃ x₁ ∈ U, ∃ x₂ ∈ U, Q' x₁ = 0 ∧ Q' x₂ = 0 ∧ QuadraticMap.polar Q' x₁ x₂ = 1 := by
  obtain ⟨a, ha, b, hb, hab⟩ := exists_polar_ne_zero_of_codim_le_two hQ h6 hdim
  obtain ⟨b', hb'mem, hab'⟩ : ∃ b' ∈ U, polar Q' a b' = 1 :=
    ⟨(polar Q' a b)⁻¹ • b, U.smul_mem _ hb,
      by rw [polar_smul_right, smul_eq_mul, inv_mul_cancel₀ hab]⟩
  have hda : polar Q' a d = 0 := by
    rw [polar_comm]
    exact hUd a ha
  have hdb' : polar Q' d b' = 0 := hUd b' hb'mem
  have hdd : polar Q' d d = 0 := by
    rw [polar_self, CharTwo.two_nsmul]
  obtain ⟨α₁, h1⟩ := exists_singular_add_smul hd (hUd a ha)
  obtain ⟨α₂, h2⟩ := exists_singular_add_smul hd (hUd b' hb'mem)
  refine ⟨a + α₁ • d, U.add_mem ha (U.smul_mem _ hdU), b' + α₂ • d,
    U.add_mem hb'mem (U.smul_mem _ hdU), h1, h2, ?_⟩
  simp only [polar_add_left, polar_add_right, polar_smul_left, polar_smul_right, hda, hdb',
    hdd, hab', smul_zero, add_zero, zero_add, smul_eq_mul, mul_zero]

end CFSG.ClassicalGroups.Orthogonal

module

public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.SL3Lift

open Matrix Module

private theorem cube_eq_of_eigenvector {k : Type*} [Field k] (g : Matrix (Fin 3) (Fin 3) k)
    {μ b : k} (hg : g ^ 3 = μ • 1) {v : Fin 3 → k} (hv : v ≠ 0) (hgv : g *ᵥ v = b • v) :
    b ^ 3 = μ := by
  have key : ∀ n : ℕ, (g ^ n) *ᵥ v = b ^ n • v := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [pow_succ', ← Matrix.mulVec_mulVec, ih, Matrix.mulVec_smul, hgv, smul_smul, pow_succ]
  have h3 := key 3
  rw [hg, Matrix.smul_mulVec, Matrix.one_mulVec] at h3
  exact (smul_left_injective k hv h3).symm

private theorem exists_eigenvector_of_line {k : Type*} [Field k] (g : Matrix (Fin 3) (Fin 3) k)
    (W : Submodule k (Fin 3 → k)) (hW : finrank k W = 1) (hinv : ∀ w ∈ W, g *ᵥ w ∈ W) :
    ∃ (v : Fin 3 → k) (b : k), v ≠ 0 ∧ g *ᵥ v = b • v := by
  obtain ⟨⟨v, hvW⟩, hv0, hspan⟩ := finrank_eq_one_iff'.1 hW
  obtain ⟨c, hc⟩ := hspan ⟨g *ᵥ v, hinv v hvW⟩
  exact ⟨v, c, fun h => hv0 (Subtype.ext h), (congrArg Subtype.val hc).symm⟩

theorem exists_cube_root_of_commute {k : Type*} [Field k] (s g : Matrix (Fin 3) (Fin 3) k)
    (hsg : s * g = g * s) (r : Fin 3 → k)
    (hs : (s - r 0 • (1 : Matrix (Fin 3) (Fin 3) k)) * (s - r 1 • 1) * (s - r 2 • 1) = 0)
    (hns : ∀ c : k, s ≠ c • 1) {μ : k} (hg : g ^ 3 = μ • 1) : ∃ b : k, b ^ 3 = μ := by
  classical
  have hdet : ∃ j : Fin 3, (s - r j • (1 : Matrix (Fin 3) (Fin 3) k)).det = 0 := by
    have h := congrArg Matrix.det hs
    rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_zero] at h
    rcases mul_eq_zero.1 h with h | h
    · rcases mul_eq_zero.1 h with h | h
      · exact ⟨0, h⟩
      · exact ⟨1, h⟩
    · exact ⟨2, h⟩
  obtain ⟨j, hj⟩ := hdet
  set N : Matrix (Fin 3) (Fin 3) k := s - r j • (1 : Matrix (Fin 3) (Fin 3) k) with hN
  have hNg : N * g = g * N := by
    simp [hN, sub_mul, mul_sub, hsg]
  have hN0 : N ≠ 0 := fun h => hns (r j) (sub_eq_zero.1 h)
  let f : (Fin 3 → k) →ₗ[k] (Fin 3 → k) := Matrix.mulVecLin N
  have hrn := LinearMap.finrank_range_add_finrank_ker f
  rw [Module.finrank_fin_fun] at hrn
  have hker : LinearMap.ker f ≠ ⊥ := by
    obtain ⟨v, hv0, hv⟩ := Matrix.exists_mulVec_eq_zero_iff.2 hj
    exact (Submodule.ne_bot_iff _).2 ⟨v, by simpa [f] using hv, hv0⟩
  have hran : LinearMap.range f ≠ ⊥ := by
    intro h
    apply hN0
    have hf : f = 0 := LinearMap.range_eq_bot.1 h
    ext i l
    have := congrArg (fun φ : (Fin 3 → k) →ₗ[k] (Fin 3 → k) => φ (Pi.single l 1) i) hf
    simpa [f, Matrix.mulVec_single_one] using this
  have hker1 := Submodule.one_le_finrank_iff.2 hker
  have hran1 := Submodule.one_le_finrank_iff.2 hran
  have hcases : finrank k (LinearMap.range f) = 1 ∨ finrank k (LinearMap.ker f) = 1 := by
    omega
  have hkinv : ∀ w ∈ LinearMap.ker f, g *ᵥ w ∈ LinearMap.ker f := by
    intro w hw
    have hw' : N *ᵥ w = 0 := by simpa [f] using hw
    simp only [LinearMap.mem_ker, f, Matrix.mulVecLin_apply]
    rw [Matrix.mulVec_mulVec, hNg, ← Matrix.mulVec_mulVec, hw', Matrix.mulVec_zero]
  have hrinv : ∀ w ∈ LinearMap.range f, g *ᵥ w ∈ LinearMap.range f := by
    rintro w ⟨u, rfl⟩
    refine ⟨g *ᵥ u, ?_⟩
    simp only [f, Matrix.mulVecLin_apply]
    rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hNg]
  obtain ⟨v, b, hv0, hgv⟩ : ∃ (v : Fin 3 → k) (b : k), v ≠ 0 ∧ g *ᵥ v = b • v := by
    rcases hcases with h | h
    · exact exists_eigenvector_of_line g _ h hrinv
    · exact exists_eigenvector_of_line g _ h hkinv
  exact ⟨b, cube_eq_of_eigenvector g hg hv0 hgv⟩

end CFSG.LocalAnalysis.RankThreeTheoremC.SL3Lift

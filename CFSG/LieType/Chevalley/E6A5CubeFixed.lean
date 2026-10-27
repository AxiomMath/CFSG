module

public import CFSG.LieType.Chevalley.E6A5CubeTwist

public noncomputable section

namespace CFSG.LieType.Chevalley.E6A5Cube

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley.ExteriorCube exteriorPower
  Set Matrix CFSG.LocalAnalysis.ComponentInitial

variable {K : Type} [Field K]

variable (K) in
@[expose] def scalarSL (l : K) (hl : l ^ 6 = 1) : SpecialLinearGroup (Fin 6) K :=
  ⟨l • (1 : Matrix (Fin 6) (Fin 6) K), by
    rw [Matrix.det_smul, det_one, mul_one, Fintype.card_fin, hl]⟩

theorem coe_scalarSL (l : K) (hl : l ^ 6 = 1) :
    (scalarSL K l hl : Matrix (Fin 6) (Fin 6) K) = l • (1 : Matrix (Fin 6) (Fin 6) K) := rfl

theorem cubeHom_scalarSL {l : K} (hl3 : l ^ 3 = 1) :
    cubeHom (scalarSL K l (by rw [show 6 = 3 * 2 from rfl, pow_mul, hl3, one_pow])) = 1 :=
  (cubeHom_eq_one_iff _).2 ⟨l, hl3, rfl⟩

variable (K) in
@[expose] def SUM (σ : K →+* K) : Subgroup (SpecialLinearGroup (Fin 6) K) :=
  MonoidHom.eqLocus (tauSL K σ) (MonoidHom.id _)

theorem mem_SUM_iff (σ : K →+* K) {h : SpecialLinearGroup (Fin 6) K} :
    h ∈ SUM K σ ↔ tauSL K σ h = h := Iff.rfl

section Fixed

variable [Finite K]

theorem twistA_liftA_of_mem_SUM (σ : K →+* K) {h : SpecialLinearGroup (Fin 6) K}
    (hh : h ∈ SUM K σ) : twistA K σ (liftA K h) = liftA K h := by
  have h1 : psiA K (twistA K σ (liftA K h)) = cubeHom (tauSL K σ h) :=
    psiA_twistA σ (psiA_liftA h)
  rw [(mem_SUM_iff σ).1 hh] at h1
  exact psiA_injective (h1.trans (psiA_liftA h).symm)

theorem exists_mem_SUM_of_twist_fixed {σ : K →+* K} (hσσ : ∀ c, σ (σ c) = c) {g : groupA K}
    (hg : twistA K σ g = g) : ∃ h ∈ SUM K σ, psiA K g = cubeHom h := by
  obtain ⟨h₀, hh₀⟩ : psiA K g ∈ (cubeHom (K := K)).range := by
    rw [← range_psiA]
    exact ⟨g, rfl⟩
  have hψ : psiA K g = cubeHom h₀ := hh₀.symm
  have h1 : cubeHom (tauSL K σ h₀) = cubeHom h₀ := by
    rw [← psiA_twistA σ hψ, hg, hψ]
  set z₀ : SpecialLinearGroup (Fin 6) K := h₀⁻¹ * tauSL K σ h₀ with hz₀
  have h2 : cubeHom z₀ = 1 := by
    rw [hz₀, map_mul, map_inv, h1, inv_mul_cancel]
  obtain ⟨ω, hω3, hω⟩ := (cubeHom_eq_one_iff _).1 h2
  have hω6 : ω ^ 6 = 1 := by rw [show 6 = 3 * 2 from rfl, pow_mul, hω3, one_pow]
  have hω0 : ω ≠ 0 := by
    rintro rfl
    simp at hω3
  have hτ : tauSL K σ h₀ = h₀ * z₀ := by rw [hz₀]; group
  have hσω : σ ω = ω := by
    have e : tauSL K σ (tauSL K σ h₀) = h₀ := tauSL_tauSL σ hσσ h₀
    rw [hτ, map_mul, hτ] at e
    have e' : z₀ * tauSL K σ z₀ = 1 :=
      mul_left_cancel (a := h₀) (by rw [← mul_assoc, e, mul_one])
    have hz := tauSL_smul_one σ (z := z₀) (l := ω) hω
    have e'' := congrArg (fun x : SpecialLinearGroup (Fin 6) K =>
      (x : Matrix (Fin 6) (Fin 6) K) 0 0) e'
    simp only [Matrix.SpecialLinearGroup.coe_mul, hω, hz, Matrix.smul_mul, Matrix.mul_smul,
      Matrix.mul_one, smul_smul, Matrix.smul_apply, Matrix.one_apply_eq, smul_eq_mul,
      Matrix.SpecialLinearGroup.coe_one] at e''
    have hσω0 : σ ω ≠ 0 := by simpa using hω0
    field_simp at e''
    exact e''.symm
  have hω'3 : (ω ^ 2) ^ 3 = 1 := by rw [← pow_mul, show 2 * 3 = 3 * 2 from rfl, pow_mul, hω3, one_pow]
  have hω'6 : (ω ^ 2) ^ 6 = 1 := by rw [show 6 = 3 * 2 from rfl, pow_mul, hω'3, one_pow]
  set z₁ := scalarSL K (ω ^ 2) hω'6 with hz₁
  refine ⟨z₁ * h₀, ?_, ?_⟩
  · rw [mem_SUM_iff, map_mul]
    apply Subtype.ext
    have hσ2 : σ (ω ^ 2) = ω ^ 2 := by rw [map_pow, hσω]
    have hz1 : (tauSL K σ z₁ : Matrix (Fin 6) (Fin 6) K) = ((ω ^ 2)⁻¹) • (1 : Matrix _ _ K) := by
      have := tauSL_smul_one σ (z := z₁) (l := ω ^ 2) rfl
      rwa [hσ2] at this
    have hz0 := tauSL_smul_one σ (z := z₀) (l := ω) hω
    rw [hσω] at hz0
    rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, hz1, hτ,
      Matrix.SpecialLinearGroup.coe_mul, hω, hz₁, coe_scalarSL, Matrix.smul_mul, Matrix.one_mul,
      Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul, Matrix.one_mul, smul_smul]
    congr 1
    have : ((ω ^ 2)⁻¹ * ω) = ω ^ 2 := by
      rw [inv_mul_eq_iff_eq_mul₀ (pow_ne_zero 2 hω0), ← pow_add,
        show 2 + 2 = 3 + 1 from rfl, pow_add, hω3, one_mul, pow_one]
    rw [this]
  · rw [map_mul, cubeHom_scalarSL hω'3, one_mul, hψ]

end Fixed

end CFSG.LieType.Chevalley.E6A5Cube

module

public import CFSG.GH74.Generic.S45.LUniLift
public import CFSG.GH74.KGroups.L3EpsUniBlock

public section

open Matrix Subgroup CFSG.GH74.KGroups.L3Eps.Uni CFSG.ClassicalGroups.UnitaryFlag
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  CFSG.ClassicalInvolution.ModelFacts.UnitaryAut
open scoped MatrixGroups

namespace CFSG.GH74.GLS.Stage2.Signalizer.Odd87

section Aut

theorem fu3_aut_core {p f : ℕ} {F : Type} [Field F] (h : UnitaryFieldData p f F)
    {K : Type} [Group K] {θ : ↥(unitarySU p f F 3) →* K} (hθ : IsCover h θ)
    (Ω : Subgroup ↥(unitarySU p f F 3))
    (hcent : ∀ (B : GL (Fin 3) F) (σ : F ≃+* F),
      (∀ g ∈ Ω, ∃ c : Fˣ, B * glAut σ (g : GL (Fin 3) F) * B⁻¹ =
        (g : GL (Fin 3) F) * GeneralLinearGroup.scalar (Fin 3) c) →
      ∀ g ∈ Ω, B * glAut σ (g : GL (Fin 3) F) * B⁻¹ = (g : GL (Fin 3) F))
    (hcomm : ∀ T : Matrix (Fin 3) (Fin 3) F,
      (∀ g ∈ Ω, T * ((g : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) =
        ((g : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) * T) →
      ∃ c : F, T = c • (1 : Matrix (Fin 3) (Fin 3) F))
    {ψ : MulAut K} (hfix : ∀ g ∈ Ω, ψ (θ g) = θ g)
    (Φ : ↥(unitarySU p f F 3) →* ↥(unitarySU p f F 3)) (C : GL (Fin 3) F)
    (hΦ : ∀ g, θ (Φ g) = ψ (θ g))
    (hC : ∀ g, ((Φ g : ↥(unitarySU p f F 3)) : GL (Fin 3) F) = C * (g : GL (Fin 3) F) * C⁻¹) :
    ψ = 1 := by
  have h1 : ∀ g ∈ Ω, ∃ c : Fˣ, C * glAut (1 : F ≃+* F) (g : GL (Fin 3) F) * C⁻¹ =
      (g : GL (Fin 3) F) * GeneralLinearGroup.scalar (Fin 3) c := by
    intro g hg
    have hθg : θ g = θ (Φ g) := by rw [hΦ, hfix g hg]
    obtain ⟨c, -, -, hc⟩ := (theta_eq_iff h θ hθ.ker).1 hθg
    refine ⟨c, ?_⟩
    apply Units.ext
    rw [map_one, MulAut.one_apply, ← hC, Units.val_mul, GeneralLinearGroup.coe_scalar]
    exact hc
  have h2 := hcent C 1 h1
  have hCcomm : ∀ g ∈ Ω, ((C : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) *
      ((g : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) =
      ((g : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) * ((C : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) := by
    intro g hg
    have h3 := h2 g hg
    rw [map_one, MulAut.one_apply] at h3
    have h4 : C * (g : GL (Fin 3) F) = (g : GL (Fin 3) F) * C := by
      calc C * (g : GL (Fin 3) F) = (C * (g : GL (Fin 3) F) * C⁻¹) * C := by group
        _ = (g : GL (Fin 3) F) * C := by rw [h3]
    simpa using congrArg (fun x : GL (Fin 3) F => (x : Matrix (Fin 3) (Fin 3) F)) h4
  obtain ⟨c, hc⟩ := hcomm _ hCcomm
  have hcentral : ∀ x : GL (Fin 3) F, C * x = x * C := by
    intro x
    apply Units.ext
    rw [Units.val_mul, Units.val_mul, hc, Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul,
      Matrix.mul_one]
  have hΦid : ∀ g, Φ g = g := by
    intro g
    apply Subtype.ext
    rw [hC, hcentral, mul_assoc, mul_inv_cancel, mul_one]
  ext x
  obtain ⟨g, rfl⟩ := hθ.surj x
  rw [← hΦ, hΦid]
  rfl

end Aut

section Main

theorem aut_fixing_trivial_unitary {p f : ℕ} {F : Type} [Field F] (h : UnitaryFieldData p f F) (hp : p ≠ 2)
    {K : Type} [Group K] {θ : ↥(unitarySU p f F 3) →* K} (hθ : IsCover h θ)
    (Ω : Subgroup ↥(unitarySU p f F 3))
    (hcent : ∀ (B : GL (Fin 3) F) (σ : F ≃+* F),
      (∀ g ∈ Ω, ∃ c : Fˣ, B * glAut σ (g : GL (Fin 3) F) * B⁻¹ =
        (g : GL (Fin 3) F) * GeneralLinearGroup.scalar (Fin 3) c) →
      ∀ g ∈ Ω, B * glAut σ (g : GL (Fin 3) F) * B⁻¹ = (g : GL (Fin 3) F))
    (hcomm : ∀ T : Matrix (Fin 3) (Fin 3) F,
      (∀ g ∈ Ω, T * ((g : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) =
        ((g : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) * T) → ∃ c : F, T = c • (1 : Matrix (Fin 3) (Fin 3) F))
    (htr : ∀ σ : F ≃+* F, (∀ g ∈ Ω, σ (Matrix.trace ((g : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F)) =
      Matrix.trace ((g : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F)) → σ = 1 ∨ ∀ c, σ c = h.bar c)
    {ψ : MulAut K} {n : ℕ} (hn : Odd n) (hψ : ψ ^ n = 1) (hfix : ∀ g ∈ Ω, ψ (θ g) = θ g) : ψ = 1 := by
  have hker : θ.ker ≤ Subgroup.center ↥(unitarySU p f F 3) := by
    rw [hθ.ker]
    exact unitaryScalars_le_center h 3
  obtain ⟨A, φ, hA, -, hlift, -⟩ :=
    CFSG.GH74.Generic.S45.exists_lift_unitarySU' h hp (le_refl 3) θ hθ.surj hker ψ
  have hΦmat : ∀ g : ↥(unitarySU p f F 3),
      ((unitaryConjHom A φ hA g : ↥(unitarySU p f F 3)) : GL (Fin 3) F) =
        A * glAut φ (g : GL (Fin 3) F) * A⁻¹ := fun g => rfl
  have h1 : ∀ g ∈ Ω, ∃ c : Fˣ, A * glAut φ (g : GL (Fin 3) F) * A⁻¹ =
      (g : GL (Fin 3) F) * GeneralLinearGroup.scalar (Fin 3) c := by
    intro g hg
    have hθg : θ g = θ (unitaryConjHom A φ hA g) := by rw [hlift, hfix g hg]
    obtain ⟨c, -, -, hc⟩ := (theta_eq_iff h θ hθ.ker).1 hθg
    refine ⟨c, ?_⟩
    apply Units.ext
    rw [← hΦmat, Units.val_mul, GeneralLinearGroup.coe_scalar]
    exact hc
  have h2 := hcent A φ h1
  have hφfix : ∀ g ∈ Ω, φ (Matrix.trace ((g : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F)) =
      Matrix.trace ((g : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) := by
    intro g hg
    have h3 := congrArg (fun x : GL (Fin 3) F => Matrix.trace (x : Matrix (Fin 3) (Fin 3) F))
      (h2 g hg)
    simp only [Units.val_mul, coe_glAut] at h3
    rw [Matrix.mul_assoc, Matrix.trace_mul_comm, Matrix.mul_assoc, ← Units.val_mul, inv_mul_cancel,
      Units.val_one, Matrix.mul_one] at h3
    exact (AddMonoidHom.map_trace φ.toAddMonoidHom
      ((g : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F)).trans h3
  rcases htr φ hφfix with hφ1 | hφbar
  ·
    refine fu3_aut_core h hθ Ω hcent hcomm hfix (unitaryConjHom A φ hA) A hlift fun g => ?_
    rw [hΦmat, hφ1, map_one, MulAut.one_apply]
  ·
    have hφφ : φ * φ = 1 := by
      ext c
      show φ (φ c) = c
      rw [hφbar, hφbar, h.bar_bar]
    have hgg : ∀ x : GL (Fin 3) F, glAut φ (glAut φ x) = x := by
      intro x
      have : (glAut (ι := Fin 3) φ * glAut (ι := Fin 3) φ : MulAut (GL (Fin 3) F)) = 1 := by
        rw [← map_mul, hφφ, map_one]
      exact congrArg (fun e : MulAut (GL (Fin 3) F) => e x) this
    have hΦ2 : ∀ g : ↥(unitarySU p f F 3),
        ((unitaryConjHom A φ hA (unitaryConjHom A φ hA g) : ↥(unitarySU p f F 3)) :
          GL (Fin 3) F) = (A * glAut φ A) * (g : GL (Fin 3) F) * (A * glAut φ A)⁻¹ := by
      intro g
      rw [hΦmat (unitaryConjHom A φ hA g), hΦmat g, map_mul, map_mul, map_inv, hgg]
      group
    have hΦk : ∀ k : ℕ, ∃ (Ψ : ↥(unitarySU p f F 3) →* ↥(unitarySU p f F 3)) (D : GL (Fin 3) F),
        (∀ g, θ (Ψ g) = ((ψ * ψ) ^ k) (θ g)) ∧
        ∀ g, ((Ψ g : ↥(unitarySU p f F 3)) : GL (Fin 3) F) = D * (g : GL (Fin 3) F) * D⁻¹ := by
      intro k
      induction k with
      | zero => exact ⟨MonoidHom.id _, 1, fun g => by simp, fun g => by simp⟩
      | succ k ih =>
        obtain ⟨Ψ, D, hΨθ, hΨD⟩ := ih
        refine ⟨Ψ.comp ((unitaryConjHom A φ hA).comp (unitaryConjHom A φ hA)),
          D * (A * glAut φ A), fun g => ?_, fun g => ?_⟩
        · rw [MonoidHom.comp_apply, MonoidHom.comp_apply, hΨθ, hlift, hlift, pow_succ]
          simp only [MulAut.mul_apply]
        · rw [MonoidHom.comp_apply, MonoidHom.comp_apply, hΨD, hΦ2]
          group
    obtain ⟨m, hm⟩ := hn
    obtain ⟨Ψ, D, hΨθ, hΨD⟩ := hΦk (m + 1)
    have hψpow : (ψ * ψ) ^ (m + 1) = ψ := by
      calc (ψ * ψ) ^ (m + 1) = ψ ^ (2 * (m + 1)) := by rw [← sq, ← pow_mul]
        _ = ψ ^ n * ψ := by rw [show 2 * (m + 1) = n + 1 by omega, pow_succ]
        _ = ψ := by rw [hψ, one_mul]
    refine fu3_aut_core h hθ Ω hcent hcomm hfix Ψ D (fun g => ?_) hΨD
    rw [hΨθ, hψpow]

end Main

end CFSG.GH74.GLS.Stage2.Signalizer.Odd87

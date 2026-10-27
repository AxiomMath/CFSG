module

public import CFSG.ClassicalInvolution.Asc77.AscC5OM23
public import CFSG.ClassicalInvolution.Asc77.AscC5OM24
public import CFSG.LieType.HighestRoot.SL2Outer
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

namespace CFSG.ClassicalInvolution.Asc77.C5O.M

open CFSG.Assembly.LowTwoRank
open CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Models.SymplecticPairs
open CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher
open CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag
open CFSG.LieType.Universal.Symplectic.SpExtras (mat mat_apply mat_injective)
open scoped Matrix MatrixGroups

variable {F : Type} [Field F]

theorem det_scl (ℓ : Fˣ) :
    ((scl ℓ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F).det = (ℓ : F) ^ 2 := by
  simp [Matrix.scalar_apply, sq]

theorem det_glm (σ : F ≃+* F) (X : GL (Fin 2) F) :
    ((glm σ X : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F).det =
      σ ((X : Matrix (Fin 2) (Fin 2) F).det) :=
  (RingHom.map_det (σ : F →+* F) _).symm

theorem det_gl_mul (X Y : GL (Fin 2) F) :
    ((X * Y : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F).det =
      (X : Matrix (Fin 2) (Fin 2) F).det * (Y : Matrix (Fin 2) (Fin 2) F).det := by
  rw [Units.val_mul, Matrix.det_mul]

theorem det_gl_inv (X : GL (Fin 2) F) :
    ((X⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F).det =
      ((X : Matrix (Fin 2) (Fin 2) F).det)⁻¹ := by
  rw [Matrix.coe_units_inv, Matrix.det_nonsing_inv, Ring.inverse_eq_inv']

theorem det_rel {X Y d : GL (Fin 2) F} {σ : F ≃+* F} {ℓ : Fˣ} {μ μ' : F}
    (hX : (X : Matrix (Fin 2) (Fin 2) F).det = μ) (hY : (Y : Matrix (Fin 2) (Fin 2) F).det = μ')
    (h : Y * glm σ d = scl ℓ * (d * X)) :
    μ' * σ (d : Matrix (Fin 2) (Fin 2) F).det = (ℓ : F) ^ 2 *
      (d : Matrix (Fin 2) (Fin 2) F).det * μ := by
  have e := congrArg (fun Z : GL (Fin 2) F => (Z : Matrix (Fin 2) (Fin 2) F).det) h
  simp only [det_gl_mul, det_glm, det_scl, hX, hY] at e
  rw [e]
  ring

theorem det_rel_swap {X Y d : GL (Fin 2) F} {π : F ≃+* F} {lam : Fˣ} {μ μ' : F}
    (hX : (X : Matrix (Fin 2) (Fin 2) F).det = μ) (hY : (Y : Matrix (Fin 2) (Fin 2) F).det = μ')
    (h : Y * glm π d = scl lam * (d⁻¹ * X)) :
    μ' * π (d : Matrix (Fin 2) (Fin 2) F).det * (d : Matrix (Fin 2) (Fin 2) F).det =
      (lam : F) ^ 2 * μ := by
  have hd : (d : Matrix (Fin 2) (Fin 2) F).det ≠ 0 := (Matrix.isUnits_det_units d).ne_zero
  have e := congrArg (fun Z : GL (Fin 2) F => (Z : Matrix (Fin 2) (Fin 2) F).det) h
  simp only [det_gl_mul, det_glm, det_scl, det_gl_inv, hX, hY] at e
  rw [e]
  field_simp

theorem isSquare_comm_det [Finite F] (hF : ringChar F ≠ 2) (σ τ : F ≃+* F) {μ η : F}
    (hμ : μ ≠ 0) (hη : η ≠ 0) : IsSquare (μ * σ η * (τ μ)⁻¹ * η⁻¹) := by
  have h1 := CFSG.ComponentClassification.RankTwoOddLie.isSquare_ringEquiv_mul_inv hF σ hη
  have h2 := (CFSG.ComponentClassification.RankTwoOddLie.isSquare_ringEquiv_mul_inv hF τ hμ).inv
  have e : μ * σ η * (τ μ)⁻¹ * η⁻¹ = σ η * η⁻¹ * (τ μ * μ⁻¹)⁻¹ := by
    have : τ μ ≠ 0 := (map_ne_zero τ).mpr hμ
    field_simp
  rw [e]
  exact h1.mul h2

theorem exists_sl_smul {c : GL (Fin 2) F} {s : F} (hs : s ≠ 0)
    (h : (c : Matrix (Fin 2) (Fin 2) F).det = s * s) :
    ∃ w : SL(2, F), (c : Matrix (Fin 2) (Fin 2) F) = s • (w : Matrix (Fin 2) (Fin 2) F) := by
  refine ⟨⟨s⁻¹ • (c : Matrix (Fin 2) (Fin 2) F), ?_⟩, ?_⟩
  · rw [Matrix.det_smul, h, Fintype.card_fin]
    field_simp
  · change _ = s • (s⁻¹ • _)
    rw [smul_smul, mul_inv_cancel₀ hs, one_smul]

variable {Y : Type} [Group Y] {Φ : Set (Subgroup Y)} {A A' : Subgroup Y} {z' : Y}

theorem Frame.inner_of_lift (fr : Frame F Y Φ A A' z') (c : Y → Y) (C : gsp 2 F)
    (hc : ∀ x, c (fr.ψ x) = fr.ψ (conjSp 2 F C x)) {cb : Fin 2 → GL (Fin 2) F}
    (hC : gm C = bd (fun k => (cb k : Matrix (Fin 2) (Fin 2) F))) {s : F} (hs : s ≠ 0)
    (w₀ w₁ : SL(2, F))
    (h₀ : (cb 0 : Matrix (Fin 2) (Fin 2) F) = s • (w₀ : Matrix (Fin 2) (Fin 2) F))
    (h₁ : (cb 1 : Matrix (Fin 2) (Fin 2) F) = s • (w₁ : Matrix (Fin 2) (Fin 2) F)) (y : Y) :
    c y = fr.ψ (longBlock F 2 0 w₀ * longBlock F 2 1 w₁) * y *
      (fr.ψ (longBlock F 2 0 w₀ * longBlock F 2 1 w₁))⁻¹ := by
  obtain ⟨x, rfl⟩ := fr.surj y
  rw [hc, conjSp_eq_conj_of_bd C hC hs w₀ w₁ h₀ h₁ x, map_mul, map_mul, map_inv]

end CFSG.ClassicalInvolution.Asc77.C5O.M

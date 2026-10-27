module

public import CFSG.ClassicalInvolution.Asc77.AscC5OM4
public import CFSG.ClassicalInvolution.Asc77.AscC5OM11

public section

namespace CFSG.ClassicalInvolution.Asc77.C5O.M

open CFSG.Assembly.LowTwoRank
open CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Models.SymplecticPairs
open CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher
open CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag
open CFSG.LieType.Universal.Symplectic.SpExtras (mat mat_apply mat_injective)
open scoped Matrix

variable {F : Type} [Field F]

abbrev gm (M : gsp 2 F) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F :=
  ((M : GL (Fin 2 ⊕ Fin 2) F) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F)

noncomputable abbrev mu (M : gsp 2 F) : F := ((multiplier 2 F M : Fˣ) : F)

theorem gm_transpose_mul (M : gsp 2 F) : (gm M)ᵀ * gram F 2 * gm M = mu M • gram F 2 :=
  multiplier_spec M

theorem stable_of_isSquare (h2 : (2 : F) ≠ 0) (M : gsp 2 F) (σ : F ≃+* F)
    (hσ2 : ∀ x, σ (σ x) = x) {a : F} (hMa : gm M * (gm M).map σ = a • 1)
    (hsq : IsSquare (mu M)) :
    ∃ (u w : Fin 2 ⊕ Fin 2 → F) (s : StatedSp 2 F), form u w = 1 ∧
      s ∈ planeGroup (Submodule.span F {u, w}) ∧ s * s * (s * s) = 1 ∧
      (¬ ∃ c : F, mat 2 F (s * s) = c • 1) ∧ conjSp 2 F M (fieldSp 2 F σ s) = s := by
  obtain ⟨l, hl⟩ := hsq
  have hl0 : l ≠ 0 := by
    rintro rfl
    have h0 : mu M = 0 := by rw [hl, mul_zero]
    exact Units.ne_zero _ h0
  have hNspec : (gm M)ᵀ * gram F 2 * gm M = (l * l) • gram F 2 := by
    rw [gm_transpose_mul, hl]
  obtain ⟨N₁, hN₁⟩ : ∃ N₁ : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F, N₁ = l⁻¹ • gm M :=
    ⟨_, rfl⟩
  have hN₁iso : N₁ᵀ * gram F 2 * N₁ = gram F 2 := by
    rw [hN₁]
    simp only [Matrix.transpose_smul, Matrix.smul_mul, Matrix.mul_smul, smul_smul]
    rw [hNspec, smul_smul]
    have : l⁻¹ * l⁻¹ * (l * l) = 1 := by field_simp
    rw [this, one_smul]
  have hmapN₁ : N₁.map σ = σ l⁻¹ • (gm M).map σ := by
    ext i j
    simp [hN₁, Matrix.map_apply]
  have hNN : N₁ * N₁.map σ = (l⁻¹ * σ l⁻¹ * a) • 1 := by
    rw [hmapN₁, hN₁, Matrix.smul_mul, Matrix.mul_smul, hMa, smul_smul, smul_smul]
  have hc'1 : (l⁻¹ * σ l⁻¹ * a) * (l⁻¹ * σ l⁻¹ * a) = 1 := by
    have hiso' := C25W.Sp.map_isometry σ N₁ hN₁iso
    have h1 : (N₁ * N₁.map σ)ᵀ * gram F 2 * (N₁ * N₁.map σ) = gram F 2 := by
      calc (N₁ * N₁.map σ)ᵀ * gram F 2 * (N₁ * N₁.map σ) =
          (N₁.map σ)ᵀ * (N₁ᵀ * gram F 2 * N₁) * N₁.map σ := by
            simp only [Matrix.transpose_mul, Matrix.mul_assoc]
        _ = gram F 2 := by rw [hN₁iso]; exact hiso'
    rw [hNN] at h1
    have e := congrFun (congrFun h1 (Sum.inl 0)) (Sum.inr 0)
    simp [Matrix.transpose_smul, gram, Matrix.fromBlocks] at e
    simpa using e
  obtain ⟨u, w, s, huw, hs, hs4, hsc, hcomm⟩ :=
    C25W.Sp.exists_stable_rotation (m := 0) σ N₁ hσ2 h2 hN₁iso _ hc'1 hNN
  refine ⟨u, w, s, huw, hs, hs4, hsc, ?_⟩
  apply Subtype.ext
  rw [coe_conjSp, mul_inv_eq_iff_eq_mul]
  apply Units.ext
  rw [Units.val_mul, Units.val_mul, coe_fieldSp]
  have hMl : gm M = l • N₁ := by rw [hN₁, smul_inv_smul₀ hl0]
  have e : N₁ * (mat 2 F s).map σ = mat 2 F s * N₁ := hcomm
  have key : gm M * (mat 2 F s).map σ = mat 2 F s * gm M := by
    calc gm M * (mat 2 F s).map σ = l • (N₁ * (mat 2 F s).map σ) := by
          rw [hMl, Matrix.smul_mul]
      _ = l • (mat 2 F s * N₁) := by rw [e]
      _ = mat 2 F s * gm M := by rw [hMl, Matrix.mul_smul]
  exact key

theorem mu_mul_gspFieldMap (σ : F ≃+* F) (M : gsp 2 F) :
    mu (M * gspFieldMap σ M) = mu M * σ (mu M) := by
  rw [mu, map_mul, Units.val_mul, C25W.Sp.multiplier_gspFieldMap]

theorem mu_eq_of_gm_eq (M : gsp 2 F) {a : F} (h : gm M = a • 1) : mu M = a * a := by
  have hs := gm_transpose_mul M
  rw [h] at hs
  have e := congrFun (congrFun hs (Sum.inl 0)) (Sum.inr 0)
  simp [Matrix.transpose_smul, gram, Matrix.fromBlocks] at e
  linear_combination -e

theorem map_scalar_eq {σ : F ≃+* F} (hσ2 : ∀ x, σ (σ x) = x) {X : Matrix (Fin 2 ⊕ Fin 2)
    (Fin 2 ⊕ Fin 2) F} {a : F} (ha : a ≠ 0) (h : X * X.map σ = a • 1) : σ a = a := by
  have h1 : X.map σ * X = a • 1 := by
    have h2 : (a⁻¹ • X) * X.map σ = 1 := by rw [Matrix.smul_mul, h, smul_smul, inv_mul_cancel₀ ha,
      one_smul]
    have h3 := mul_eq_one_comm.mp h2
    rw [Matrix.mul_smul] at h3
    calc X.map σ * X = a • (a⁻¹ • (X.map σ * X)) := by rw [smul_smul, mul_inv_cancel₀ ha, one_smul]
      _ = a • 1 := by rw [h3]
  have h4 := congrArg (fun Z => Z.map σ) h
  simp only [map_mul_ringEquiv] at h4
  have hmm : (X.map σ).map σ = X := by
    ext i j
    simp [Matrix.map_apply, hσ2]
  rw [hmm, h1] at h4
  have e := congrFun (congrFun h4 (Sum.inl 0)) (Sum.inl 0)
  simp [Matrix.map_apply] at e
  exact e.symm

theorem fieldSp_of_forall_eq {σ : F ≃+* F} (hσ : ∀ x, σ x = x) (g : StatedSp 2 F) :
    fieldSp 2 F σ g = g := by
  apply Subtype.ext
  apply Units.ext
  rw [coe_fieldSp]
  ext i j
  simp [Matrix.map_apply, hσ]

namespace Frame

variable {Y : Type} [Group Y] {Φ : Set (Subgroup Y)} {A A' : Subgroup Y} {z' : Y}
  (fr : Frame F Y Φ A A' z')
include fr

theorem proj_eq_of_ψ_eq {a b : StatedSp 2 F} (h : fr.ψ a = fr.ψ b) :
    proj 2 F a = proj 2 F b := by
  rcases fr.lift_eq_iff.mp h with rfl | rfl
  · rfl
  · have h1 : proj 2 F (negOne F) = 1 := by
      rw [← MonoidHom.mem_ker, ker_proj]
      exact negOne_mem_spScalars
    rw [map_mul, h1, mul_one]

theorem exc_shape [Finite F] {p : ℕ} [Fact p.Prime] [CharP F p] (hp : p ≠ 2) (h2 : (2 : F) ≠ 0)
    (h4 : 4 ≤ Nat.card F) (β : Y ≃* Y) (hβ2 : ∀ x, β (β x) = x)
    (hfix : ∀ J ∈ Φ, ∀ x ∈ J, x * x * x * x = 1 → x * x ≠ 1 → β x ≠ x) :
    ∃ M : gsp 2 F, (∀ x, β (fr.ψ x) = fr.ψ (conjSp 2 F M x)) ∧ ¬ IsSquare (mu M) ∧
      (gm M * gm M = mu M • 1 ∨ gm M * gm M = (-mu M) • 1) := by
  obtain ⟨M, σ, hβM⟩ := fr.exists_lift_aut h2 β
  have hsq1 : (conjAut 2 F M * fieldAut 2 F σ) * (conjAut 2 F M * fieldAut 2 F σ) = 1 := by
    ext u
    obtain ⟨x, rfl⟩ := proj_surjective (r := 2) (K := F) u
    simp only [MulAut.mul_apply, conjAut_proj, fieldAut_proj, MulAut.one_apply]
    apply fr.proj_eq_of_ψ_eq
    rw [← hβM, ← hβM, hβ2]
  rw [C25W.Sp.sq_formula] at hsq1
  obtain ⟨hσσ, a, ha, hMa⟩ := C25W.Sp.shape_of_trivial h4 _ _ hsq1
  have hσ2 : ∀ x, σ (σ x) = x := fun x => by
    have := RingEquiv.congr_fun hσσ x
    simpa using this
  have hMa' : gm M * (gm M).map σ = a • 1 := by
    have := hMa
    rw [Subgroup.coe_mul, Units.val_mul] at this
    exact this
  have hns : ¬ IsSquare (mu M) := by
    intro hsq
    obtain ⟨u, w, s, huw, hs, hs4, hsc, hfx⟩ := stable_of_isSquare h2 M σ hσ2 hMa' hsq
    apply hfix _ (fr.mem' _ ⟨u, w, huw, rfl⟩) (fr.ψ s) (Subgroup.mem_map_of_mem _ hs)
    · rw [← map_mul, ← map_mul, ← map_mul, show s * s * s * s = s * s * (s * s) by group, hs4,
        map_one]
    · intro h1
      rw [← map_mul, ← MonoidHom.mem_ker, fr.ker] at h1
      exact hsc (C25W.Sp.scalar_of_mem_spScalars h1)
    · rw [hβM, hfx]
  have hmu : mu M * σ (mu M) = a * a := by
    rw [← mu_mul_gspFieldMap]
    exact mu_eq_of_gm_eq _ hMa
  have hσ1 : ∀ x, σ x = x := by
    by_contra h
    push Not at h
    exact hns (isSquare_of_mul_ringEquiv hp σ hσ2 h (Units.ne_zero _) (map_scalar_eq hσ2 ha hMa')
      hmu)
  have hmap : (gm M).map σ = gm M := by
    ext i j
    simp [Matrix.map_apply, hσ1]
  rw [hmap] at hMa'
  rw [hσ1] at hmu
  refine ⟨M, fun x => by rw [hβM, fieldSp_of_forall_eq hσ1], hns, ?_⟩
  have h3 : (a - mu M) * (a + mu M) = 0 := by linear_combination -hmu
  rcases mul_eq_zero.mp h3 with h | h
  · left
    rw [hMa', show a = mu M by linear_combination h]
  · right
    rw [hMa', show a = -mu M by linear_combination h]

end Frame

end CFSG.ClassicalInvolution.Asc77.C5O.M

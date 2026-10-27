module

public import CFSG.ClassicalInvolution.Asc77.AscC5OM29

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

section Blocks

theorem exists_gl_blocks (M : gsp 2 F) (hM : IsBD (gm M)) :
    ∃ g : Fin 2 → GL (Fin 2) F, gm M = bd (fun k => (g k : Matrix (Fin 2) (Fin 2) F)) ∧
      ∀ k, ((g k : Matrix (Fin 2) (Fin 2) F)).det = mu M := by
  have hgm : gm M = bd (fun k => stdBlock k (gm M)) := (bd_stdBlock hM).symm
  have hdet : ∀ k, (stdBlock k (gm M)).det = mu M := det_eq_mu_of_gm_eq_bd M hgm
  have hne : ∀ k, (stdBlock k (gm M)).det ≠ 0 := fun k => by
    rw [hdet k]
    exact Units.ne_zero _
  exact ⟨fun k => Matrix.GeneralLinearGroup.mkOfDetNeZero _ (hne k), hgm, hdet⟩

@[expose] def slSemi (g : GL (Fin 2) F) (σ : F ≃+* F) (b : SL(2, F)) : SL(2, F) :=
  ⟨(g : Matrix (Fin 2) (Fin 2) F) * (b : Matrix (Fin 2) (Fin 2) F).map σ *
    ((g⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F), by
    have hb : ((b : Matrix (Fin 2) (Fin 2) F).map σ).det = 1 := by
      have h := (RingHom.map_det (σ : F →+* F) (b : Matrix (Fin 2) (Fin 2) F)).symm
      rw [b.2, map_one] at h
      exact h
    rw [Matrix.det_mul, Matrix.det_mul, hb, mul_one, ← Matrix.det_mul, ← Units.val_mul,
      mul_inv_cancel, Units.val_one, Matrix.det_one]⟩

theorem slg_slSemi (g : GL (Fin 2) F) (σ : F ≃+* F) (b : SL(2, F)) :
    Matrix.SpecialLinearGroup.toGL (slSemi g σ b) =
      g * glm σ (Matrix.SpecialLinearGroup.toGL b) * g⁻¹ :=
  Units.ext rfl

theorem conjSp_fieldSp_longBlock_gl (M : gsp 2 F) {g : Fin 2 → GL (Fin 2) F}
    (hM : gm M = bd (fun k => (g k : Matrix (Fin 2) (Fin 2) F))) (σ : F ≃+* F) (k : Fin 2)
    (b : SL(2, F)) :
    conjSp 2 F M (fieldSp 2 F σ (longBlock F 2 k b)) = longBlock F 2 k (slSemi (g k) σ b) :=
  conjSp_fieldSp_longBlock M hM σ k b _ (by
    change _ * _ * ((g k)⁻¹ : GL (Fin 2) F).val = _
    rw [Matrix.coe_units_inv])

theorem comm_conjSp_fieldSp_gen [Finite F] (M N N' : gsp 2 F) (σ τ : F ≃+* F) :
    conjSp 2 F M * fieldSp 2 F σ * (conjSp 2 F N * fieldSp 2 F τ) *
        (conjSp 2 F M * fieldSp 2 F σ)⁻¹ * (conjSp 2 F N' * fieldSp 2 F τ)⁻¹ =
      conjSp 2 F (M * gspFieldMap σ N * gspFieldMap τ M⁻¹ * N'⁻¹) := by
  have h1 := fieldSp_mul_conjSp' σ N
  have h2 := fieldSp_mul_conjSp' τ M⁻¹
  have h3 := fieldSp_comm (F := F) σ τ
  calc conjSp 2 F M * fieldSp 2 F σ * (conjSp 2 F N * fieldSp 2 F τ) *
        (conjSp 2 F M * fieldSp 2 F σ)⁻¹ * (conjSp 2 F N' * fieldSp 2 F τ)⁻¹ =
      conjSp 2 F M * (fieldSp 2 F σ * conjSp 2 F N) * fieldSp 2 F τ * (fieldSp 2 F σ)⁻¹ *
        conjSp 2 F M⁻¹ * (fieldSp 2 F τ)⁻¹ * conjSp 2 F N'⁻¹ := by
        simp only [mul_inv_rev, map_inv]
        group
    _ = conjSp 2 F M * conjSp 2 F (gspFieldMap σ N) * (fieldSp 2 F σ * fieldSp 2 F τ) *
        (fieldSp 2 F σ)⁻¹ * conjSp 2 F M⁻¹ * (fieldSp 2 F τ)⁻¹ * conjSp 2 F N'⁻¹ := by
        rw [h1]
        group
    _ = conjSp 2 F M * conjSp 2 F (gspFieldMap σ N) * (fieldSp 2 F τ * conjSp 2 F M⁻¹) *
        (fieldSp 2 F τ)⁻¹ * conjSp 2 F N'⁻¹ := by
        rw [h3]
        group
    _ = conjSp 2 F (M * gspFieldMap σ N * gspFieldMap τ M⁻¹ * N'⁻¹) := by
        rw [h2, map_mul, map_mul, map_mul]
        group

theorem gm_bd_inv {M : gsp 2 F} {g : Fin 2 → GL (Fin 2) F}
    (hM : gm M = bd (fun k => (g k : Matrix (Fin 2) (Fin 2) F))) :
    gm M⁻¹ = bd (fun k => ((g k)⁻¹ : GL (Fin 2) F).val) := by
  rw [gm_inv, hM, bd_inv (fun k => (Matrix.isUnits_det_units (g k)).ne_zero)]
  congr 1
  funext k
  rw [Matrix.coe_units_inv]

theorem gm_comm_bd (M N N' : gsp 2 F) (σ τ : F ≃+* F) {a b b' : Fin 2 → GL (Fin 2) F}
    (hM : gm M = bd (fun k => (a k : Matrix (Fin 2) (Fin 2) F)))
    (hN : gm N = bd (fun k => (b k : Matrix (Fin 2) (Fin 2) F)))
    (hN' : gm N' = bd (fun k => (b' k : Matrix (Fin 2) (Fin 2) F))) :
    gm (M * gspFieldMap σ N * gspFieldMap τ M⁻¹ * N'⁻¹) =
      bd (fun k => ((a k * glm σ (b k) * glm τ (a k)⁻¹ * (b' k)⁻¹ : GL (Fin 2) F) :
        Matrix (Fin 2) (Fin 2) F)) := by
  rw [gm_mul, gm_mul, gm_mul, gm_gspFieldMap, gm_gspFieldMap, gm_bd_inv hM, gm_bd_inv hN', hM,
    hN, bd_map, bd_map, bd_mul, bd_mul, bd_mul]
  rfl

end Blocks

section Rel

variable {Y₁ : Type} [Group Y₁] {Φ₁ : Set (Subgroup Y₁)} {A₁ A₁' : Subgroup Y₁} {z₁ : Y₁}
  {Y₂ : Type} [Group Y₂] {Φ₂ : Set (Subgroup Y₂)} {A₂ A₂' : Subgroup Y₂} {z₂ : Y₂}
  {M : Type} [Group M]

theorem slg_inv_apply {θ : MulAut SL(2, F)} {d : GL (Fin 2) F}
    (hθ : ∀ b, Matrix.SpecialLinearGroup.toGL (θ b) =
      d * Matrix.SpecialLinearGroup.toGL b * d⁻¹) (c : SL(2, F)) :
    Matrix.SpecialLinearGroup.toGL (θ⁻¹ c) = d⁻¹ * Matrix.SpecialLinearGroup.toGL c * d := by
  have h := hθ (θ⁻¹ c)
  rw [show θ (θ⁻¹ c) = c from by simp] at h
  rw [h]
  group

theorem fix_block_rel (h2 : (2 : F) ≠ 0) (fr₁ : Frame F Y₁ Φ₁ A₁ A₁' z₁)
    (fr₂ : Frame F Y₂ Φ₂ A₂ A₂' z₂) (π₁ : M →* Y₁) (π₂ : M →* Y₂) (θ : MulAut SL(2, F))
    (d : GL (Fin 2) F) (k : Fin 2)
    (hθ : ∀ b, Matrix.SpecialLinearGroup.toGL (θ b) =
      d * Matrix.SpecialLinearGroup.toGL b * d⁻¹)
    (hrel : ∀ (m : M) (b : SL(2, F)), π₁ m = fr₁.ψ (longBlock F 2 k b) →
      π₂ m = fr₂.ψ (longBlock F 2 k (θ b)))
    (hsurj : ∀ b : SL(2, F), ∃ m : M, π₁ m = fr₁.ψ (longBlock F 2 k b))
    (γ₁ : Y₁ ≃* Y₁) (γ₂ : Y₂ ≃* Y₂) (G₁ G₂ : gsp 2 F) (σ₁ σ₂ : F ≃+* F)
    (hG₁ : ∀ x, γ₁ (fr₁.ψ x) = fr₁.ψ (conjSp 2 F G₁ (fieldSp 2 F σ₁ x)))
    (hG₂ : ∀ x, γ₂ (fr₂.ψ x) = fr₂.ψ (conjSp 2 F G₂ (fieldSp 2 F σ₂ x)))
    {g₁ g₂ : Fin 2 → GL (Fin 2) F}
    (hg₁ : gm G₁ = bd (fun k => (g₁ k : Matrix (Fin 2) (Fin 2) F)))
    (hg₂ : gm G₂ = bd (fun k => (g₂ k : Matrix (Fin 2) (Fin 2) F)))
    (hγ : ∀ m : M, ∃ m' : M, π₁ m' = γ₁ (π₁ m) ∧ π₂ m' = γ₂ (π₂ m)) :
    σ₁ = σ₂ ∧ ∃ ℓ : Fˣ, g₂ k * glm σ₂ d = scl ℓ * (d * g₁ k) := by
  have key : ∀ b, θ (slSemi (g₁ k) σ₁ b) = slSemi (g₂ k) σ₂ (θ b) := fun b => by
    obtain ⟨m, hm⟩ := hsurj b
    obtain ⟨m', e1, e2⟩ := hγ m
    rw [hm, hG₁, conjSp_fieldSp_longBlock_gl G₁ hg₁] at e1
    rw [hrel m b hm, hG₂, conjSp_fieldSp_longBlock_gl G₂ hg₂, hrel m' _ e1] at e2
    exact injective_ψ_longBlock fr₂ h2 k e2
  refine semilinear_unique (d * g₁ k) (g₂ k * glm σ₂ d) σ₁ σ₂ fun b => ?_
  have e := congrArg Matrix.SpecialLinearGroup.toGL (key b)
  rw [hθ, slg_slSemi, slg_slSemi, hθ] at e
  simp only [map_mul, map_inv] at e
  convert e using 1 <;> group

theorem swap_block_rel (h2 : (2 : F) ≠ 0) (fr₁ : Frame F Y₁ Φ₁ A₁ A₁' z₁)
    (fr₂ : Frame F Y₂ Φ₂ A₂ A₂' z₂) (π₁ : M →* Y₁) (π₂ : M →* Y₂) (hker : π₁.ker = π₂.ker)
    (θ : MulAut SL(2, F)) (d : GL (Fin 2) F) (k : Fin 2)
    (hθ : ∀ b, Matrix.SpecialLinearGroup.toGL (θ b) =
      d * Matrix.SpecialLinearGroup.toGL b * d⁻¹)
    (hrel : ∀ (m : M) (b : SL(2, F)), π₁ m = fr₁.ψ (longBlock F 2 k b) →
      π₂ m = fr₂.ψ (longBlock F 2 k (θ b)))
    (hsurj : ∀ b : SL(2, F), ∃ m : M, π₁ m = fr₁.ψ (longBlock F 2 k b))
    (ψ : Y₁ ≃* Y₂) (ψ' : Y₂ ≃* Y₁) (P P' : gsp 2 F) (π π' : F ≃+* F)
    (hP : ∀ x, ψ (fr₁.ψ x) = fr₂.ψ (conjSp 2 F P (fieldSp 2 F π x)))
    (hP' : ∀ x, ψ' (fr₂.ψ x) = fr₁.ψ (conjSp 2 F P' (fieldSp 2 F π' x)))
    {p p' : Fin 2 → GL (Fin 2) F}
    (hp : gm P = bd (fun k => (p k : Matrix (Fin 2) (Fin 2) F)))
    (hp' : gm P' = bd (fun k => (p' k : Matrix (Fin 2) (Fin 2) F)))
    (hψ : ∀ m : M, ∃ m' : M, π₂ m' = ψ (π₁ m) ∧ π₁ m' = ψ' (π₂ m)) :
    π' = π ∧ ∃ lam : Fˣ, p' k * glm π d = scl lam * (d⁻¹ * p k) := by
  have hrel' : ∀ (m : M) (c : SL(2, F)), π₂ m = fr₂.ψ (longBlock F 2 k c) →
      π₁ m = fr₁.ψ (longBlock F 2 k (θ⁻¹ c)) := fun m c hm => by
    obtain ⟨m₀, hm₀⟩ := hsurj (θ⁻¹ c)
    have h0 := hrel m₀ _ hm₀
    rw [show θ (θ⁻¹ c) = c from by simp, ← hm] at h0
    have h1 : m₀⁻¹ * m ∈ π₁.ker := by
      rw [hker, MonoidHom.mem_ker, map_mul, map_inv, h0, inv_mul_cancel]
    rw [MonoidHom.mem_ker, map_mul, map_inv, inv_mul_eq_one] at h1
    rw [← h1, hm₀]
  have key : ∀ b, slSemi (p' k) π' (θ b) = θ⁻¹ (slSemi (p k) π b) := fun b => by
    obtain ⟨m, hm⟩ := hsurj b
    obtain ⟨m', e1, e2⟩ := hψ m
    rw [hm, hP, conjSp_fieldSp_longBlock_gl P hp] at e1
    rw [hrel m b hm, hP', conjSp_fieldSp_longBlock_gl P' hp', hrel' m' _ e1] at e2
    exact (injective_ψ_longBlock fr₁ h2 k e2).symm
  obtain ⟨hπ, lam, hlam⟩ :=
    semilinear_unique (p' k * glm π' d) (d⁻¹ * p k) π' π fun b => by
      have e := congrArg Matrix.SpecialLinearGroup.toGL (key b)
      rw [slg_slSemi, hθ, slg_inv_apply hθ, slg_slSemi] at e
      simp only [map_mul, map_inv] at e
      convert e using 1 <;> group
  subst hπ
  refine ⟨rfl, lam⁻¹, ?_⟩
  rw [hlam, ← mul_assoc, ← map_mul, inv_mul_cancel, map_one, one_mul]

end Rel

end CFSG.ClassicalInvolution.Asc77.C5O.M

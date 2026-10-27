module

public import CFSG.ClassicalInvolution.ModelFacts.Orth15OuterSp4

public section

open CFSG.ClassicalInvolution.ModelFacts.Orth15.OuterSp4
open CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher
open CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag
open CFSG.Assembly.LowTwoRank
open scoped Matrix
open CFSG.ClassicalInvolution.Models.SymplecticPairs
open CFSG.ClassicalInvolution.ModelFacts.Orth15.ChainU (eq_of_central_ratio)
open CFSG.LieType.Universal.Symplectic.SpExtras (mat mat_apply mat_elt_positiveLong
  mat_elt_negativeLong)
open CFSG.LieType.Steinberg (sl2Upper sl2Lower)

namespace CFSG.ClassicalInvolution.Asc77.C25W.Sp

variable {F : Type} [Field F]

theorem multiplier_gspFieldMap (σ : F ≃+* F) (A : gsp 2 F) :
    ((multiplier 2 F (gspFieldMap σ A) : Fˣ) : F) = σ ((multiplier 2 F A : Fˣ) : F) := by
  have hμ := multiplier_spec A
  set Am : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F :=
    ((A : GL (Fin 2 ⊕ Fin 2) F) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) with hAm
  have h := multiplier_eq (gspFieldMap σ A)
    (μ := Units.map σ.toRingHom.toMonoidHom (multiplier 2 F A)) (by
      change (Am.map σ)ᵀ * formJ 2 F * Am.map σ = σ ((multiplier 2 F A : Fˣ) : F) • formJ 2 F
      have h1 : (Amᵀ * formJ 2 F * Am).map σ = (Am.map σ)ᵀ * formJ 2 F * Am.map σ := by
        rw [map_mul_ringEquiv, map_mul_ringEquiv, Matrix.transpose_map, formJ_map]
      rw [← h1, hμ]
      ext i j
      have h := congrFun (congrFun (formJ_map (r := 2) σ) i) j
      simp only [Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, map_mul] at h ⊢
      rw [h])
  rw [h]
  rfl


theorem ringChar_ne_two_of_two_ne_zero (h2 : (2 : F) ≠ 0) : ringChar F ≠ 2 := by
  intro h
  have h3 : ((2 : ℕ) : F) = 0 := (ringChar.spec F 2).mpr (by rw [h])
  exact h2 (by simpa using h3)

theorem isSquare_mul_map [Finite F] (h2 : (2 : F) ≠ 0) (ρ : F ≃+* F) (m : F) (hm : m ≠ 0) :
    IsSquare (m * ρ m) := by
  have := Fintype.ofFinite F
  have hodd := ringChar_ne_two_of_two_ne_zero h2
  have hρm : ρ m ≠ 0 := (map_ne_zero ρ).2 hm
  rw [FiniteField.isSquare_iff hodd (mul_ne_zero hm hρm), mul_pow]
  have hq : Fintype.card F % 2 = 1 := FiniteField.odd_card_of_char_ne_two hodd
  have hχ : (m ^ (Fintype.card F / 2)) * (m ^ (Fintype.card F / 2)) = 1 := by
    rw [← pow_add, ← two_mul]
    have : 2 * (Fintype.card F / 2) = Fintype.card F - 1 := by omega
    rw [this]
    exact FiniteField.pow_card_sub_one_eq_one m hm
  have hρχ : ρ m ^ (Fintype.card F / 2) = m ^ (Fintype.card F / 2) := by
    rw [← map_pow]
    rcases mul_self_eq_one_iff.1 hχ with h | h
    · rw [h, map_one]
    · rw [h, map_neg, map_one]
  rw [hρχ]
  exact hχ


theorem fix_of_trivial [Finite F] (h4 : 4 ≤ Nat.card F) (M : gsp 2 F) (ρ : F ≃+* F)
    (h : conjAut 2 F M * fieldAut 2 F ρ = 1) :
    ∀ g : StatedSp 2 F, conjSp 2 F M (fieldSp 2 F ρ g) = g := by
  set α : MulAut (StatedSp 2 F) := conjSp 2 F M * fieldSp 2 F ρ with hα
  have hαproj : ∀ g, proj 2 F (α g) = proj 2 F g := by
    intro g
    have h1 := congrArg (fun γ : MulAut (StatedProj (StatedSp 2 F)) => γ (proj 2 F g)) h
    have e : α g = conjSp 2 F M (fieldSp 2 F ρ g) := rfl
    rw [e]
    simpa [MulAut.mul_apply, fieldAut_proj, conjAut_proj] using h1
  have hperf : Group.IsPerfect (StatedSp 2 F) :=
    (CFSG.LieType.Universal.Symplectic.isQuasisimple (n := 2) (F := F) (by norm_num)
      (Or.inl (Or.inr h4))).1
  have : Group.IsPerfect (MonoidHom.id (StatedSp 2 F)).range := Group.IsPerfect.range _
  have key := eq_of_central_ratio (MonoidHom.id (StatedSp 2 F)).range α.toMonoidHom (fun r _ => by
    rw [CFSG.LieType.Universal.Symplectic.center_eq 2 F]
    change α r * r⁻¹ ∈ spScalars 2 F
    rw [← ker_proj, MonoidHom.mem_ker, map_mul, map_inv, hαproj, mul_inv_cancel])
  intro g
  exact key g ⟨g, rfl⟩


theorem shape_of_trivial [Finite F] (h4 : 4 ≤ Nat.card F) (M : gsp 2 F) (ρ : F ≃+* F)
    (h : conjAut 2 F M * fieldAut 2 F ρ = 1) :
    ρ = 1 ∧ ∃ a : F, a ≠ 0 ∧
      ((M : GL (Fin 2 ⊕ Fin 2) F) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) = a • 1 := by
  have hfix := fix_of_trivial h4 M ρ h
  have hu : ∀ (k : Fin 2) (t : F),
      ((M : GL (Fin 2 ⊕ Fin 2) F) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) *
          Matrix.transvection (Sum.inl k) (Sum.inr k) (ρ t) =
        Matrix.transvection (Sum.inl k) (Sum.inr k) t *
          ((M : GL (Fin 2 ⊕ Fin 2) F) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) := by
    intro k t
    have := rel_of_fixed M ρ _ (hfix (longBlock F 2 k (sl2Upper t)))
    rwa [longBlock_sl2Upper, mat_elt_positiveLong, map_transvection] at this
  have hl : ∀ (k : Fin 2) (t : F),
      ((M : GL (Fin 2 ⊕ Fin 2) F) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) *
          Matrix.transvection (Sum.inr k) (Sum.inl k) (ρ t) =
        Matrix.transvection (Sum.inr k) (Sum.inl k) t *
          ((M : GL (Fin 2 ⊕ Fin 2) F) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) := by
    intro k t
    have := rel_of_fixed M ρ _ (hfix (longBlock F 2 k (sl2Lower t)))
    rwa [longBlock_sl2Lower, mat_elt_negativeLong, map_transvection] at this
  have hdet : ((M : GL (Fin 2 ⊕ Fin 2) F) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F).det ≠ 0 :=
    ((Matrix.isUnit_iff_isUnit_det _).mp (M : GL (Fin 2 ⊕ Fin 2) F).isUnit).ne_zero
  obtain ⟨hσ, a, b, ha, hb, hMab⟩ := sp4_shape ρ _ hdet hu hl
  refine ⟨hσ, a, ha, ?_⟩
  have hij : (0 : Fin 2) ≠ 1 := by decide
  set g : StatedSp 2 F :=
    CFSG.LieType.Universal.Symplectic.equivStatedSp 2 F
      (TauCeti.GLSymplecticFin.leviHom (TauCeti.transvectionUnit hij (1 : F))) with hg
  have hrel := rel_of_fixed M ρ g (hfix g)
  have hmat : mat 2 F g = Matrix.fromBlocks (Matrix.transvection (0 : Fin 2) 1 (1 : F)) 0 0
      (((TauCeti.transvectionUnit hij (1 : F))⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F)ᵀ := by
    rw [hg, CFSG.LieType.Universal.Symplectic.SpExtras.mat_equiv_leviHom,
      TauCeti.coe_transvectionUnit]
  subst hσ
  rw [hMab, hmat] at hrel
  have e := congrFun (congrFun hrel (Sum.inl 0)) (Sum.inl 1)
  simp [Matrix.mul_apply, Matrix.diagonal_apply, Matrix.transvection] at e
  subst e
  rw [hMab, Matrix.smul_one_eq_diagonal]
  congr 1
  funext i
  rcases i with i | i <;> fin_cases i <;> rfl


theorem sq_formula (N : gsp 2 F) (τ : F ≃+* F) :
    (conjAut 2 F N * fieldAut 2 F τ) * (conjAut 2 F N * fieldAut 2 F τ) =
      conjAut 2 F (N * gspFieldMap τ N) * fieldAut 2 F (τ.trans τ) := by
  obtain ⟨hcc, hff, hfc, -⟩ := standard_automorphism_transport (r := 2) (K := F)
  rw [← hcc, ← hff, ← hfc τ N]
  group


theorem map_isometry (τ : F ≃+* F) (N₁ : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F)
    (hN : N₁ᵀ * gram F 2 * N₁ = gram F 2) :
    (N₁.map τ)ᵀ * gram F 2 * N₁.map τ = gram F 2 := by
  have hg : (gram F 2).map τ = gram F 2 := formJ_map (r := 2) τ
  have h1 : (N₁ᵀ * gram F 2 * N₁).map τ = (N₁.map τ)ᵀ * (gram F 2).map τ * N₁.map τ := by
    rw [map_mul_ringEquiv, map_mul_ringEquiv, Matrix.transpose_map]
  calc (N₁.map τ)ᵀ * gram F 2 * N₁.map τ = (N₁.map τ)ᵀ * (gram F 2).map τ * N₁.map τ := by
        rw [hg]
    _ = (N₁ᵀ * gram F 2 * N₁).map τ := h1.symm
    _ = (gram F 2).map τ := by rw [hN]
    _ = gram F 2 := hg

theorem normal_form_sq [Finite F] (h2 : (2 : F) ≠ 0) (h4 : 4 ≤ Nat.card F)
    (β : MulAut (StatedProj (StatedSp 2 F))) (hβ : β * β * (β * β) = 1) :
    ∃ (Nl : gsp 2 F) (τ : F ≃+* F) (l c' : F) (N₁ : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F),
      (∀ x, τ (τ x) = x) ∧ l ≠ 0 ∧
      ((Nl : GL (Fin 2 ⊕ Fin 2) F) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) = l • N₁ ∧
      N₁ᵀ * gram F 2 * N₁ = gram F 2 ∧ c' * c' = 1 ∧ N₁ * N₁.map τ = c' • 1 ∧
      β * β = conjAut 2 F Nl * fieldAut 2 F τ := by
  obtain ⟨A, σ, hAσ⟩ := exists_conjAut_fieldAut_sp4 h2 β
  have hsq : β * β = conjAut 2 F (A * gspFieldMap σ A) * fieldAut 2 F (σ.trans σ) := by
    rw [hAσ]; exact sq_formula A σ
  set N : gsp 2 F := A * gspFieldMap σ A with hN
  set τ : F ≃+* F := σ.trans σ with hτ
  have h4' : (conjAut 2 F N * fieldAut 2 F τ) * (conjAut 2 F N * fieldAut 2 F τ) = _ := rfl
  have hone : conjAut 2 F (N * gspFieldMap τ N) * fieldAut 2 F (τ.trans τ) = 1 := by
    rw [← sq_formula N τ, ← hsq]; exact hβ
  obtain ⟨hττ, a, ha, hMa⟩ := shape_of_trivial h4 (N * gspFieldMap τ N) (τ.trans τ) hone
  have hττ' : ∀ x, τ (τ x) = x := fun x => by
    have := RingEquiv.congr_fun hττ x
    simpa using this
  have hmul : ((multiplier 2 F N : Fˣ) : F) =
      ((multiplier 2 F A : Fˣ) : F) * σ ((multiplier 2 F A : Fˣ) : F) := by
    rw [hN, map_mul, Units.val_mul, multiplier_gspFieldMap]
  obtain ⟨l, hl⟩ := isSquare_mul_map h2 σ ((multiplier 2 F A : Fˣ) : F) (Units.ne_zero _)
  have hl0 : l ≠ 0 := by
    rintro rfl
    exact Units.ne_zero (multiplier 2 F N) (by rw [hmul, hl]; ring)
  set Nm : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F :=
    ((N : GL (Fin 2 ⊕ Fin 2) F) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) with hNm
  have hNspec : Nmᵀ * gram F 2 * Nm = (l * l) • gram F 2 := by
    have := multiplier_spec N
    rw [hmul, hl] at this
    exact this
  set N₁ : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F := l⁻¹ • Nm with hN₁
  have hN₁iso : N₁ᵀ * gram F 2 * N₁ = gram F 2 := by
    rw [hN₁]
    simp only [Matrix.transpose_smul, Matrix.smul_mul, Matrix.mul_smul, smul_smul]
    rw [hNspec, smul_smul]
    have : l⁻¹ * l⁻¹ * (l * l) = 1 := by field_simp
    rw [this, one_smul]
  have hMm : Nm * Nm.map τ = a • 1 := by
    have := hMa
    rw [Subgroup.coe_mul, Units.val_mul] at this
    exact this
  have hmapN₁ : N₁.map τ = τ l⁻¹ • Nm.map τ := by
    ext i j; simp [hN₁, Matrix.map_apply]
  have hNN : N₁ * N₁.map τ = (l⁻¹ * τ l⁻¹ * a) • 1 := by
    rw [hmapN₁, hN₁, Matrix.smul_mul, Matrix.mul_smul, hMm, smul_smul, smul_smul]
  have hc'1 : (l⁻¹ * τ l⁻¹ * a) * (l⁻¹ * τ l⁻¹ * a) = 1 := by
    have hiso' := map_isometry τ N₁ hN₁iso
    have h1 : (N₁ * N₁.map τ)ᵀ * gram F 2 * (N₁ * N₁.map τ) = gram F 2 := by
      calc (N₁ * N₁.map τ)ᵀ * gram F 2 * (N₁ * N₁.map τ) =
          (N₁.map τ)ᵀ * (N₁ᵀ * gram F 2 * N₁) * N₁.map τ := by
            simp only [Matrix.transpose_mul, Matrix.mul_assoc]
        _ = gram F 2 := by rw [hN₁iso]; exact hiso'
    rw [hNN] at h1
    have e := congrFun (congrFun h1 (Sum.inl 0)) (Sum.inr 0)
    simp [Matrix.transpose_smul, gram, Matrix.fromBlocks] at e
    simpa using e
  refine ⟨N, τ, l, l⁻¹ * τ l⁻¹ * a, N₁, hττ', hl0, ?_, hN₁iso, hc'1, hNN, hsq⟩
  rw [hN₁, smul_inv_smul₀ hl0]

end CFSG.ClassicalInvolution.Asc77.C25W.Sp

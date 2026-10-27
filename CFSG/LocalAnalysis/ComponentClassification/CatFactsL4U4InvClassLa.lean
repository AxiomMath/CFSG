module

public import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4TFrameL
public import CFSG.LocalAnalysis.ComponentInitial.LinearInvolutionFixedInner

public section

namespace CFSG.ComponentClassification.CatFactsL4U4

namespace InvClassL

open Matrix Module TBlocks HBlocks CFSG.LocalAnalysis.ComponentInitial

variable {F : Type} [Field F]

@[expose] def stdN (c : F) : Matrix (Fin 4) (Fin 4) F :=
  !![0, c, 0, 0; 1, 0, 0, 0; 0, 0, 0, c; 0, 0, 1, 0]

theorem stdN_mul_stdN (c : F) : stdN c * stdN c = c • 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [stdN, Matrix.mul_apply, Fin.sum_univ_four]

theorem det_stdN (c : F) : (stdN c).det = c ^ 2 := by
  rw [stdN, Matrix.det_succ_row_zero]
  simp [Fin.sum_univ_succ, Matrix.det_succ_row_zero, Matrix.submatrix, Fin.succAbove]
  ring

theorem sq_sub_mul_ne_zero {c : F} (hc : ¬ IsSquare c) {a b : F} (hab : a ≠ 0 ∨ b ≠ 0) :
    a ^ 2 - b ^ 2 * c ≠ 0 := by
  intro h0
  rcases eq_or_ne b 0 with hb | hb
  · rw [hb] at h0
    have : a = 0 := by simpa using h0
    rcases hab with ha | hb' <;> contradiction
  · apply hc
    refine ⟨a / b, ?_⟩
    field_simp
    linear_combination -h0

theorem eq_zero_of_smul_add_mulVec_eq_zero {c : F} (hc : ¬ IsSquare c)
    {X : Matrix (Fin 4) (Fin 4) F} (hX : X * X = c • 1) {a b : F} {v : Fin 4 → F}
    (hv : a • v + b • (X *ᵥ v) = 0) (hab : a ≠ 0 ∨ b ≠ 0) : v = 0 := by
  have hsum := sq_sub_mul_ne_zero hc hab
  have hXX : ∀ w : Fin 4 → F, X *ᵥ (X *ᵥ w) = c • w := by
    intro w
    rw [Matrix.mulVec_mulVec, hX, Matrix.smul_mulVec, Matrix.one_mulVec]
  have h1 : a • (a • v + b • (X *ᵥ v)) - b • (X *ᵥ (a • v + b • (X *ᵥ v))) =
      (a ^ 2 - b ^ 2 * c) • v := by
    rw [Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_smul, hXX]
    ext i
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    ring
  rw [hv, Matrix.mulVec_zero, smul_zero, smul_zero, sub_zero] at h1
  exact (smul_eq_zero.1 h1.symm).resolve_left hsum

theorem exists_mul_eq_mul_stdN {c : F} (hc : ¬ IsSquare c) {X : Matrix (Fin 4) (Fin 4) F}
    (hX : X * X = c • 1) : ∃ P : Matrix (Fin 4) (Fin 4) F, IsUnit P.det ∧ X * P = P * stdN c := by
  classical
  have hXX : ∀ w : Fin 4 → F, X *ᵥ (X *ᵥ w) = c • w := by
    intro w
    rw [Matrix.mulVec_mulVec, hX, Matrix.smul_mulVec, Matrix.one_mulVec]
  set v₁ : Fin 4 → F := Pi.single 0 1 with hv₁
  have hv₁0 : v₁ ≠ 0 := by
    intro h
    have := congrFun h 0
    simp [hv₁] at this
  set W : Submodule F (Fin 4 → F) := Submodule.span F (Set.range ![v₁, X *ᵥ v₁]) with hW
  have hv₁W : v₁ ∈ W := Submodule.subset_span ⟨0, rfl⟩
  have hXv₁W : X *ᵥ v₁ ∈ W := Submodule.subset_span ⟨1, rfl⟩
  obtain ⟨i₀, hi₀⟩ : ∃ i : Fin 4, Pi.single i (1 : F) ∉ W := by
    by_contra hall
    push Not at hall
    have htop : W = ⊤ := by
      rw [eq_top_iff, ← (Pi.basisFun F (Fin 4)).span_eq, Submodule.span_le]
      rintro _ ⟨i, rfl⟩
      simpa using hall i
    have h1 : Module.finrank F W ≤ 2 := by
      rw [hW]
      exact (finrank_range_le_card (R := F) ![v₁, X *ᵥ v₁]).trans (by simp)
    rw [htop, finrank_top, Module.finrank_fin_fun] at h1
    omega
  set v₂ : Fin 4 → F := Pi.single i₀ 1 with hv₂
  set col : Fin 4 → Fin 4 → F := ![v₁, X *ᵥ v₁, v₂, X *ᵥ v₂] with hcol
  set P : Matrix (Fin 4) (Fin 4) F := Matrix.of fun i j => col j i with hP
  refine ⟨P, ?_, ?_⟩
  · rw [← Matrix.isUnit_iff_isUnit_det, ← Matrix.linearIndependent_cols_iff_isUnit]
    rw [Fintype.linearIndependent_iff]
    intro g hg
    have hg' : g 0 • v₁ + g 1 • (X *ᵥ v₁) + (g 2 • v₂ + g 3 • (X *ᵥ v₂)) = 0 := by
      rw [← hg]
      ext i
      simp [Fin.sum_univ_four, hP, hcol]
      ring
    have hWX : ∀ w ∈ W, X *ᵥ w ∈ W := by
      intro w hw
      rw [hW] at hw ⊢
      refine Submodule.span_induction ?_ ?_ ?_ ?_ hw
      · rintro x ⟨j, rfl⟩
        fin_cases j
        · exact Submodule.subset_span ⟨1, rfl⟩
        · change X *ᵥ (X *ᵥ v₁) ∈ _
          rw [hXX]
          exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨0, rfl⟩)
      · rw [Matrix.mulVec_zero]
        exact Submodule.zero_mem _
      · intro x y _ _ hx hy
        rw [Matrix.mulVec_add]
        exact Submodule.add_mem _ hx hy
      · intro a x _ hx
        rw [Matrix.mulVec_smul]
        exact Submodule.smul_mem _ a hx
    have hmem1 : g 0 • v₁ + g 1 • (X *ᵥ v₁) ∈ W :=
      Submodule.add_mem _ (Submodule.smul_mem _ _ hv₁W) (Submodule.smul_mem _ _ hXv₁W)
    have h23 : g 2 = 0 ∧ g 3 = 0 := by
      by_contra hne
      have hne' : g 2 ≠ 0 ∨ g 3 ≠ 0 := by tauto
      have hu : g 2 • v₂ + g 3 • (X *ᵥ v₂) ∈ W := by
        have : g 2 • v₂ + g 3 • (X *ᵥ v₂) = -(g 0 • v₁ + g 1 • (X *ᵥ v₁)) := by
          rw [eq_neg_iff_add_eq_zero, add_comm]
          exact hg'
        rw [this]
        exact Submodule.neg_mem _ hmem1
      have hsum : g 2 ^ 2 - g 3 ^ 2 * c ≠ 0 := sq_sub_mul_ne_zero hc hne'
      have hv₂W : v₂ ∈ W := by
        have h1 : g 2 • (g 2 • v₂ + g 3 • (X *ᵥ v₂)) -
            g 3 • (X *ᵥ (g 2 • v₂ + g 3 • (X *ᵥ v₂))) = (g 2 ^ 2 - g 3 ^ 2 * c) • v₂ := by
          rw [Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_smul, hXX]
          ext i
          simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
          ring
        have h2 : (g 2 ^ 2 - g 3 ^ 2 * c) • v₂ ∈ W := by
          rw [← h1]
          exact Submodule.sub_mem _ (Submodule.smul_mem _ _ hu)
            (Submodule.smul_mem _ _ (hWX _ hu))
        have := Submodule.smul_mem W (g 2 ^ 2 - g 3 ^ 2 * c)⁻¹ h2
        rwa [smul_smul, inv_mul_cancel₀ hsum, one_smul] at this
      exact hi₀ hv₂W
    obtain ⟨h2, h3⟩ := h23
    rw [h2, h3, zero_smul, zero_smul, add_zero, add_zero] at hg'
    have h01 : g 0 = 0 ∧ g 1 = 0 := by
      by_contra hne
      have hne' : g 0 ≠ 0 ∨ g 1 ≠ 0 := by tauto
      exact hv₁0 (eq_zero_of_smul_add_mulVec_eq_zero hc hX hg' hne')
    intro i
    fin_cases i
    · exact h01.1
    · exact h01.2
    · exact h2
    · exact h3
  · ext i j
    rw [Matrix.mul_apply, Matrix.mul_apply]
    change (X *ᵥ col j) i = _
    fin_cases j <;> simp [hcol, stdN, Fin.sum_univ_four, hP, hXX, mul_comm]

@[expose] def dOne : Matrix (Fin 4) (Fin 4) F := diagonal fun i => if (i : ℕ) < 3 then 1 else -1

theorem dOne_mul_dOne : (dOne : Matrix (Fin 4) (Fin 4) F) * dOne = 1 := by
  rw [dOne, diagonal_mul_diagonal, ← diagonal_one]
  congr 1
  funext i
  split_ifs <;> simp

theorem exists_frame_of_finrank_three (hK : ringChar F ≠ 2) {Y : Matrix (Fin 4) (Fin 4) F}
    (hY : Y * Y = 1) (h3 : Module.finrank F (LinearMap.ker (toLin' Y - 1)) = 3) :
    ∃ P : GL (Fin 4) F,
      Y * (P : Matrix (Fin 4) (Fin 4) F) = (P : Matrix (Fin 4) (Fin 4) F) * dOne := by
  obtain ⟨b, hb⟩ := LinearFlag.exists_eigenbasis hK hY
  obtain ⟨P, D, hPD, hD⟩ := LinearFlag.exists_gl_inv_mul_mul_eq_toMatrix b ⟨Y, Y, hY, hY⟩
  have hDd : (D : Matrix (Fin 4) (Fin 4) F) = dOne := by
    rw [hD, dOne]
    ext a c
    rw [LinearMap.toMatrix_apply, toLin'_apply, hb c, h3, map_smul, Basis.repr_self,
      Finsupp.smul_apply, Finsupp.single_apply, diagonal_apply]
    by_cases hac : a = c
    · subst hac
      simp
    · simp [hac, Ne.symm hac]
  refine ⟨P, ?_⟩
  have h1 : (⟨Y, Y, hY, hY⟩ : GL (Fin 4) F) * P = P * D := by
    rw [← hPD, ← mul_assoc, ← mul_assoc, mul_inv_cancel, one_mul]
  have h2 := congrArg (fun g : GL (Fin 4) F => (g : Matrix (Fin 4) (Fin 4) F)) h1
  simp only [Units.val_mul] at h2
  rw [← hDd]
  exact h2

theorem exists_frame_t1_L4 (hK : ringChar F ≠ 2) {X : Matrix (Fin 4) (Fin 4) F} (hXX : X * X = 1)
    (hdet : X.det = -1) : ∃ P : GL (Fin 4) F, ∃ s : F, (s = 1 ∨ s = -1) ∧
      (s • X) * (P : Matrix (Fin 4) (Fin 4) F) = (P : Matrix (Fin 4) (Fin 4) F) * dOne := by
  have h2 : (2 : F) ≠ 0 := Ring.two_ne_zero hK
  have hc := LinearFlag.isCompl_eigenspaces hK hXX
  have hsum := Submodule.finrank_add_eq_of_isCompl hc
  rw [Module.finrank_fin_fun] at hsum
  have hTp : ∀ v ∈ LinearMap.ker (toLin' X - 1), toLin' X v = (1 : F) • v := fun v hv => by
    rw [LinearMap.mem_ker, LinearMap.sub_apply, Module.End.one_apply, sub_eq_zero] at hv
    rw [one_smul, hv]
  have hTm : ∀ v ∈ LinearMap.ker (toLin' X + 1), toLin' X v = (-1 : F) • v := fun v hv => by
    rw [LinearMap.mem_ker, LinearMap.add_apply, Module.End.one_apply,
      add_eq_zero_iff_eq_neg] at hv
    rw [neg_one_smul, hv]
  have hdetT := det_eq_of_isCompl_smul hc hTp hTm
  rw [LinearMap.det_toLin', hdet, one_pow, one_mul] at hdetT
  have hodd : Odd (Module.finrank F (LinearMap.ker (toLin' X + 1))) := by
    rcases Nat.even_or_odd (Module.finrank F (LinearMap.ker (toLin' X + 1))) with he | ho
    · exfalso
      rw [he.neg_one_pow] at hdetT
      apply h2
      linear_combination -hdetT
    · exact ho
  have hm4 : Module.finrank F (LinearMap.ker (toLin' X + 1)) ≤ 4 := by omega
  rcases (by obtain ⟨k, hk⟩ := hodd; omega :
      Module.finrank F (LinearMap.ker (toLin' X + 1)) = 1 ∨
        Module.finrank F (LinearMap.ker (toLin' X + 1)) = 3) with h1 | h3
  · obtain ⟨P, hP⟩ := exists_frame_of_finrank_three hK hXX (by omega)
    exact ⟨P, 1, Or.inl rfl, by rw [one_smul]; exact hP⟩
  · have hYY : (-X) * (-X) = 1 := by rw [neg_mul_neg, hXX]
    have hker : LinearMap.ker (toLin' (-X) - 1) = LinearMap.ker (toLin' X + 1) := by
      ext v
      simp only [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.add_apply,
        Module.End.one_apply, toLin'_apply, Matrix.neg_mulVec]
      constructor <;> intro h <;> linear_combination -h
    obtain ⟨P, hP⟩ := exists_frame_of_finrank_three hK hYY (by rw [hker, h3])
    exact ⟨P, -1, Or.inr rfl, by rw [neg_one_smul]; exact hP⟩

theorem classify_inv (hK : ringChar F ≠ 2) {X : Matrix (Fin 4) (Fin 4) F} {c : F}
    (hX : X * X = c • 1) (hc0 : c ≠ 0) (hns : ∀ a : F, X ≠ a • 1) :
    (∃ l : F, l ≠ 0 ∧ c = l ^ 2 ∧ (l⁻¹ • X).det = 1 ∧
      ∃ P : GL (Fin 4) F, (l⁻¹ • X) * (P : Matrix (Fin 4) (Fin 4) F) =
        (P : Matrix (Fin 4) (Fin 4) F) * X1 1) ∨
    (∃ l : F, l ≠ 0 ∧ c = l ^ 2 ∧ (l⁻¹ • X).det = -1 ∧
      ∃ P : GL (Fin 4) F, ∃ s : F, (s = 1 ∨ s = -1) ∧
        ((s * l⁻¹) • X) * (P : Matrix (Fin 4) (Fin 4) F) =
          (P : Matrix (Fin 4) (Fin 4) F) * dOne) ∨
    (¬ IsSquare c ∧ ∃ P : GL (Fin 4) F,
      X * (P : Matrix (Fin 4) (Fin 4) F) = (P : Matrix (Fin 4) (Fin 4) F) * stdN c) := by
  have h2 : (2 : F) ≠ 0 := Ring.two_ne_zero hK
  by_cases hsq : IsSquare c
  · obtain ⟨l, hl⟩ := hsq
    have hl0 : l ≠ 0 := by rintro rfl; rw [mul_zero] at hl; exact hc0 hl
    have hc : c = l ^ 2 := by rw [hl, sq]
    set Y := l⁻¹ • X with hYdef
    have hYY : Y * Y = 1 := by
      rw [hYdef, Matrix.smul_mul, Matrix.mul_smul, smul_smul, hX, smul_smul, hc,
        show l⁻¹ * l⁻¹ * l ^ 2 = 1 by field_simp, one_smul]
    have hdet2 : Y.det * Y.det = 1 := by rw [← det_mul, hYY, det_one]
    have hXY : X = l • Y := by rw [hYdef, smul_smul, mul_inv_cancel₀ hl0, one_smul]
    have hY1 : Y ≠ 1 := fun h => hns l (by rw [hXY, h])
    have hYm1 : Y ≠ -1 := fun h => hns (-l) (by rw [hXY, h, smul_neg, neg_smul])
    rcases mul_self_eq_one_iff.mp hdet2 with hd | hd
    · obtain ⟨P, hP⟩ := exists_frame_t2_L4 h2 hYY hd hY1 hYm1
      exact Or.inl ⟨l, hl0, hc, hd, P, hP⟩
    · obtain ⟨P, s, hs, hP⟩ := exists_frame_t1_L4 hK hYY hd
      refine Or.inr (Or.inl ⟨l, hl0, hc, hd, P, s, hs, ?_⟩)
      rw [← smul_smul]
      exact hP
  · obtain ⟨P, hPu, hP⟩ := exists_mul_eq_mul_stdN hsq hX
    exact Or.inr (Or.inr ⟨hsq, Matrix.nonsingInvUnit P hPu, hP⟩)

end InvClassL

end CFSG.ComponentClassification.CatFactsL4U4

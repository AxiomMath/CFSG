module

public import CFSG.LieType.Universal.SpecialLinear

public section

namespace CFSG.SeitzReduction.SymplecticPilot

open Matrix

section Gen

variable {F : Type} [Field F]

noncomputable abbrev tr3 (i j : Fin 3) (h : i ≠ j) (c : F) : SpecialLinearGroup (Fin 3) F :=
  SpecialLinearGroup.transvection h c

theorem coe_tr3 (i j : Fin 3) (h : i ≠ j) (c : F) :
    ((tr3 i j h c : SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) =
      Matrix.of fun a b => (if a = b then 1 else 0) + (if i = a ∧ j = b then c else 0) := by
  ext a b
  simp only [SpecialLinearGroup.transvection_coe, Matrix.add_apply, Matrix.one_apply,
    Matrix.single_apply, Matrix.of_apply]

theorem coe_tr3_02 (c : F) :
    ((tr3 0 2 (by decide) c : SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) =
      !![1, 0, c; 0, 1, 0; 0, 0, 1] := by
  rw [coe_tr3]
  ext a b
  fin_cases a <;> fin_cases b <;> simp

theorem coe_tr3_20 (c : F) :
    ((tr3 2 0 (by decide) c : SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) =
      !![1, 0, 0; 0, 1, 0; c, 0, 1] := by
  rw [coe_tr3]
  ext a b
  fin_cases a <;> fin_cases b <;> simp

theorem coe_tr3_01 (c : F) :
    ((tr3 0 1 (by decide) c : SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) =
      !![1, c, 0; 0, 1, 0; 0, 0, 1] := by
  rw [coe_tr3]
  ext a b
  fin_cases a <;> fin_cases b <;> simp

theorem coe_tr3_12 (c : F) :
    ((tr3 1 2 (by decide) c : SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) =
      !![1, 0, 0; 0, 1, c; 0, 0, 1] := by
  rw [coe_tr3]
  ext a b
  fin_cases a <;> fin_cases b <;> simp

theorem coe_tr3_10 (c : F) :
    ((tr3 1 0 (by decide) c : SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) =
      !![1, 0, 0; c, 1, 0; 0, 0, 1] := by
  rw [coe_tr3]
  ext a b
  fin_cases a <;> fin_cases b <;> simp

theorem coe_tr3_21 (c : F) :
    ((tr3 2 1 (by decide) c : SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) =
      !![1, 0, 0; 0, 1, 0; 0, c, 1] := by
  rw [coe_tr3]
  ext a b
  fin_cases a <;> fin_cases b <;> simp

variable [CharP F 2]

variable (F) in
@[expose] noncomputable def regUnip3 : SpecialLinearGroup (Fin 3) F :=
  tr3 0 1 (by decide) 1 * tr3 1 2 (by decide) 1 * tr3 0 2 (by decide) 1

theorem coe_regUnip3 :
    ((regUnip3 F : SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) =
      !![1, 1, 0; 0, 1, 1; 0, 0, 1] := by
  rw [regUnip3]
  simp only [Matrix.SpecialLinearGroup.coe_mul]
  rw [coe_tr3_01, coe_tr3_12, coe_tr3_02]
  simp only [Matrix.mul_fin_three]
  ext a b
  fin_cases a <;> fin_cases b <;> (simp; try grind)

theorem regUnip3_inv :
    (regUnip3 F)⁻¹ = tr3 0 2 (by decide) 1 * tr3 1 2 (by decide) 1 * tr3 0 1 (by decide) 1 := by
  refine inv_eq_of_mul_eq_one_right (Subtype.ext ?_)
  simp only [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_one]
  rw [coe_regUnip3, coe_tr3_02, coe_tr3_12, coe_tr3_01]
  simp only [Matrix.mul_fin_three]
  ext a b
  fin_cases a <;> fin_cases b <;> simp <;> grind

theorem coe_regUnip3_inv :
    (((regUnip3 F)⁻¹ : SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) =
      !![1, 1, 1; 0, 1, 1; 0, 0, 1] := by
  rw [regUnip3_inv]
  simp only [Matrix.SpecialLinearGroup.coe_mul]
  rw [coe_tr3_02, coe_tr3_12, coe_tr3_01]
  simp only [Matrix.mul_fin_three]
  ext a b
  fin_cases a <;> fin_cases b <;> simp

theorem coe_regUnip3_conj :
    (((regUnip3 F)⁻¹ * tr3 2 0 (by decide) 1 * regUnip3 F : SpecialLinearGroup (Fin 3) F) :
        Matrix (Fin 3) (Fin 3) F) = !![0, 1, 0; 1, 0, 0; 1, 1, 1] := by
  simp only [Matrix.SpecialLinearGroup.coe_mul]
  rw [coe_regUnip3_inv, coe_tr3_20, coe_regUnip3]
  simp only [Matrix.mul_fin_three]
  ext a b
  fin_cases a <;> fin_cases b <;> simp <;> grind

variable (F) in
noncomputable abbrev gm3 : SpecialLinearGroup (Fin 3) F := tr3 2 0 (by decide) 1

variable (F) in
noncomputable abbrev gz3 : SpecialLinearGroup (Fin 3) F := tr3 0 2 (by decide) 1

noncomputable def gk3 (s : F) : SpecialLinearGroup (Fin 3) F :=
  gm3 F * tr3 0 2 (by decide) s * gm3 F

variable (F) in
noncomputable def gtau3 : SpecialLinearGroup (Fin 3) F := (regUnip3 F)⁻¹ * gm3 F * regUnip3 F

theorem coe_gk3 (s : F) :
    ((gk3 s : SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) =
      !![1 + s, 0, s; 0, 1, 0; s, 0, 1 + s] := by
  rw [gk3]
  simp only [Matrix.SpecialLinearGroup.coe_mul]
  rw [coe_tr3_20, coe_tr3_02]
  simp only [Matrix.mul_fin_three]
  ext a b
  fin_cases a <;> fin_cases b <;> simp <;> grind

theorem coe_gk3_mul_gtau3 (s : F) :
    ((gk3 s : SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) *
      (gtau3 F : Matrix (Fin 3) (Fin 3) F) =
      !![s, 1, s; 1, 0, 0; 1 + s, 1, 1 + s] := by
  rw [coe_gk3, gtau3, coe_regUnip3_conj]
  simp only [Matrix.mul_fin_three]
  ext a b
  fin_cases a <;> fin_cases b <;> simp <;> grind

theorem coe_gk3_mul_gtau3_sq (s : F) :
    ((gk3 s : SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) *
      (gtau3 F : Matrix (Fin 3) (Fin 3) F) *
      ((gk3 s : Matrix (Fin 3) (Fin 3) F) * (gtau3 F : Matrix (Fin 3) (Fin 3) F)) =
      !![1 + s, 0, s; s, 1, s; s, 0, 1 + s] := by
  rw [coe_gk3_mul_gtau3]
  simp only [Matrix.mul_fin_three]
  ext a b
  fin_cases a <;> fin_cases b <;> simp <;> grind

theorem tr3_12_eq_word (s : F) :
    tr3 1 2 (by decide) s =
      tr3 0 2 (by decide) s * gm3 F * (gk3 s * gtau3 F * (gk3 s * gtau3 F)) * gm3 F := by
  apply Subtype.ext
  simp only [Matrix.SpecialLinearGroup.coe_mul]
  rw [coe_gk3_mul_gtau3_sq, coe_tr3_12, coe_tr3_02, coe_tr3_20]
  simp only [Matrix.mul_fin_three]
  ext a b
  fin_cases a <;> fin_cases b <;> simp <;> grind

theorem coe_gz3_gtau3_gz3 :
    ((gz3 F : SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) *
      (gtau3 F : Matrix (Fin 3) (Fin 3) F) *
      (gz3 F : Matrix (Fin 3) (Fin 3) F) = !![1, 0, 0; 1, 0, 1; 1, 1, 0] := by
  rw [gtau3, coe_tr3_02, coe_regUnip3_conj]
  simp only [Matrix.mul_fin_three]
  ext a b
  fin_cases a <;> fin_cases b <;> simp <;> grind

theorem coe_gk3_mul_ztz (s : F) :
    ((gk3 s : SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) *
      ((gz3 F : Matrix (Fin 3) (Fin 3) F) * (gtau3 F : Matrix (Fin 3) (Fin 3) F) *
        (gz3 F : Matrix (Fin 3) (Fin 3) F)) =
      !![1, s, 0; 1, 0, 1; 1, 1 + s, 0] := by
  rw [coe_gk3, coe_gz3_gtau3_gz3]
  simp only [Matrix.mul_fin_three]
  ext a b
  fin_cases a <;> fin_cases b <;> simp <;> grind

theorem coe_gk3_mul_ztz_sq (s : F) :
    ((gk3 s : SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) *
      ((gz3 F : Matrix (Fin 3) (Fin 3) F) * (gtau3 F : Matrix (Fin 3) (Fin 3) F) *
        (gz3 F : Matrix (Fin 3) (Fin 3) F)) *
      ((gk3 s : Matrix (Fin 3) (Fin 3) F) *
        ((gz3 F : Matrix (Fin 3) (Fin 3) F) * (gtau3 F : Matrix (Fin 3) (Fin 3) F) *
        (gz3 F : Matrix (Fin 3) (Fin 3) F))) =
      !![1 + s, s, s; 0, 1, 0; s, s, 1 + s] := by
  rw [coe_gk3_mul_ztz]
  simp only [Matrix.mul_fin_three]
  ext a b
  fin_cases a <;> fin_cases b <;> simp <;> grind

omit [CharP F 2] in
theorem mul_aux_01 (s : F) :
    (!![1, 0, s; 0, 1, 0; 0, 0, 1] * !![1, 0, 0; 0, 1, 0; 1, 0, 1] : Matrix (Fin 3) (Fin 3) F) =
      !![1 + s, 0, s; 0, 1, 0; 1, 0, 1] := by
  simp only [Matrix.mul_fin_three]
  ext a b
  fin_cases a <;> fin_cases b <;> simp

theorem mul_aux_01' (s : F) :
    (!![1 + s, 0, s; 0, 1, 0; 1, 0, 1] * !![1 + s, s, s; 0, 1, 0; s, s, 1 + s] :
      Matrix (Fin 3) (Fin 3) F) = !![1, s, 0; 0, 1, 0; 1, 0, 1] := by
  simp only [Matrix.mul_fin_three]
  ext a b
  fin_cases a <;> fin_cases b <;> simp <;> grind

theorem tr3_01_eq_word (s : F) :
    tr3 0 1 (by decide) s = tr3 0 2 (by decide) s * gm3 F *
      (gk3 s * (gz3 F * gtau3 F * gz3 F) * (gk3 s * (gz3 F * gtau3 F * gz3 F))) * gm3 F := by
  apply Subtype.ext
  simp only [Matrix.SpecialLinearGroup.coe_mul]
  rw [coe_gk3_mul_ztz_sq, coe_tr3_01, coe_tr3_02, coe_tr3_20, mul_aux_01, mul_aux_01']
  simp only [Matrix.mul_fin_three]
  ext a b
  fin_cases a <;> fin_cases b <;> (simp; try grind)

theorem coe_gweyl3 :
    ((gz3 F * gm3 F * gz3 F : SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) =
      !![0, 0, 1; 0, 1, 0; 1, 0, 0] := by
  simp only [Matrix.SpecialLinearGroup.coe_mul]
  rw [coe_tr3_02, coe_tr3_20]
  simp only [Matrix.mul_fin_three]
  ext a b
  fin_cases a <;> fin_cases b <;> simp <;> grind

theorem tr3_10_eq_conj (s : F) :
    tr3 1 0 (by decide) s = (gz3 F * gm3 F * gz3 F) * tr3 1 2 (by decide) s *
      (gz3 F * gm3 F * gz3 F) := by
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, coe_gweyl3, coe_tr3_10,
    coe_tr3_12]
  simp only [Matrix.mul_fin_three]
  ext a b
  fin_cases a <;> fin_cases b <;> simp

theorem tr3_21_eq_conj (s : F) :
    tr3 2 1 (by decide) s = (gz3 F * gm3 F * gz3 F) * tr3 0 1 (by decide) s *
      (gz3 F * gm3 F * gz3 F) := by
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, coe_gweyl3, coe_tr3_21,
    coe_tr3_01]
  simp only [Matrix.mul_fin_three]
  ext a b
  fin_cases a <;> fin_cases b <;> simp

theorem eq_top_of_block_conj {H : Subgroup (SpecialLinearGroup (Fin 3) F)}
    (h02 : ∀ c : F, tr3 0 2 (by decide) c ∈ H) (h20 : ∀ c : F, tr3 2 0 (by decide) c ∈ H)
    (hg : (regUnip3 F)⁻¹ * tr3 2 0 (by decide) 1 * regUnip3 F ∈ H) : H = ⊤ := by
  have hmH : gm3 F ∈ H := h20 1
  have hzH : gz3 F ∈ H := h02 1
  have hkH : ∀ s, gk3 s ∈ H := fun s => mul_mem (mul_mem hmH (h02 s)) hmH
  have hτH : gtau3 F ∈ H := by rw [gtau3]; exact hg
  have hzτz : gz3 F * gtau3 F * gz3 F ∈ H := mul_mem (mul_mem hzH hτH) hzH
  have hwH : gz3 F * gm3 F * gz3 F ∈ H := mul_mem (mul_mem hzH hmH) hzH
  have h12 : ∀ s : F, tr3 1 2 (by decide) s ∈ H := by
    intro s
    rw [tr3_12_eq_word]
    exact mul_mem (mul_mem (mul_mem (h02 s) hmH)
      (mul_mem (mul_mem (hkH s) hτH) (mul_mem (hkH s) hτH))) hmH
  have h01 : ∀ s : F, tr3 0 1 (by decide) s ∈ H := by
    intro s
    rw [tr3_01_eq_word]
    exact mul_mem (mul_mem (mul_mem (h02 s) hmH)
      (mul_mem (mul_mem (hkH s) hzτz) (mul_mem (hkH s) hzτz))) hmH
  have h10 : ∀ s : F, tr3 1 0 (by decide) s ∈ H := fun s => by
    rw [tr3_10_eq_conj]
    exact mul_mem (mul_mem hwH (h12 s)) hwH
  have h21 : ∀ s : F, tr3 2 1 (by decide) s ∈ H := fun s => by
    rw [tr3_21_eq_conj]
    exact mul_mem (mul_mem hwH (h01 s)) hwH
  have hall : ∀ (i j : Fin 3) (h : i ≠ j) (c : F), SpecialLinearGroup.transvection h c ∈ H := by
    intro i j h c
    fin_cases i <;> fin_cases j
    all_goals first
      | exact absurd rfl h
      | exact h01 c | exact h02 c | exact h10 c | exact h12 c | exact h20 c | exact h21 c
  rw [eq_top_iff, ← CFSG.LieType.Universal.SpecialLinear.iSup_fundamentalRootSubgroup_eq_top
    (m := 2) (F := F)]
  refine iSup_le fun i => iSup_le fun b => ?_
  intro x hx
  cases b <;> obtain ⟨c, rfl⟩ :=
    (CFSG.LieType.Universal.SpecialLinear.mem_rootSubgroup _ x).mp hx <;> exact hall _ _ _ c

end Gen

end CFSG.SeitzReduction.SymplecticPilot

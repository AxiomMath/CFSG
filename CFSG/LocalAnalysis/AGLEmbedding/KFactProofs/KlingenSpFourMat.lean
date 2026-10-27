module

public import CFSG.LocalAnalysis.ComponentInitial.SymplecticFlagData
import CFSG.LieType.BorelTits.Symplectic

public section

namespace CFSG.AGLEmbedding.KlingenSpFour

open Matrix CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag
open scoped MatrixGroups

variable {F : Type} [Field F]

@[expose] def A2 (s : F) : Matrix (Fin 2) (Fin 2) F := !![1, s; 0, 1]
@[expose] def C2 (u t : F) : Matrix (Fin 2) (Fin 2) F := !![u, t; t, 0]
@[expose] def S2 (a b c : F) : Matrix (Fin 2) (Fin 2) F := !![a, b; b, c]

theorem A2_det (s : F) : (A2 s).det = 1 := by simp [A2, Matrix.det_fin_two]
theorem A2_isUnit (s : F) : IsUnit (A2 s).det := by rw [A2_det]; exact isUnit_one
theorem C2_symm (u t : F) : (C2 u t)ᵀ = C2 u t := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [C2]
omit [Field F] in
theorem S2_symm (a b c : F) : (S2 a b c)ᵀ = S2 a b c := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [S2]

@[expose] noncomputable def eEl (s t u : F) : StatedSp 2 F := blockElt (A2_isUnit s) (C2_symm u t)

@[expose] noncomputable def xEl (a b c : F) : StatedSp 2 F := upperUnipotentSp 2 F (S2_symm a b c)

theorem coe_eEl (s t u : F) :
    (((eEl s t u : StatedSp 2 F) : GL (Fin 2 ⊕ Fin 2) F) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F)
      = blockMat (A2 s) (C2 u t) := coe_blockElt _ _

theorem coe_xEl (a b c : F) :
    (((xEl a b c : StatedSp 2 F) : GL (Fin 2 ⊕ Fin 2) F) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F)
      = fromBlocks 1 (S2 a b c) 0 1 := coe_upperUnipotentSp _

theorem A2_inv (s : F) : (A2 s)⁻¹ = A2 (-s) := by
  refine Matrix.inv_eq_right_inv ?_
  simp [A2, Matrix.one_fin_two]

theorem A2_mul (s s' : F) : A2 s * A2 s' = A2 (s + s') := by
  simp [A2, add_comm]

theorem A2_zero : A2 (0 : F) = 1 := by
  simp [A2, Matrix.one_fin_two]

theorem C2_add (u t u' t' : F) : C2 u t + C2 u' t' = C2 (u + u') (t + t') := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [C2]

theorem A2_inv_mul_C2_mul_transpose (s u t : F) :
    (A2 s)⁻¹ * C2 u t * (A2 s)⁻¹ᵀ = C2 (u - 2 * s * t) t := by
  rw [A2_inv]
  ext i j; fin_cases i <;> fin_cases j <;> simp [A2, C2, Matrix.mul_apply, Fin.sum_univ_two]
  ring

theorem eEl_mul (s t u s' t' u' : F) :
    eEl s t u * eEl s' t' u' = eEl (s + s') (t + t') (u + u' - 2 * s' * t) := by
  refine Subtype.ext (Units.ext ?_)
  rw [Subgroup.coe_mul, Units.val_mul, coe_eEl, coe_eEl, coe_eEl,
    blockMat_mul (A2_isUnit s'), A2_mul, A2_inv_mul_C2_mul_transpose, C2_add]
  congr 2 <;> ring

theorem A2_isUnitriangular (s : F) : IsUnitriangular (A2 s) := by
  refine ⟨?_, fun i => ?_⟩
  · intro i j hij
    fin_cases i <;> fin_cases j <;> simp [A2] at hij ⊢
  · fin_cases i <;> simp [A2]

theorem eEl_mem_unipotent (s t u : F) : eEl s t u ∈ unipotent 2 F :=
  mem_unipotent.mpr ⟨A2 s, C2 u t, A2_isUnitriangular s, C2_symm u t, coe_eEl s t u⟩

theorem eEl_inj {s t u s' t' u' : F} (h : eEl s t u = eEl s' t' u') :
    s = s' ∧ t = t' ∧ u = u' := by
  have h' : blockMat (A2 s) (C2 u t) = blockMat (A2 s') (C2 u' t') := by
    rw [← coe_eEl, ← coe_eEl, h]
  have h1 := congr_fun (congr_fun h' (Sum.inl 0)) (Sum.inl 1)
  have h2 := congr_fun (congr_fun h' (Sum.inl 0)) (Sum.inr 1)
  have h3 := congr_fun (congr_fun h' (Sum.inl 0)) (Sum.inr 0)
  simp [blockMat, A2, C2] at h1 h2 h3
  subst h1 h2
  exact ⟨rfl, rfl, by linear_combination h3⟩

theorem S2_add (a b c a' b' c' : F) :
    S2 a b c + S2 a' b' c' = S2 (a + a') (b + b') (c + c') := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [S2]

theorem S2_zero : S2 (0 : F) 0 0 = 0 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [S2]

theorem xEl_mul (a b c a' b' c' : F) :
    xEl a b c * xEl a' b' c' = xEl (a + a') (b + b') (c + c') := by
  refine Subtype.ext (Units.ext ?_)
  rw [Subgroup.coe_mul, Units.val_mul, coe_xEl, coe_xEl, coe_xEl, fromBlocks_multiply]
  simp [S2_add, add_comm]

theorem xEl_zero : xEl (0 : F) 0 0 = 1 := by
  refine Subtype.ext (Units.ext ?_)
  rw [coe_xEl, S2_zero, fromBlocks_one, Subgroup.coe_one, Units.val_one]

theorem xEl_mem_unipotent (a b c : F) : xEl a b c ∈ unipotent 2 F :=
  mem_unipotent.mpr ⟨1, S2 a b c, isUnitriangular_one, S2_symm a b c, by
    rw [coe_xEl]; simp [blockMat]⟩

theorem xEl_inj {a b c a' b' c' : F} (h : xEl a b c = xEl a' b' c') :
    a = a' ∧ b = b' ∧ c = c' := by
  have h' : (fromBlocks 1 (S2 a b c) 0 1 : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) =
      fromBlocks 1 (S2 a' b' c') 0 1 := by
    rw [← coe_xEl, ← coe_xEl, h]
  have h'' := (fromBlocks_inj.mp h').2.1
  have h1 := congr_fun (congr_fun h'' 0) 0
  have h2 := congr_fun (congr_fun h'' 0) 1
  have h3 := congr_fun (congr_fun h'' 1) 1
  simp [S2] at h1 h2 h3
  exact ⟨h1, h2, h3⟩

theorem eEl_xEl_comm {s u : F} (h : eEl s 0 u * xEl 0 1 0 = xEl 0 1 0 * eEl s 0 u) :
    (2 : F) * s = 0 := by
  have h' : blockMat (A2 s) (C2 u 0) * fromBlocks 1 (S2 0 1 0) 0 1 =
      fromBlocks 1 (S2 0 1 0) 0 1 * blockMat (A2 s) (C2 u 0) := by
    have := congr_arg (fun g : StatedSp 2 F =>
      ((g : GL (Fin 2 ⊕ Fin 2) F) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F)) h
    simpa only [Subgroup.coe_mul, Units.val_mul, coe_eEl, coe_xEl] using this
  simp only [blockMat, A2_inv, fromBlocks_multiply] at h'
  have h1 := congr_fun (congr_fun h' (Sum.inl 0)) (Sum.inr 0)
  simp only [fromBlocks_apply₁₂, Matrix.add_apply, Matrix.mul_apply, Fin.sum_univ_two,
    Matrix.transpose_apply] at h1
  simp [A2, C2, S2] at h1
  linear_combination h1

@[expose] def iotaMat (g : Matrix (Fin 2) (Fin 2) F) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F :=
  fromBlocks !![1, 0; 0, g 0 0] !![0, 0; 0, g 0 1] !![0, 0; 0, g 1 0] !![1, 0; 0, g 1 1]

theorem iotaMat_mul (g h : Matrix (Fin 2) (Fin 2) F) :
    iotaMat g * iotaMat h = iotaMat (g * h) := by
  ext i j
  rcases i with i | i <;> rcases j with j | j <;> fin_cases i <;> fin_cases j <;>
    simp [iotaMat, Matrix.mul_apply, Fin.sum_univ_two, Fintype.sum_sum_type]

theorem iotaMat_one : iotaMat (1 : Matrix (Fin 2) (Fin 2) F) = 1 := by
  ext i j
  rcases i with i | i <;> rcases j with j | j <;> fin_cases i <;> fin_cases j <;>
    simp [iotaMat]

theorem iotaMat_symp {g : Matrix (Fin 2) (Fin 2) F} (hg : g.det = 1) :
    (iotaMat g)ᵀ * fromBlocks 0 1 (-1) 0 * iotaMat g = fromBlocks 0 1 (-1) 0 := by
  rw [Matrix.det_fin_two] at hg
  ext i j
  rcases i with i | i <;> rcases j with j | j <;> fin_cases i <;> fin_cases j <;>
    simp [iotaMat, Matrix.mul_apply, Fin.sum_univ_two, Fintype.sum_sum_type, Matrix.one_apply,
      Matrix.transpose_apply] <;>
    first | ring1 | linear_combination hg | linear_combination (-1 : F) * hg

@[expose] noncomputable def iotaSp : SL(2, F) →* StatedSp 2 F where
  toFun g := ⟨⟨iotaMat (g : Matrix (Fin 2) (Fin 2) F),
    iotaMat ((g⁻¹ : SL(2, F)) : Matrix (Fin 2) (Fin 2) F),
    by rw [iotaMat_mul, ← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel,
      Matrix.SpecialLinearGroup.coe_one, iotaMat_one],
    by rw [iotaMat_mul, ← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel,
      Matrix.SpecialLinearGroup.coe_one, iotaMat_one]⟩,
    Subgroup.subset_closure (iotaMat_symp g.2)⟩
  map_one' := Subtype.ext (Units.ext (by
    show iotaMat ((1 : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) = 1
    rw [Matrix.SpecialLinearGroup.coe_one, iotaMat_one]))
  map_mul' g h := Subtype.ext (Units.ext (by
    show iotaMat ((g * h : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) =
      iotaMat (g : Matrix (Fin 2) (Fin 2) F) * iotaMat (h : Matrix (Fin 2) (Fin 2) F)
    rw [Matrix.SpecialLinearGroup.coe_mul, iotaMat_mul]))

theorem coe_iotaSp (g : SL(2, F)) :
    (((iotaSp g : StatedSp 2 F) : GL (Fin 2 ⊕ Fin 2) F) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F)
      = iotaMat (g : Matrix (Fin 2) (Fin 2) F) := rfl

theorem iotaSp_conj (g : SL(2, F)) (s t u : F) :
    iotaSp g * eEl s t u * (iotaSp g)⁻¹ =
      eEl (g 1 1 * s - g 1 0 * t) (g 0 0 * t - g 0 1 * s)
        (u + s * t - (g 1 1 * s - g 1 0 * t) * (g 0 0 * t - g 0 1 * s)) := by
  have hdet : g 0 0 * g 1 1 - g 0 1 * g 1 0 = 1 := by
    rw [← Matrix.det_fin_two]
    exact g.2
  rw [mul_inv_eq_iff_eq_mul]
  refine Subtype.ext (Units.ext ?_)
  show ((iotaSp g : StatedSp 2 F) : GL (Fin 2 ⊕ Fin 2) F).val * ((eEl s t u : StatedSp 2 F) :
      GL (Fin 2 ⊕ Fin 2) F).val = _
  rw [Subgroup.coe_mul, Units.val_mul, coe_iotaSp, coe_eEl, coe_eEl]
  simp only [blockMat, A2_inv]
  ext i j
  rcases i with i | i <;> rcases j with j | j <;> fin_cases i <;> fin_cases j <;>
    simp [iotaMat, A2, C2, Matrix.mul_apply, Fin.sum_univ_two, Fintype.sum_sum_type] <;>
    first | ring1 | linear_combination (-s) * hdet | linear_combination (-t) * hdet

theorem single_inl_mem_flag_two (j : Fin 2) :
    (Pi.single (Sum.inl j) (1 : F) : Fin 2 ⊕ Fin 2 → F) ∈ flag 2 F 2 := by
  rw [mem_flag_of_le le_rfl, mem_isoFlag]
  exact ⟨fun k => by simp, fun k hk => absurd k.2 (not_lt.mpr hk)⟩

theorem stabilizer_flag_entry_inr_inl {h : StatedSp 2 F} (hh : h ∈ stabilizer 2 F (flag 2 F 2))
    (i j : Fin 2) :
    ((h : GL (Fin 2 ⊕ Fin 2) F) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F)
      (Sum.inr i) (Sum.inl j) = 0 := by
  have hmem := Submodule.mem_map_of_mem (f := mulVecLin ((h : GL (Fin 2 ⊕ Fin 2) F) :
    Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F)) (single_inl_mem_flag_two (F := F) j)
  rw [mem_stabilizer.mp hh, mem_flag_of_le le_rfl, mem_isoFlag, mulVecLin_apply] at hmem
  simpa [mulVec_single_one] using hmem.1 i

theorem exists_fromBlocks_of_entries_inr_inl {M : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F}
    (hM : ∀ i j, M (Sum.inr i) (Sum.inl j) = 0) :
    ∃ A B D : Matrix (Fin 2) (Fin 2) F, M = fromBlocks A B 0 D := by
  refine ⟨M.toBlocks₁₁, M.toBlocks₁₂, M.toBlocks₂₂, ?_⟩
  conv_lhs => rw [← fromBlocks_toBlocks M]
  congr 1
  ext i j
  exact hM i j

theorem transpose_mul_eq_one_of_symplectic {A B D : Matrix (Fin 2) (Fin 2) F}
    (h : (fromBlocks A B 0 D)ᵀ * fromBlocks 0 1 (-1) 0 * fromBlocks A B 0 D =
      fromBlocks 0 1 (-1) 0) : Aᵀ * D = 1 := by
  simp only [fromBlocks_transpose, transpose_zero, fromBlocks_multiply] at h
  simpa using (fromBlocks_inj.mp h).2.1

theorem fromBlocks_mul_siegel {A B D : Matrix (Fin 2) (Fin 2) F} (hAD : Aᵀ * D = 1)
    (S : Matrix (Fin 2) (Fin 2) F) :
    fromBlocks A B 0 D * fromBlocks 1 S 0 1 =
      fromBlocks 1 (A * S * Aᵀ) 0 1 * fromBlocks A B 0 D := by
  simp only [fromBlocks_multiply, Matrix.mul_one, Matrix.one_mul, Matrix.zero_mul,
    Matrix.mul_zero, add_zero, zero_add, Matrix.mul_assoc, hAD]
  rw [add_comm]

omit [Field F] in
theorem eq_S2_of_transpose_eq {C : Matrix (Fin 2) (Fin 2) F} (hC : Cᵀ = C) :
    C = S2 (C 0 0) (C 0 1) (C 1 1) := by
  have h10 : C 1 0 = C 0 1 := by simpa using congrFun (congrFun hC 0) 1
  ext i j
  fin_cases i <;> fin_cases j <;> simp [S2, h10]

theorem stabilizer_conj_xEl {h : StatedSp 2 F} (hh : h ∈ stabilizer 2 F (flag 2 F 2))
    (a b c : F) :
    ∃ a' b' c' : F, h * xEl a b c * h⁻¹ = xEl a' b' c' := by
  obtain ⟨A, B, D, hM⟩ := exists_fromBlocks_of_entries_inr_inl (stabilizer_flag_entry_inr_inl hh)
  have hsymp := CFSG.LieType.BorelTits.transpose_mul_mul_of_mem_statedSp h.2
  rw [hM] at hsymp
  have hAD := transpose_mul_eq_one_of_symplectic hsymp
  have hsymm : (A * S2 a b c * Aᵀ)ᵀ = A * S2 a b c * Aᵀ := by
    rw [transpose_mul, transpose_mul, transpose_transpose, S2_symm, Matrix.mul_assoc]
  refine ⟨(A * S2 a b c * Aᵀ) 0 0, (A * S2 a b c * Aᵀ) 0 1, (A * S2 a b c * Aᵀ) 1 1, ?_⟩
  rw [mul_inv_eq_iff_eq_mul]
  refine Subtype.ext (Units.ext ?_)
  rw [Subgroup.coe_mul, Subgroup.coe_mul, Units.val_mul, Units.val_mul, coe_xEl, coe_xEl,
    ← eq_S2_of_transpose_eq hsymm, hM]
  exact fromBlocks_mul_siegel hAD _

theorem iotaSp_not_mem_stabilizer (g₀ : SL(2, F)) (h : g₀ 1 0 ≠ 0) :
    iotaSp g₀ ∉ stabilizer 2 F (flag 2 F 2) := by
  intro hmem
  have h0 := stabilizer_flag_entry_inr_inl hmem 1 1
  rw [coe_iotaSp] at h0
  exact h (by simpa [iotaMat] using h0)

end CFSG.AGLEmbedding.KlingenSpFour

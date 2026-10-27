module

public import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.YamadaEndL44Defs
public import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.YamadaEndConj

public section

namespace CFSG.EvenSmallLie.UnitarySix.YamadaEnd

open Matrix Subgroup CFSG.ClassicalInvolution.WeakCT
open CFSG.ClassicalInvolution.Phan (blockMat blockMat_apply)
open scoped MatrixGroups

variable (F : Type) [Field F] [CharP F 2]

omit [CharP F 2] in
theorem permMatrix_mul_mul_permMatrix_apply {n : ℕ} (σ τ : Equiv.Perm (Fin n))
    (M : Matrix (Fin n) (Fin n) F) (a b : Fin n) :
    (σ.permMatrix F * M * τ.permMatrix F) a b = M (σ a) (τ.symm b) := by
  simp only [Equiv.Perm.permMatrix, PEquiv.toMatrix_toPEquiv_mul, PEquiv.mul_toMatrix_toPEquiv,
    submatrix_apply, id]

omit [CharP F 2] in
theorem map_permMatrix {n : ℕ} (ψ : F ≃+* F) (σ : Equiv.Perm (Fin n)) :
    (σ.permMatrix F).map ψ = σ.permMatrix F := by
  ext a b
  simp only [Matrix.map_apply, Equiv.Perm.permMatrix, PEquiv.toMatrix_apply]
  split_ifs <;> simp

omit [CharP F 2] in
theorem coe_inv_of_coe_eq_permMatrix {σ : Equiv.Perm (Fin 4)} {g : SL(4, F)}
    (hg : (g : Matrix (Fin 4) (Fin 4) F) = σ.permMatrix F) :
    ((g⁻¹ : SL(4, F)) : Matrix (Fin 4) (Fin 4) F) = σ⁻¹.permMatrix F := by
  have h1 : ((g⁻¹ : SL(4, F)) : Matrix (Fin 4) (Fin 4) F) * g = 1 := by
    rw [← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel, Matrix.SpecialLinearGroup.coe_one]
  have h2 : σ.permMatrix F * σ⁻¹.permMatrix F = (1 : Matrix (Fin 4) (Fin 4) F) := by
    rw [← Matrix.permMatrix_mul, inv_mul_cancel, Matrix.permMatrix_one]
  calc ((g⁻¹ : SL(4, F)) : Matrix (Fin 4) (Fin 4) F)
      = (g⁻¹ : SL(4, F)) * (σ.permMatrix F * σ⁻¹.permMatrix F) := by rw [h2, Matrix.mul_one]
    _ = σ⁻¹.permMatrix F := by rw [← Matrix.mul_assoc, ← hg, h1, Matrix.one_mul]

omit [CharP F 2] in
theorem conj_apply_of_coe_eq_permMatrix {σ : Equiv.Perm (Fin 4)} {g : SL(4, F)}
    (hg : (g : Matrix (Fin 4) (Fin 4) F) = σ.permMatrix F) (x : SL(4, F)) (a b : Fin 4) :
    (g * x * g⁻¹ : SL(4, F)) a b = x (σ a) (σ b) := by
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul,
    coe_inv_of_coe_eq_permMatrix F hg, hg, permMatrix_mul_mul_permMatrix_apply,
    Equiv.Perm.inv_def, Equiv.symm_symm]

omit [CharP F 2] in
theorem inv_mul_transvection_mul_of_coe_eq_permMatrix {σ : Equiv.Perm (Fin 4)}
    {g : SL(4, F)} (hg : (g : Matrix (Fin 4) (Fin 4) F) = σ.permMatrix F) {i j : Fin 4}
    (h : i ≠ j) (c : F) :
    g⁻¹ * SpecialLinearGroup.transvection h c * g =
      SpecialLinearGroup.transvection (σ.injective.ne h) c := by
  ext a b
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul,
    coe_inv_of_coe_eq_permMatrix F hg, hg, permMatrix_mul_mul_permMatrix_apply]
  simp [SpecialLinearGroup.transvection_coe, one_apply, single_apply, Equiv.eq_symm_apply]

omit [CharP F 2] in
theorem conjR_rootSL_of_coe_eq_permMatrix {σ : Equiv.Perm (Fin 4)} {g : SL(4, F)}
    (hg : (g : Matrix (Fin 4) (Fin 4) F) = σ.permMatrix F) (i j : Fin 4) :
    conjR (rootSL F i j) g = rootSL F (σ i) (σ j) := by
  rw [conjR, rootSL, rootSL, MonoidHom.map_closure]
  congr 1
  ext y
  simp only [Set.mem_image, Set.mem_ofPred_eq, MulEquiv.coe_toMonoidHom, MulAut.conj_apply,
    inv_inv]
  constructor
  · rintro ⟨x, ⟨h, c, rfl⟩, rfl⟩
    exact ⟨σ.injective.ne h, c, inv_mul_transvection_mul_of_coe_eq_permMatrix F hg h c⟩
  · rintro ⟨h, c, rfl⟩
    exact ⟨_, ⟨σ.injective.ne_iff.mp h, c, rfl⟩,
      inv_mul_transvection_mul_of_coe_eq_permMatrix F hg _ c⟩

theorem coe_sY (k : Fin 3) :
    ((sY F k : SL(4, F)) : Matrix (Fin 4) (Fin 4) F) =
      (Equiv.swap k.castSucc k.succ).permMatrix F := by
  rw [sY, blockSL2, coe_blockSL]
  ext a b
  rw [blockMat_apply]
  fin_cases k <;> fin_cases a <;> fin_cases b <;> simp [swapSL2, Equiv.swap_apply_def]

omit [CharP F 2] in
theorem blockSL2_three_apply (k : Fin 3) (A : SL(2, F)) (a b : Fin 4) :
    (blockSL2 F 3 k A : SL(4, F)) a b = blockMat 4 k (A : Matrix (Fin 2) (Fin 2) F) a b :=
  rfl

omit [CharP F 2] in
theorem blockSL2_transvection_one_zero (k : Fin 3) (h : (1 : Fin 2) ≠ 0) (c : F) :
    blockSL2 F 3 k (SpecialLinearGroup.transvection h c) =
      SpecialLinearGroup.transvection (Fin.castSucc_lt_succ (i := k)).ne' c := by
  ext a b
  rw [blockSL2_three_apply, blockMat_apply]
  fin_cases k <;> fin_cases a <;> fin_cases b <;>
    simp [SpecialLinearGroup.transvection_coe, one_apply]

omit [CharP F 2] in
theorem blockSL2_transvection_zero_one (k : Fin 3) (h : (0 : Fin 2) ≠ 1) (c : F) :
    blockSL2 F 3 k (SpecialLinearGroup.transvection h c) =
      SpecialLinearGroup.transvection (Fin.castSucc_lt_succ (i := k)).ne c := by
  ext a b
  rw [blockSL2_three_apply, blockMat_apply]
  fin_cases k <;> fin_cases a <;> fin_cases b <;>
    simp [SpecialLinearGroup.transvection_coe, one_apply]

omit [CharP F 2] in
theorem rootSL_sup_rootSL_eq_range (k : Fin 3) :
    rootSL F k.succ k.castSucc ⊔ rootSL F k.castSucc k.succ = (blockSL2 F 3 k).range := by
  refine le_antisymm (sup_le ((closure_le _).mpr ?_) ((closure_le _).mpr ?_)) ?_
  · rintro _ ⟨h, c, rfl⟩
    exact ⟨_, blockSL2_transvection_one_zero F k one_ne_zero c⟩
  · rintro _ ⟨h, c, rfl⟩
    exact ⟨_, blockSL2_transvection_zero_one F k zero_ne_one c⟩
  · rintro _ ⟨B, rfl⟩
    induction B using Matrix.SL2.transvection_induction with
    | htransvec i j h c =>
      fin_cases i <;> fin_cases j
      · exact absurd rfl h
      · rw [blockSL2_transvection_zero_one F k h c]
        exact mem_sup_right (subset_closure ⟨_, c, rfl⟩)
      · rw [blockSL2_transvection_one_zero F k h c]
        exact mem_sup_left (subset_closure ⟨_, c, rfl⟩)
      · exact absurd rfl h
    | hmul A B hA hB =>
      rw [map_mul]
      exact mul_mem hA hB

theorem coe_sY_zero_mul_sY_two :
    ((sY F 0 * sY F 2 : SL(4, F)) : Matrix (Fin 4) (Fin 4) F) =
      (Equiv.swap 0 1 * Equiv.swap 2 3 : Equiv.Perm (Fin 4)).permMatrix F := by
  simp only [Matrix.SpecialLinearGroup.coe_mul, coe_sY, ← permMatrix_mul]
  congr 1
  decide

theorem conjR_rootSL_one_zero : conjR (rootSL F 1 0) (sY F 0 * sY F 2) = rootSL F 0 1 :=
  conjR_rootSL_of_coe_eq_permMatrix F (coe_sY_zero_mul_sY_two F) 1 0

theorem conjR_rootSL_three_two : conjR (rootSL F 3 2) (sY F 0 * sY F 2) = rootSL F 2 3 :=
  conjR_rootSL_of_coe_eq_permMatrix F (coe_sY_zero_mul_sY_two F) 3 2

theorem conjR_rootSL_two_one : conjR (rootSL F 2 1) (sY F 1) = rootSL F 1 2 :=
  conjR_rootSL_of_coe_eq_permMatrix F (coe_sY F 1) 2 1

omit [CharP F 2] in
theorem lowerUni_mul {A B : Matrix (Fin 4) (Fin 4) F}
    (hA : (∀ i j, i < j → A i j = 0) ∧ ∀ i, A i i = 1)
    (hB : (∀ i j, i < j → B i j = 0) ∧ ∀ i, B i i = 1) :
    (∀ i j, i < j → (A * B) i j = 0) ∧ ∀ i, (A * B) i i = 1 := by
  refine ⟨fun i j hij => ?_, fun i => ?_⟩
  · rw [mul_apply]
    refine Finset.sum_eq_zero fun k _ => ?_
    rcases lt_or_ge i k with hik | hki
    · rw [hA.1 i k hik, zero_mul]
    · rw [hB.1 k j (lt_of_le_of_lt hki hij), mul_zero]
  · rw [mul_apply, Finset.sum_eq_single i (fun k _ hki => ?_) (by simp), hA.2, hB.2, one_mul]
    rcases lt_or_gt_of_ne hki with h | h
    · rw [hB.1 k i h, mul_zero]
    · rw [hA.1 i k h, zero_mul]

omit [CharP F 2] in
theorem lowerUni_transvection {i j : Fin 4} (h : i ≠ j) (hji : j < i) (c : F) :
    (∀ a b, a < b → (SpecialLinearGroup.transvection h c : SL(4, F)) a b = 0) ∧
      ∀ a, (SpecialLinearGroup.transvection h c : SL(4, F)) a a = 1 := by
  refine ⟨fun a b hab => ?_, fun a => ?_⟩
  · rw [SpecialLinearGroup.transvection_coe, Matrix.add_apply, one_apply_ne hab.ne,
      single_apply, ite_eq_right, add_zero]
    rintro ⟨rfl, rfl⟩
    exact lt_irrefl _ (hab.trans hji)
  · rw [SpecialLinearGroup.transvection_coe, Matrix.add_apply, one_apply_eq, single_apply,
      ite_eq_right, add_zero]
    rintro ⟨rfl, rfl⟩
    exact h rfl

omit [CharP F 2] in
theorem lowerUni_of_mem_pstd {x : SL(4, F)} (hx : x ∈ pstd F) :
    (∀ i j : Fin 4, i < j → x i j = 0) ∧ ∀ i : Fin 4, x i i = 1 := by
  rw [pstd] at hx
  induction hx using Subgroup.closure_induction'' with
  | mem y hy =>
    obtain ⟨i, j, h, c, hji, rfl⟩ := hy
    exact lowerUni_transvection F h hji c
  | inv_mem y hy =>
    obtain ⟨i, j, h, c, hji, rfl⟩ := hy
    rw [SpecialLinearGroup.transvection_inv]
    exact lowerUni_transvection F h hji (-c)
  | one =>
    exact ⟨fun i j hij => by simp [one_apply, hij.ne], fun i => by simp⟩
  | mul y z _ _ hy hz =>
    rw [Matrix.SpecialLinearGroup.coe_mul]
    exact lowerUni_mul F hy hz

omit [CharP F 2] in
theorem lowerUni_of_mem_pstd_inf_conjR {σ : Equiv.Perm (Fin 4)} {g : SL(4, F)}
    (hg : (g : Matrix (Fin 4) (Fin 4) F) = σ.permMatrix F) {x : SL(4, F)}
    (hx : x ∈ pstd F ⊓ conjR (pstd F) g) :
    ((∀ i j : Fin 4, i < j → x i j = 0) ∧ ∀ i : Fin 4, x i i = 1) ∧
      ∀ a b : Fin 4, a < b → x (σ a) (σ b) = 0 := by
  obtain ⟨hx, hx'⟩ := Subgroup.mem_inf.mp hx
  rw [mem_conjR] at hx'
  refine ⟨lowerUni_of_mem_pstd F hx, fun a b hab => ?_⟩
  rw [← conj_apply_of_coe_eq_permMatrix F hg]
  exact (lowerUni_of_mem_pstd F hx').1 a b hab

omit [CharP F 2] in
theorem rootSL_le_pstd {i j : Fin 4} (hji : j < i) : rootSL F i j ≤ pstd F :=
  (closure_le _).mpr fun _ ⟨h, c, hA⟩ => subset_closure ⟨i, j, h, c, hji, hA⟩

theorem pstd_inf_conjR_b :
    pstd F ⊓ conjR (pstd F) (sY F 1 * (sY F 0 * sY F 2) * sY F 1) =
      rootSL F 1 0 ⊔ rootSL F 3 2 := by
  set g := sY F 1 * (sY F 0 * sY F 2) * sY F 1 with hg_def
  have hg : (g : Matrix (Fin 4) (Fin 4) F) =
      (Equiv.swap 0 2 * Equiv.swap 1 3 : Equiv.Perm (Fin 4)).permMatrix F := by
    simp only [hg_def, Matrix.SpecialLinearGroup.coe_mul, coe_sY, ← permMatrix_mul]
    congr 1
    decide
  refine le_antisymm (fun x hx => ?_) (sup_le (le_inf (rootSL_le_pstd F (by decide)) ?_)
    (le_inf (rootSL_le_pstd F (by decide)) ?_))
  · obtain ⟨⟨hl, hd⟩, hl'⟩ := lowerUni_of_mem_pstd_inf_conjR F hg hx
    have h20 : x 2 0 = 0 := hl' 0 2 (by decide)
    have h21 : x 2 1 = 0 := hl' 0 3 (by decide)
    have h30 : x 3 0 = 0 := hl' 1 2 (by decide)
    have h31 : x 3 1 = 0 := hl' 1 3 (by decide)
    have key : x = SpecialLinearGroup.transvection (by decide : (1 : Fin 4) ≠ 0) (x 1 0) *
        SpecialLinearGroup.transvection (by decide : (3 : Fin 4) ≠ 2) (x 3 2) := by
      ext a b
      rw [Matrix.SpecialLinearGroup.coe_mul, SpecialLinearGroup.transvection_coe,
        SpecialLinearGroup.transvection_coe]
      fin_cases a <;> fin_cases b <;>
        simp [mul_apply, Fin.sum_univ_four, one_apply, single_apply, h20, h21, h30, h31,
          hd, hl 0 1 (by decide), hl 0 2 (by decide), hl 0 3 (by decide),
          hl 1 2 (by decide), hl 1 3 (by decide), hl 2 3 (by decide)]
    rw [key]
    exact mul_mem (mem_sup_left (subset_closure ⟨_, _, rfl⟩))
      (mem_sup_right (subset_closure ⟨_, _, rfl⟩))
  · calc rootSL F 1 0 = conjR (rootSL F 3 2) g :=
          (conjR_rootSL_of_coe_eq_permMatrix F hg 3 2).symm
      _ ≤ conjR (pstd F) g := conjR_mono (rootSL_le_pstd F (by decide)) g
  · calc rootSL F 3 2 = conjR (rootSL F 1 0) g :=
          (conjR_rootSL_of_coe_eq_permMatrix F hg 1 0).symm
      _ ≤ conjR (pstd F) g := conjR_mono (rootSL_le_pstd F (by decide)) g

theorem pstd_inf_conjR_c :
    pstd F ⊓ conjR (pstd F) (sY F 0 * sY F 2 * sY F 1 * (sY F 0 * sY F 2)) = rootSL F 2 1 := by
  set g := sY F 0 * sY F 2 * sY F 1 * (sY F 0 * sY F 2) with hg_def
  have hg : (g : Matrix (Fin 4) (Fin 4) F) =
      (Equiv.swap 0 3 : Equiv.Perm (Fin 4)).permMatrix F := by
    simp only [hg_def, Matrix.SpecialLinearGroup.coe_mul, coe_sY, ← permMatrix_mul]
    congr 1
    decide
  refine le_antisymm (fun x hx => ?_) (le_inf (rootSL_le_pstd F (by decide)) ?_)
  · obtain ⟨⟨hl, hd⟩, hl'⟩ := lowerUni_of_mem_pstd_inf_conjR F hg hx
    have h10 : x 1 0 = 0 := hl' 1 3 (by decide)
    have h20 : x 2 0 = 0 := hl' 2 3 (by decide)
    have h30 : x 3 0 = 0 := hl' 0 3 (by decide)
    have h31 : x 3 1 = 0 := hl' 0 1 (by decide)
    have h32 : x 3 2 = 0 := hl' 0 2 (by decide)
    have key : x = SpecialLinearGroup.transvection (by decide : (2 : Fin 4) ≠ 1) (x 2 1) := by
      ext a b
      rw [SpecialLinearGroup.transvection_coe]
      fin_cases a <;> fin_cases b <;>
        simp [one_apply, h10, h20, h30, h31, h32, hd, hl 0 1 (by decide),
          hl 0 2 (by decide), hl 0 3 (by decide), hl 1 2 (by decide), hl 1 3 (by decide),
          hl 2 3 (by decide)]
    rw [key]
    exact subset_closure ⟨_, _, rfl⟩
  · calc rootSL F 2 1 = conjR (rootSL F 2 1) g :=
          (conjR_rootSL_of_coe_eq_permMatrix F hg 2 1).symm
      _ ≤ conjR (pstd F) g := conjR_mono (rootSL_le_pstd F (by decide)) g

theorem sY_mul_self (k : Fin 3) : sY F k * sY F k = 1 :=
  Subtype.ext (by
    rw [Matrix.SpecialLinearGroup.coe_mul, coe_sY, ← permMatrix_mul, Equiv.swap_mul_self,
      permMatrix_one, Matrix.SpecialLinearGroup.coe_one])

theorem sY_inv (k : Fin 3) : (sY F k)⁻¹ = sY F k :=
  inv_eq_of_mul_eq_one_right (sY_mul_self F k)

theorem fieldAutSL_sY (ψ : F ≃+* F) (k : Fin 3) : fieldAutSL ψ 4 (sY F k) = sY F k :=
  Subtype.ext (by rw [coe_fieldAutSL, coe_sY, map_permMatrix])

theorem invTransposeSL_sY (k : Fin 3) : invTransposeSL 4 (sY F k) = sY F k :=
  Subtype.ext (by rw [coe_invTransposeSL, sY_inv, coe_sY, transpose_permMatrix, Equiv.swap_inv])

theorem conjSL_antiDiag_sY (k : Fin 3) :
    conjSL (antiDiag F) (antiDiag F) (antiDiag_mul_self F) (sY F k) = sY F k.rev := by
  refine Subtype.ext ?_
  rw [coe_conjSL, coe_sY, coe_sY, antiDiag, ← permMatrix_mul, ← permMatrix_mul]
  congr 1
  fin_cases k <;> decide

omit [CharP F 2] in
theorem fieldAutSL_transvection (ψ : F ≃+* F) {i j : Fin 4} (h : i ≠ j) (c : F) :
    fieldAutSL ψ 4 (SpecialLinearGroup.transvection h c) =
      SpecialLinearGroup.transvection h (ψ c) := by
  ext a b
  rw [coe_fieldAutSL, Matrix.map_apply, SpecialLinearGroup.transvection_coe,
    SpecialLinearGroup.transvection_coe, Matrix.add_apply, Matrix.add_apply, map_add, one_apply,
    single_apply, single_apply]
  split_ifs <;> simp

omit [CharP F 2] in
theorem invTransposeSL_transvection {i j : Fin 4} (h : i ≠ j) (c : F) :
    invTransposeSL 4 (SpecialLinearGroup.transvection h c) =
      SpecialLinearGroup.transvection h.symm (-c) :=
  Subtype.ext (by
    rw [coe_invTransposeSL, SpecialLinearGroup.transvection_inv,
      SpecialLinearGroup.transvection_coe, SpecialLinearGroup.transvection_coe, transpose_add,
      transpose_one, transpose_single])

omit [CharP F 2] in
theorem conjSL_antiDiag_transvection {i j : Fin 4} (h : i ≠ j) (c : F) :
    conjSL (antiDiag F) (antiDiag F) (antiDiag_mul_self F) (SpecialLinearGroup.transvection h c) =
      SpecialLinearGroup.transvection (Fin.rev_injective.ne h) c := by
  ext a b
  rw [coe_conjSL, antiDiag, permMatrix_mul_mul_permMatrix_apply,
    SpecialLinearGroup.transvection_coe, SpecialLinearGroup.transvection_coe]
  simp [one_apply, single_apply, Fin.rev_eq_iff]

variable [Finite F]

theorem sigmaSL_apply (A : SL(4, F)) :
    sigmaSL F A = conjSL (antiDiag F) (antiDiag F) (antiDiag_mul_self F)
      (invTransposeSL 4 (fieldAutSL (frobeniusEquiv F 2) 4 A)) :=
  rfl

theorem sigmaSL_transvection {i j : Fin 4} (h : i ≠ j) (c : F) :
    sigmaSL F (SpecialLinearGroup.transvection h c) =
      SpecialLinearGroup.transvection (Fin.rev_injective.ne h.symm) (c ^ 2) := by
  rw [sigmaSL_apply, fieldAutSL_transvection, invTransposeSL_transvection,
    conjSL_antiDiag_transvection, frobeniusEquiv_apply, frobenius_def, CharTwo.neg_eq]

theorem map_sigmaSL_rootSL (i j : Fin 4) :
    (rootSL F i j).map (sigmaSL F).toMonoidHom = rootSL F j.rev i.rev := by
  rw [rootSL, rootSL, MonoidHom.map_closure]
  congr 1
  ext y
  simp only [Set.mem_image, Set.mem_ofPred_eq, MulEquiv.coe_toMonoidHom]
  constructor
  · rintro ⟨x, ⟨h, c, rfl⟩, rfl⟩
    exact ⟨Fin.rev_injective.ne h.symm, c ^ 2, sigmaSL_transvection F h c⟩
  · rintro ⟨h, d, rfl⟩
    obtain ⟨c, rfl⟩ := (frobeniusEquiv F 2).surjective d
    refine ⟨SpecialLinearGroup.transvection (Fin.rev_injective.ne_iff.mp h).symm c,
      ⟨_, c, rfl⟩, ?_⟩
    rw [sigmaSL_transvection, frobeniusEquiv_apply, frobenius_def]

theorem sigmaSL_sY_zero : sigmaSL F (sY F 0) = sY F 2 := by
  rw [sigmaSL_apply, fieldAutSL_sY, invTransposeSL_sY, conjSL_antiDiag_sY]
  rfl

theorem sigmaSL_sY_two : sigmaSL F (sY F 2) = sY F 0 := by
  rw [sigmaSL_apply, fieldAutSL_sY, invTransposeSL_sY, conjSL_antiDiag_sY]
  rfl

theorem sigmaSL_sY_one : sigmaSL F (sY F 1) = sY F 1 := by
  rw [sigmaSL_apply, fieldAutSL_sY, invTransposeSL_sY, conjSL_antiDiag_sY]
  rfl

theorem map_sigmaSL_range_zero :
    (blockSL2 F 3 0).range.map (sigmaSL F).toMonoidHom = (blockSL2 F 3 2).range := by
  rw [← rootSL_sup_rootSL_eq_range, ← rootSL_sup_rootSL_eq_range, Subgroup.map_sup,
    map_sigmaSL_rootSL, map_sigmaSL_rootSL]
  rfl

end CFSG.EvenSmallLie.UnitarySix.YamadaEnd

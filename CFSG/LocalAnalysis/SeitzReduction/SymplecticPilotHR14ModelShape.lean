module

public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotHR14ModelPiece
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotHR14PartnerModel

public section

namespace CFSG.SeitzReduction.SymplecticPilot

open Subgroup Matrix CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial LinearFlag
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher (blockSwapJ)
open CFSG.LocalAnalysis.ComponentInitial.FourGroupEvenCanonical (matrixIsometryGroup
  mem_matrixIsometryGroup)
open CFSG.ComponentClassification.UnbalancedCatalog (mem_matrixIsometryGroup_iff_inverseTranspose
  sq_injective_of_charTwo dotProduct_mulVec_self_eq_zero)
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.ComponentClassification.OutcomeLocal (blockSwapIsometryEquivStatedSp)

section Matrices

variable {m : ℕ} {F : Type} [Field F] [CharP F 2]

omit [CharP F 2] in
theorem mulVec_dotProduct_eq_dotProduct_transpose (g : Matrix (Fin m) (Fin m) F) (v w : Fin m → F) :
    (g *ᵥ v) ⬝ᵥ w = v ⬝ᵥ (gᵀ *ᵥ w) := by
  rw [dotProduct_comm, dotProduct_mulVec, ← mulVec_transpose, dotProduct_comm]

theorem dotProduct_add_single_mulVec_self {J : Matrix (Fin m) (Fin m) F} (hJs : Jᵀ = J)
    (hJd : ∀ i, J i i = 0) (b : Fin m) (x : Fin m → F) :
    x ⬝ᵥ ((J + single b b 1) *ᵥ x) = x b ^ 2 := by
  rw [add_mulVec, dotProduct_add, dotProduct_mulVec_self_eq_zero hJs hJd, zero_add,
    single_mulVec]
  simp [dotProduct, Function.update_apply, sq]

theorem row_eq_of_isometry_add_single {J : Matrix (Fin m) (Fin m) F} (hJs : Jᵀ = J)
    (hJd : ∀ i, J i i = 0) (b : Fin m) {g : Matrix (Fin m) (Fin m) F}
    (hg : gᵀ * (J + single b b 1) * g = J + single b b 1) (j : Fin m) :
    g b j = (1 : Matrix (Fin m) (Fin m) F) b j := by
  have h1 : (g *ᵥ Pi.single j 1) ⬝ᵥ ((J + single b b 1) *ᵥ (g *ᵥ Pi.single j 1)) =
      Pi.single j (1 : F) ⬝ᵥ ((J + single b b 1) *ᵥ Pi.single j 1) := by
    rw [mulVec_dotProduct_eq_dotProduct_transpose, mulVec_mulVec, mulVec_mulVec, hg]
  rw [dotProduct_add_single_mulVec_self hJs hJd, dotProduct_add_single_mulVec_self hJs hJd]
    at h1
  have h2 := sq_injective_of_charTwo h1
  rw [mulVec_single_one, col_apply] at h2
  rw [h2, Pi.single_apply, one_apply]

theorem transpose_mul_mul_eq_of_isometry_add_single {J : Matrix (Fin m) (Fin m) F}
    (hJs : Jᵀ = J) (hJd : ∀ i, J i i = 0) (b : Fin m) {g : Matrix (Fin m) (Fin m) F}
    (hg : gᵀ * (J + single b b 1) * g = J + single b b 1) : gᵀ * J * g = J := by
  have hrow := row_eq_of_isometry_add_single hJs hJd b hg
  have hE : gᵀ * single b b 1 * g = single b b 1 := by
    ext i j
    rw [mul_apply, Finset.sum_eq_single b (fun k _ hk => by
        rw [mul_single_apply_of_ne (hbj := hk), zero_mul]) (by simp),
      mul_single_apply_same, transpose_apply, hrow, hrow, one_apply, one_apply, single_apply]
    by_cases hi : b = i <;> by_cases hj : b = j <;> simp [hi, hj]
  have h1 := hg
  rw [Matrix.mul_add, Matrix.add_mul, hE] at h1
  exact add_right_cancel h1

omit [CharP F 2] in
theorem col_eq_of_mem_isometry {J : GL (Fin m) F} (hJ2 : J * J = 1) {a b : Fin m}
    (hJa : ∀ i, (J : Matrix (Fin m) (Fin m) F) i a = if i = b then 1 else 0)
    (hJb : ∀ i, (J : Matrix (Fin m) (Fin m) F) i b = if i = a then 1 else 0)
    {g : GL (Fin m) F} (hg : g ∈ matrixIsometryGroup (J : Matrix (Fin m) (Fin m) F))
    (hrow : ∀ j, (g : Matrix (Fin m) (Fin m) F) b j = (1 : Matrix (Fin m) (Fin m) F) b j)
    (i : Fin m) : (g : Matrix (Fin m) (Fin m) F) i a = (1 : Matrix (Fin m) (Fin m) F) i a := by
  have hinv : ∀ k, ((g⁻¹ : GL (Fin m) F) : Matrix (Fin m) (Fin m) F) b k =
      (1 : Matrix (Fin m) (Fin m) F) b k := by
    intro k
    have h1 : ((g : Matrix (Fin m) (Fin m) F) * ((g⁻¹ : GL (Fin m) F) :
        Matrix (Fin m) (Fin m) F)) b k = (1 : Matrix (Fin m) (Fin m) F) b k := by
      rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
    rw [mul_apply, Finset.sum_eq_single b (fun j _ hj => by
      rw [hrow j, one_apply_ne (Ne.symm hj), zero_mul]) (by simp), hrow b, one_apply_eq,
      one_mul] at h1
    exact h1
  have hJinv : J⁻¹ = J := inv_eq_of_mul_eq_one_right hJ2
  have hT := (mem_matrixIsometryGroup_iff_inverseTranspose J g).1 hg
  rw [hJinv] at hT
  have hT' := congrArg (fun x : GL (Fin m) F => (x : Matrix (Fin m) (Fin m) F)) hT
  simp only [GeneralLinearGroup.coe_inverseTranspose, Units.val_mul] at hT'
  have hJJ : (J : Matrix (Fin m) (Fin m) F) * J = 1 := by
    rw [← Units.val_mul, hJ2, Units.val_one]
  have hg' : (g : Matrix (Fin m) (Fin m) F) =
      J * ((g⁻¹ : GL (Fin m) F) : Matrix (Fin m) (Fin m) F)ᵀ * J := by
    rw [hT', ← Matrix.mul_assoc, ← Matrix.mul_assoc, hJJ, Matrix.one_mul, Matrix.mul_assoc, hJJ,
      Matrix.mul_one]
  have hJb' : (J : Matrix (Fin m) (Fin m) F) b a = 1 := by simp [hJa b]
  rw [hg', mul_apply, Finset.sum_eq_single b (fun l _ hl => by simp [hJa l, hl])
    (by simp), hJb', mul_one, mul_apply,
    Finset.sum_eq_single b (fun k _ hk => by
      rw [transpose_apply, hinv k, one_apply_ne (Ne.symm hk), mul_zero]) (by simp),
    transpose_apply, hinv b, one_apply_eq, mul_one, hJb i]
  rw [one_apply]

omit [CharP F 2] in
theorem mul_single_eq_single_mul {g : Matrix (Fin m) (Fin m) F} {a b : Fin m}
    (hrow : ∀ j, g b j = (1 : Matrix (Fin m) (Fin m) F) b j)
    (hcol : ∀ i, g i a = (1 : Matrix (Fin m) (Fin m) F) i a) :
    g * single a b 1 = single a b 1 * g := by
  ext i j
  by_cases hj : j = b
  · rw [hj, mul_single_apply_same, hcol, mul_one]
    by_cases hi : i = a
    · rw [hi, single_mul_apply_same, one_mul, hrow, one_apply_eq, one_apply_eq]
    · rw [single_mul_apply_of_ne (h := hi), one_apply_ne hi]
  · rw [mul_single_apply_of_ne (hbj := hj)]
    by_cases hi : i = a
    · rw [hi, single_mul_apply_same, one_mul, hrow, one_apply_ne (Ne.symm hj)]
    · rw [single_mul_apply_of_ne (h := hi)]

end Matrices

section Standard

variable {n : ℕ} {F : Type} [Field F] [CharP F 2]

variable (n F) in
@[expose] noncomputable def spBlockSwapGL : GL (Fin (2 * n)) F :=
  ⟨blockSwapJ (2 * n) n, blockSwapJ (2 * n) n, blockSwapJ_two_mul_mul_self n F,
    blockSwapJ_two_mul_mul_self n F⟩

theorem coe_spBlockSwapGL :
    ((spBlockSwapGL n F : GL (Fin (2 * n)) F) : Matrix (Fin (2 * n)) (Fin (2 * n)) F) =
      blockSwapJ (2 * n) n := rfl

theorem spBlockSwapGL_mul_self : spBlockSwapGL n F * spBlockSwapGL n F = 1 :=
  Units.ext (blockSwapJ_two_mul_mul_self n F)

omit [CharP F 2] in
theorem blockSwapJ_apply_inl (p : Fin n) (i : Fin (2 * n)) :
    (blockSwapJ (2 * n) n : Matrix (Fin (2 * n)) (Fin (2 * n)) F) i (spModelIdx n (Sum.inl p)) =
      if i = spModelIdx n (Sum.inr p) then 1 else 0 := by
  have hv := spModelIdx_inl_val p
  have hw := spModelIdx_inr_val p
  have hi := i.isLt
  have key : ((spModelIdx n (Sum.inl p) : ℕ) = i + n ∨ (i : ℕ) = spModelIdx n (Sum.inl p) + n) ↔
      i = spModelIdx n (Sum.inr p) := by
    rw [Fin.ext_iff, hv, hw]
    omega
  simp only [blockSwapJ, of_apply, key]

omit [CharP F 2] in
theorem blockSwapJ_apply_inr (p : Fin n) (i : Fin (2 * n)) :
    (blockSwapJ (2 * n) n : Matrix (Fin (2 * n)) (Fin (2 * n)) F) i (spModelIdx n (Sum.inr p)) =
      if i = spModelIdx n (Sum.inl p) then 1 else 0 := by
  have hv := spModelIdx_inl_val p
  have hw := spModelIdx_inr_val p
  have hi := i.isLt
  have key : ((spModelIdx n (Sum.inr p) : ℕ) = i + n ∨ (i : ℕ) = spModelIdx n (Sum.inr p) + n) ↔
      i = spModelIdx n (Sum.inl p) := by
    rw [Fin.ext_iff, hv, hw]
    omega
  simp only [blockSwapJ, of_apply, key]

omit [CharP F 2] in
theorem single_mul_blockSwapJ_two_mul (p : Fin n) :
    single (spModelIdx n (Sum.inl p)) (spModelIdx n (Sum.inr p)) (1 : F) *
        blockSwapJ (2 * n) n =
      single (spModelIdx n (Sum.inl p)) (spModelIdx n (Sum.inl p)) 1 := by
  ext i j
  by_cases hi : i = spModelIdx n (Sum.inl p)
  · rw [hi, single_mul_apply_same, one_mul, single_apply]
    have h1 : (blockSwapJ (2 * n) n : Matrix (Fin (2 * n)) (Fin (2 * n)) F)
        (spModelIdx n (Sum.inr p)) j =
          (blockSwapJ (2 * n) n : Matrix (Fin (2 * n)) (Fin (2 * n)) F) j
            (spModelIdx n (Sum.inr p)) := by
      rw [← transpose_apply (blockSwapJ (2 * n) n : Matrix (Fin (2 * n)) (Fin (2 * n)) F) j,
        CFSG.ComponentClassification.UnbalancedCatalog.blockSwapJ_transpose]
    rw [h1, blockSwapJ_apply_inr]
    by_cases hj : j = spModelIdx n (Sum.inl p) <;> simp [hj, eq_comm]
  · rw [single_mul_apply_of_ne (h := hi), single_apply, eq_comm, ite_eq_right_iff]
    exact fun h => absurd h.1.symm hi

omit [CharP F 2] in
theorem blockSwapJ_two_mul_mul_single (p : Fin n) :
    blockSwapJ (2 * n) n *
        single (spModelIdx n (Sum.inl p)) (spModelIdx n (Sum.inr p)) (1 : F) =
      single (spModelIdx n (Sum.inr p)) (spModelIdx n (Sum.inr p)) 1 := by
  ext i j
  by_cases hj : j = spModelIdx n (Sum.inr p)
  · rw [hj, mul_single_apply_same, mul_one, blockSwapJ_apply_inl, single_apply]
    by_cases hi : i = spModelIdx n (Sum.inr p) <;> simp [hi, eq_comm]
  · rw [mul_single_apply_of_ne (hbj := hj), single_apply, eq_comm, ite_eq_right_iff]
    exact fun h => absurd h.2.symm hj

theorem coe_spModelSL_siegDiag (p : Fin n) :
    ((spModelSL n F (siegDiag F p 1) : SpecialLinearGroup (Fin (2 * n)) F) :
        Matrix (Fin (2 * n)) (Fin (2 * n)) F) =
      1 + single (spModelIdx n (Sum.inl p)) (spModelIdx n (Sum.inr p)) 1 := by
  rw [coe_spModelSL, ← CFSG.LieType.Universal.Symplectic.SpExtras.mat_apply, siegDiag,
    mat_upperUnipotentSp]
  ext i j
  obtain ⟨s, rfl⟩ := (spModelIdx n).surjective i
  obtain ⟨s', rfl⟩ := (spModelIdx n).surjective j
  simp only [submatrix_apply, Equiv.symm_apply_apply, Matrix.add_apply, single_apply, one_apply,
    EmbeddingLike.apply_eq_iff_eq]
  rcases s with a | a <;> rcases s' with b | b <;>
    simp [fromBlocks, one_apply, single_apply, eq_comm]

end Standard

section Partner

variable {n : ℕ} {F : Type} [Field F] [Finite F] [CharP F 2]

omit [Finite F] in
theorem isCanonicalGram_spBlockSwapGL :
    CFSG.ComponentClassification.UnbalancedCatalog.IsCanonicalGram
      ((spBlockSwapGL n F : GL (Fin (2 * n)) F) : Matrix (Fin (2 * n)) (Fin (2 * n)) F) := by
  rw [coe_spBlockSwapGL]
  exact CFSG.ComponentClassification.UnbalancedCatalog.isCanonicalGram_blockSwapJ (two_mul n).symm

theorem conj_siegDiag_mul_graph_sq (hn : 2 ≤ n) (p : Fin n) :
    (MulAut.conj (spModelPSL n F (siegDiag F p 1)) *
      (conjAut (2 * n) F (spBlockSwapGL n F) * dualAut (2 * n) F)) ^ 2 = 1 := by
  set z := spModelPSL n F (siegDiag F p 1) with hz
  set β := conjAut (2 * n) F (spBlockSwapGL n F) * dualAut (2 * n) F with hβ
  have hβz : β z = z := conjAut_dualAut_spModelPSL hn coe_spBlockSwapGL _
  have hcomm : β * MulAut.conj z = MulAut.conj z * β := by rw [mulAut_mul_conj_eq_conj_apply_mul, hβz]
  have hz2 : z * z = 1 := by rw [hz, ← map_mul, siegDiag_one_mul_self, map_one]
  have hβ2 : β ^ 2 = 1 :=
    CFSG.ComponentClassification.UnbalancedCatalog.pureGraph_sq isCanonicalGram_spBlockSwapGL
  calc (MulAut.conj z * β) ^ 2 = MulAut.conj z * (β * MulAut.conj z) * β := by
        rw [sq]
        group
    _ = MulAut.conj (z * z) * β ^ 2 := by
        rw [hcomm, map_mul, sq]
        group
    _ = 1 := by rw [hz2, map_one, hβ2, one_mul]

omit [Finite F] in
theorem coe_toGL_spModelSL_siegDiag_mul_spBlockSwapGL (p : Fin n) :
    ((SpecialLinearGroup.toGL (spModelSL n F (siegDiag F p 1)) * spBlockSwapGL n F :
        GL (Fin (2 * n)) F) : Matrix (Fin (2 * n)) (Fin (2 * n)) F) =
      blockSwapJ (2 * n) n + single (spModelIdx n (Sum.inl p)) (spModelIdx n (Sum.inl p)) 1 := by
  rw [Units.val_mul, SpecialLinearGroup.coe_GL_coe_matrix, coe_spModelSL_siegDiag,
    coe_spBlockSwapGL, Matrix.add_mul, Matrix.one_mul, single_mul_blockSwapJ_two_mul]

omit [Finite F] in
theorem coe_inv_toGL_spModelSL_siegDiag_mul_spBlockSwapGL (p : Fin n) :
    (((SpecialLinearGroup.toGL (spModelSL n F (siegDiag F p 1)) * spBlockSwapGL n F)⁻¹ :
        GL (Fin (2 * n)) F) : Matrix (Fin (2 * n)) (Fin (2 * n)) F) =
      blockSwapJ (2 * n) n + single (spModelIdx n (Sum.inr p)) (spModelIdx n (Sum.inr p)) 1 := by
  have hZ2 : SpecialLinearGroup.toGL (spModelSL n F (siegDiag F p 1)) *
      SpecialLinearGroup.toGL (spModelSL n F (siegDiag F p 1)) = 1 := by
    rw [← map_mul, ← map_mul, siegDiag_one_mul_self, map_one, map_one]
  have hJinv : (spBlockSwapGL n F)⁻¹ = spBlockSwapGL n F :=
    inv_eq_of_mul_eq_one_right spBlockSwapGL_mul_self
  have hZinv : (SpecialLinearGroup.toGL (spModelSL n F (siegDiag F p 1)))⁻¹ =
      SpecialLinearGroup.toGL (spModelSL n F (siegDiag F p 1)) := inv_eq_of_mul_eq_one_right hZ2
  rw [_root_.mul_inv_rev, hJinv, hZinv, Units.val_mul, SpecialLinearGroup.coe_GL_coe_matrix,
    coe_spModelSL_siegDiag, coe_spBlockSwapGL, Matrix.mul_add, Matrix.mul_one,
    blockSwapJ_two_mul_mul_single]

theorem exists_normalForm_conj_siegDiag {f : ℕ} (hf : 1 ≤ f) (hF : Nat.card F = 2 ^ f)
    (hn : 2 ≤ n) (p : Fin n) :
    ∃ H' : GL (Fin (2 * n)) F,
      MulAut.conj (spModelPSL n F (siegDiag F p 1)) *
          (conjAut (2 * n) F (spBlockSwapGL n F) * dualAut (2 * n) F) =
        conjAut (2 * n) F H' * dualAut (2 * n) F * (conjAut (2 * n) F H')⁻¹ ∧
      ((SpecialLinearGroup.toGL (spModelSL n F (siegDiag F p 1)) * spBlockSwapGL n F :
          GL (Fin (2 * n)) F) : Matrix (Fin (2 * n)) (Fin (2 * n)) F) =
        (H' : Matrix (Fin (2 * n)) (Fin (2 * n)) F) * (H' : Matrix (Fin (2 * n)) (Fin (2 * n)) F)ᵀ := by
  set S : GL (Fin (2 * n)) F :=
    SpecialLinearGroup.toGL (spModelSL n F (siegDiag F p 1)) * spBlockSwapGL n F with hSdef
  have hS : MulAut.conj (spModelPSL n F (siegDiag F p 1)) *
      (conjAut (2 * n) F (spBlockSwapGL n F) * dualAut (2 * n) F) =
        conjAut (2 * n) F S * dualAut (2 * n) F := by
    rw [spModelPSL_apply, ← conjAut_toGL, ← mul_assoc, ← map_mul]
  have hsq := conj_siegDiag_mul_graph_sq (F := F) hn p
  rw [hS] at hsq
  obtain ⟨-, ⟨H', C', hSm, hconj, hC'⟩, -⟩ :=
    UnitaryHigher.even_linear_pure_graph_involution_normal_forms hf hF (by omega) S hsq
  rcases hC' with ⟨hC1, -⟩ | ⟨r, -, -, halt⟩
  · obtain rfl : C' = 1 := Units.ext hC1
    rw [map_one, one_mul] at hconj
    refine ⟨H', hS.trans hconj, ?_⟩
    rw [hSm, Units.val_one, Matrix.mul_one]
  · exfalso
    have h := halt (Pi.single (spModelIdx n (Sum.inl p)) 1)
    have hab : spModelIdx n (Sum.inl p) ≠ spModelIdx n (Sum.inr p) :=
      fun h' => Sum.inl_ne_inr ((spModelIdx n).injective h')
    rw [hSdef, coe_toGL_spModelSL_siegDiag_mul_spBlockSwapGL, mulVec_single_one, single_dotProduct,
      one_mul, col_apply, Matrix.add_apply, blockSwapJ_apply_inl, single_apply_same] at h
    simp only [hab, ↓reduceIte, zero_add] at h
    exact one_ne_zero h

theorem fixedSubgroup_conj_siegDiag_mul_graph {f : ℕ} (hf : 1 ≤ f) (hF : Nat.card F = 2 ^ f)
    (hn : 2 ≤ n) (p : Fin n) :
    fixedSubgroup (MulAut.conj (spModelPSL n F (siegDiag F p 1)) *
        (conjAut (2 * n) F (spBlockSwapGL n F) * dualAut (2 * n) F)) =
      (centralizer ({siegDiag F p 1} : Set (StatedSp n F))).map (spModelPSL n F) := by
  set z := siegDiag F p 1 with hz
  set a := spModelIdx n (Sum.inl p) with ha
  set b := spModelIdx n (Sum.inr p) with hb
  apply le_antisymm
  · obtain ⟨H', hconj, hSm⟩ := exists_normalForm_conj_siegDiag hf hF hn p
    intro y hy
    have hy' : (conjAut (2 * n) F H' * dualAut (2 * n) F * (conjAut (2 * n) F H')⁻¹) y = y := by
      rw [← hconj]
      exact hy
    set y' := (conjAut (2 * n) F H')⁻¹ y with hy'def
    have hδ : dualAut (2 * n) F y' = y' := by
      have h2 := hy'
      simp only [MulAut.mul_apply] at h2
      apply (conjAut (2 * n) F H').injective
      rw [hy'def, MulAut.apply_inv_self]
      exact h2
    obtain ⟨g₀, hg₀⟩ := proj_surjective (2 * n) F y'
    have hcomm : Commute (conjAut (2 * n) F 1 * dualAut (2 * n) F)
        (conjAut (2 * n) F (SpecialLinearGroup.toGL g₀)) := by
      rw [map_one, one_mul, conjAut_toGL, hg₀]
      exact commute_conj_of_apply_eq hδ
    obtain ⟨g₁, hg₁, hg₀₁⟩ := (CFSG.ComponentClassification.UnbalancedCatalog.commute_pureGraph_conjAut_iff
      (C := 1) (by rw [Units.val_one]; exact
        CFSG.ComponentClassification.UnbalancedCatalog.isCanonicalGram_one) (by omega) _).1 hcomm
    rw [Units.val_one] at hg₁
    have hdet : (g₁ : Matrix (Fin (2 * n)) (Fin (2 * n)) F).det = 1 :=
      CFSG.LocalAnalysis.ComponentInitial.FourGroupEvenCanonical.det_eq_one_of_mem
        (by rw [det_one]; exact one_ne_zero) hg₁
    set h₁ : SpecialLinearGroup (Fin (2 * n)) F := ⟨g₁, hdet⟩ with hh₁
    have hh₁GL : SpecialLinearGroup.toGL h₁ = g₁ := Units.ext rfl
    have hy'h : y' = proj (2 * n) F h₁ := by
      apply ProjectivePlane.conj_injective_projectiveSL (by omega)
      rw [← hg₀, ← conjAut_toGL, ← conjAut_toGL, hg₀₁, hh₁GL]
    set S : GL (Fin (2 * n)) F :=
      SpecialLinearGroup.toGL (spModelSL n F (siegDiag F p 1)) * spBlockSwapGL n F with hSdef
    set g' : GL (Fin (2 * n)) F := H' * g₁ * H'⁻¹ with hg'def
    have hiT1 : GeneralLinearGroup.inverseTranspose g₁ = g₁ := by
      have := (mem_matrixIsometryGroup_iff_inverseTranspose 1 g₁).1 (by rw [Units.val_one]; exact hg₁)
      rw [this, one_mul, inv_one, mul_one]
    have hSH : S = H' * (GeneralLinearGroup.inverseTranspose H')⁻¹ := by
      apply Units.ext
      rw [hSm, Units.val_mul, ← map_inv, GeneralLinearGroup.coe_inverseTranspose, inv_inv]
    have hg'S : g' ∈ matrixIsometryGroup ((S⁻¹ : GL (Fin (2 * n)) F) :
        Matrix (Fin (2 * n)) (Fin (2 * n)) F) := by
      rw [mem_matrixIsometryGroup_iff_inverseTranspose, hg'def, map_mul, map_mul, map_inv, hiT1,
        hSH]
      group
    rw [mem_matrixIsometryGroup, hSdef, coe_inv_toGL_spModelSL_siegDiag_mul_spBlockSwapGL] at hg'S
    have hJs : (blockSwapJ (2 * n) n : Matrix (Fin (2 * n)) (Fin (2 * n)) F)ᵀ =
        blockSwapJ (2 * n) n := CFSG.ComponentClassification.UnbalancedCatalog.blockSwapJ_transpose
    have hJd : ∀ i, (blockSwapJ (2 * n) n : Matrix (Fin (2 * n)) (Fin (2 * n)) F) i i = 0 :=
      CFSG.ComponentClassification.UnbalancedCatalog.blockSwapJ_apply_self (by omega)
    have hrow := row_eq_of_isometry_add_single hJs hJd b hg'S
    have hg'J : g' ∈ matrixIsometryGroup
        (blockSwapJ (2 * n) n : Matrix (Fin (2 * n)) (Fin (2 * n)) F) :=
      transpose_mul_mul_eq_of_isometry_add_single hJs hJd b hg'S
    have hcol := col_eq_of_mem_isometry (J := spBlockSwapGL n F) spBlockSwapGL_mul_self
      (blockSwapJ_apply_inl p) (blockSwapJ_apply_inr p) (by rw [coe_spBlockSwapGL]; exact hg'J)
      hrow
    set x' : StatedSp n F :=
      blockSwapIsometryEquivStatedSp (k := F) (two_mul n).symm ⟨g', hg'J⟩ with hx'def
    have hx'mat : ((spModelSL n F x' : SpecialLinearGroup (Fin (2 * n)) F) :
        Matrix (Fin (2 * n)) (Fin (2 * n)) F) = (g' : Matrix (Fin (2 * n)) (Fin (2 * n)) F) := by
      simp only [spModelSL, MonoidHom.coe_comp, Function.comp_apply, hx'def,
        MulEquiv.coe_toMonoidHom]
      rw [MulEquiv.symm_apply_apply]
      rfl
    have hyx : y = spModelPSL n F x' := by
      have h1 : y = conjAut (2 * n) F H' y' := by
        rw [hy'def, MulAut.apply_inv_self]
      rw [h1, hy'h, conjAut_proj, spModelPSL_apply]
      congr 1
      apply Subtype.ext
      rw [coe_slConjugation, hx'mat, hg'def, Units.val_mul, Units.val_mul, ← hh₁GL]
      rfl
    refine ⟨x', ?_, hyx.symm⟩
    rw [SetLike.mem_coe, mem_centralizer_singleton_iff]
    apply spModelSL_injective
    apply Subtype.ext
    rw [map_mul, map_mul, Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, hx'mat,
      coe_spModelSL_siegDiag, Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, Matrix.one_mul,
      mul_single_eq_single_mul hrow hcol]
  · rintro _ ⟨x, hx, rfl⟩
    have hxz : x * z = z * x := mem_centralizer_singleton_iff.1 hx
    change (MulAut.conj (spModelPSL n F z) *
      (conjAut (2 * n) F (spBlockSwapGL n F) * dualAut (2 * n) F)) (spModelPSL n F x) = _
    rw [MulAut.mul_apply, conjAut_dualAut_spModelPSL hn coe_spBlockSwapGL x, MulAut.conj_apply,
      ← map_mul, ← map_inv, ← map_mul, ← hxz, mul_inv_cancel_right]
    rfl

end Partner

section FieldMap

variable {K F : Type} [Field K] [Field F] {n : ℕ}

theorem statedSpMap_siegDiag (σ : K →+* F) (p : Fin n) :
    CFSG.SeitzReduction.F4Pilot.statedSpMap σ n (siegDiag K p 1) = siegDiag F p 1 := by
  apply CFSG.LieType.Universal.Symplectic.SpExtras.mat_injective
  rw [CFSG.LieType.Universal.Symplectic.SpExtras.mat_apply,
    CFSG.SeitzReduction.F4Pilot.coe_statedSpMap, CFSG.SeitzReduction.F4Pilot.coe_map_GL,
    ← CFSG.LieType.Universal.Symplectic.SpExtras.mat_apply, siegDiag, siegDiag,
    mat_upperUnipotentSp, mat_upperUnipotentSp]
  ext a b
  rcases a with i | i <;> rcases b with j | j <;> simp [fromBlocks, one_apply, single_apply]

theorem map_statedSpMap_centralizer_siegDiag (σ : K ≃+* F) (p : Fin n) :
    (centralizer ({siegDiag K p 1} : Set (StatedSp n K))).map
        (CFSG.SeitzReduction.F4Pilot.statedSpMap (σ : K →+* F) n) =
      centralizer ({siegDiag F p 1} : Set (StatedSp n F)) := by
  apply le_antisymm
  · rintro _ ⟨x, hx, rfl⟩
    rw [SetLike.mem_coe, mem_centralizer_singleton_iff] at hx
    rw [mem_centralizer_singleton_iff]
    rw [← statedSpMap_siegDiag (σ : K →+* F) p, ← map_mul, ← map_mul, hx]
  · intro x hx
    refine ⟨CFSG.SeitzReduction.F4Pilot.statedSpMap (σ.symm : F →+* K) n x, ?_,
      statedSpMap_symm_apply σ x⟩
    rw [mem_centralizer_singleton_iff] at hx
    rw [SetLike.mem_coe, mem_centralizer_singleton_iff]
    rw [← statedSpMap_siegDiag (σ.symm : F →+* K) p, ← map_mul, ← map_mul, hx]

end FieldMap

section Row

theorem mulAut_congr_trans_apply {X Y Z : Type*} [Group X] [Group Y] [Group Z] (e₁ : X ≃* Y)
    (e₂ : Y ≃* Z) (γ : MulAut X) :
    MulAut.congr (e₁.trans e₂) γ = MulAut.congr e₂ (MulAut.congr e₁ γ) := by
  ext x
  simp [MulAut.congr_apply]

theorem mulAut_congr_congr_symm_apply {X Y : Type*} [Group X] [Group Y] (e : X ≃* Y) (γ : MulAut Y) :
    MulAut.congr e (MulAut.congr e.symm γ) = γ := by
  ext x
  simp [MulAut.congr_apply]

theorem mulAut_congr_symm_congr_apply {X Y : Type*} [Group X] [Group Y] (e : X ≃* Y) (γ : MulAut X) :
    MulAut.congr e.symm (MulAut.congr e γ) = γ := by
  ext x
  simp [MulAut.congr_apply]

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {K : Type} [Field K] [Finite K]
  [CharP K 2]

open CFSG.Blueprint
open CFSG.ComponentClassification.CatLeafProof (fixedSubgroupCongrEquiv)

end Row

end CFSG.SeitzReduction.SymplecticPilot

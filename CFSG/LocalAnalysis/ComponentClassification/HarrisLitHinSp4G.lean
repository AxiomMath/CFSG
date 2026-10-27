module

public import CFSG.LocalAnalysis.ComponentClassification.HarrisLitHinSp4F
public import CFSG.LocalAnalysis.ComponentClassification.GSThmBCatalog7E6ClsA

public noncomputable section

namespace CFSG.ComponentClassification.HarrisLit.Hin

open CFSG Subgroup Matrix CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial
open SymplecticHigher SymplecticFlag
open CFSG.ComponentClassification.CatFactsSp4
open CFSG.ComponentClassification.GSThmB.Cat7E6 (b0)

variable {K : Type} [Field K]

theorem b0_mul_b0 (d : K) : b0 d * b0 d = d • 1 := by
  ext (i | i) (j | j) <;> fin_cases i <;> fin_cases j <;>
    simp [b0, Matrix.mul_apply, Fin.sum_univ_two]

theorem b0_symplectic (d : K) : (b0 d)ᵀ * formJ 2 K * b0 d = d • formJ 2 K := by
  rw [formJ_eq_blk]
  ext (i | i) (j | j) <;> fin_cases i <;> fin_cases j <;>
    simp [b0, blk, diag2, J₁, fromBlocks_multiply, fromBlocks_transpose, Matrix.mul_apply,
      Fin.sum_univ_two]

theorem isUnit_det_b0 {d : K} (hd0 : d ≠ 0) : IsUnit (b0 d).det := by
  have h := congrArg Matrix.det (b0_mul_b0 d)
  rw [det_mul, det_smul, det_one, mul_one, Fintype.card_sum, Fintype.card_fin] at h
  exact isUnit_iff_ne_zero.mpr (fun h0 => by rw [h0, mul_zero] at h; exact pow_ne_zero _ hd0 h.symm)

@[expose] def b0gsp {d : K} (hd0 : d ≠ 0) : gsp 2 K :=
  ⟨nonsingInvUnit (b0 d) (isUnit_det_b0 hd0), ⟨Units.mk0 d hd0, by
    rw [Units.val_mk0]
    exact b0_symplectic d⟩⟩

theorem coe_b0gsp {d : K} (hd0 : d ≠ 0) :
    (((b0gsp hd0 : gsp 2 K) : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) =
      b0 d := rfl

@[expose] def twistD (d : K) (g : Matrix (Fin 2) (Fin 2) K) : Matrix (Fin 2) (Fin 2) K :=
  diag2 1 d * g * diag2 1 d⁻¹

theorem twistD_mul {d : K} (hd0 : d ≠ 0) (g h : Matrix (Fin 2) (Fin 2) K) :
    twistD d (g * h) = twistD d g * twistD d h := by
  have hD : diag2 (1 : K) d⁻¹ * diag2 1 d = 1 := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [diag2, Matrix.mul_apply, Fin.sum_univ_two, hd0]
  simp only [twistD, Matrix.mul_assoc]
  rw [← Matrix.mul_assoc (diag2 1 d⁻¹) (diag2 1 d), hD, Matrix.one_mul]

theorem det_twistD {d : K} (hd0 : d ≠ 0) (g : Matrix (Fin 2) (Fin 2) K) :
    (twistD d g).det = g.det := by
  simp only [twistD, det_mul]
  simp only [diag2, det_fin_two_of, one_mul, mul_zero, sub_zero]
  field_simp

theorem twistD_eq {d : K} (hd0 : d ≠ 0) (g : Matrix (Fin 2) (Fin 2) K) :
    twistD d g = !![g 0 0, g 0 1 * d⁻¹; d * g 1 0, g 1 1] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [twistD, diag2, Matrix.mul_apply, Fin.sum_univ_two, Matrix.vecMul, dotProduct]
  field_simp

theorem twistD_one {d : K} (hd0 : d ≠ 0) : twistD d (1 : Matrix (Fin 2) (Fin 2) K) = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [twistD, diag2, Matrix.mul_apply, Fin.sum_univ_two, hd0]

theorem twistD_neg_one {d : K} (hd0 : d ≠ 0) : twistD d (-1 : Matrix (Fin 2) (Fin 2) K) = -1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [twistD, diag2, Matrix.mul_apply, Fin.sum_univ_two, hd0]

@[expose] def blkD {d : K} (hd0 : d ≠ 0) : Matrix.SpecialLinearGroup (Fin 2) K →* StatedSp 2 K where
  toFun g := toSp (blk (g : Matrix (Fin 2) (Fin 2) K) (twistD d g))
    (blk_symplectic_of_det g.2 (by rw [det_twistD hd0]; exact g.2))
  map_one' := sp_ext (by simp [twistD_one hd0, blk_one_one])
  map_mul' g h := sp_ext (by simp [blk_mul, twistD_mul hd0])

theorem coe_blkD {d : K} (hd0 : d ≠ 0) (g : Matrix.SpecialLinearGroup (Fin 2) K) :
    (((blkD hd0 g : StatedSp 2 K) : GL (Fin 2 ⊕ Fin 2) K) :
      Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) = blk (g : Matrix (Fin 2) (Fin 2) K) (twistD d g) :=
  rfl

theorem b0_mul_blkD {d : K} (hd0 : d ≠ 0) (g : Matrix (Fin 2) (Fin 2) K) :
    b0 d * blk g (twistD d g) = blk g (twistD d g) * b0 d := by
  rw [twistD_eq hd0]
  ext (i | i) (j | j) <;> fin_cases i <;> fin_cases j <;>
    simp [b0, blk, diag2, Matrix.mul_apply, Fin.sum_univ_two] <;> field_simp

theorem b0_mul_T1 (d : K) : b0 d * blk 1 (-1) = -(blk 1 (-1) * b0 d) := by
  ext (i | i) (j | j) <;> fin_cases i <;> fin_cases j <;>
    simp [b0, blk, diag2, Matrix.mul_apply, Fin.sum_univ_two]

theorem T1_mul_blkD {d : K} (hd0 : d ≠ 0) (g : Matrix.SpecialLinearGroup (Fin 2) K) :
    T1 K * blkD hd0 g = blkD hd0 g * T1 K := by
  apply sp_ext
  rw [Subgroup.coe_mul, Subgroup.coe_mul, Units.val_mul, Units.val_mul, coe_T1, coe_blkD, blk_mul,
    blk_mul, Matrix.one_mul, Matrix.mul_one, Matrix.neg_mul, Matrix.mul_neg, Matrix.one_mul,
    Matrix.mul_one]

theorem ker_proj_comp_blkD {d : K} (hd0 : d ≠ 0) :
    ((proj 2 K).comp (blkD hd0)).ker = center (Matrix.SpecialLinearGroup (Fin 2) K) := by
  ext g
  rw [MonoidHom.mem_ker, MonoidHom.comp_apply, ← MonoidHom.mem_ker, ker_proj, mem_spScalars_iff,
    coe_blkD]
  constructor
  · rintro (h | h)
    · rw [← blk_one_one] at h
      exact mem_center_of_eq_smul (r := 1) (by rw [(blk_injective _ _ _ _ h).1, one_smul])
    · rw [← blk_neg_one_neg_one] at h
      exact mem_center_of_eq_smul (r := -1) (by rw [(blk_injective _ _ _ _ h).1, neg_one_smul])
  · intro hg
    obtain ⟨r, hr⟩ := eq_smul_of_mem_center hg
    have hr2 : r * r = 1 := by
      have h := g.2
      rw [hr, det_smul, det_one, mul_one, Fintype.card_fin, pow_two] at h
      exact h
    have hr' : r = 1 ∨ r = -1 := by
      have : (r - 1) * (r + 1) = 0 := by linear_combination hr2
      rcases mul_eq_zero.mp this with h | h
      · left; linear_combination h
      · right; linear_combination h
    rcases hr' with rfl | rfl
    · left
      rw [hr, one_smul, twistD_one hd0, blk_one_one]
    · right
      rw [hr, neg_one_smul, twistD_neg_one hd0, blk_neg_one_neg_one]

theorem exists_elemTwo_b0 [Finite K] (hodd : Odd (Nat.card K)) (h4 : 4 ≤ Nat.card K) {d : K}
    (hd0 : d ≠ 0) :
    ∃ E : Subgroup (StatedProj (StatedSp 2 K)), E ≤ fixOf (conjAut 2 K (b0gsp hd0)) ∧
      ElemTwo E ∧ 8 ≤ Nat.card E := by
  have h2 : (2 : K) ≠ 0 := two_ne_zero_of_odd_card hodd
  set ψ := (proj 2 K).comp (blkD hd0) with hψ
  have hker := ker_proj_comp_blkD hd0
  obtain ⟨E, hEr, hE, hE4⟩ := exists_E4_of_hom h2 hodd ψ hker
  let eR : Matrix.ProjectiveSpecialLinearGroup (Fin 2) K ≃* ψ.range :=
    (QuotientGroup.quotientMulEquivOfEq hker.symm).trans (QuotientGroup.quotientKerEquivRange ψ)
  have hRs : IsSimpleGroup ψ.range :=
    eR.isSimpleGroup_congr.mp (Matrix.ProjectiveSpecialLinearGroup.rank_two_simple h4)
  have hRnab : ∃ x y : ψ.range, x * y ≠ y * x := by
    obtain ⟨x, hx, y, hy, hxy⟩ := exists_mul_ne_of_isQuasisimple
      (isQuasisimple_range_comp h4 (blkD hd0) hker)
    exact ⟨⟨x, hx⟩, ⟨y, hy⟩, fun h => hxy (congrArg Subtype.val h)⟩
  have hfix : ∀ g : StatedSp 2 K,
      ((b0gsp hd0 : gsp 2 K) : GL (Fin 2 ⊕ Fin 2) K) * g = g * (b0gsp hd0 : gsp 2 K) →
      proj 2 K g ∈ fixOf (conjAut 2 K (b0gsp hd0)) := by
    intro g hg
    change conjAut 2 K (b0gsp hd0) (proj 2 K g) = proj 2 K g
    rw [conjAut_proj]
    congr 1
    apply Subtype.ext
    rw [coe_conjSp, hg, mul_inv_cancel_right]
  have hRfix : ψ.range ≤ fixOf (conjAut 2 K (b0gsp hd0)) := by
    rintro _ ⟨g, rfl⟩
    refine hfix _ (Units.ext ?_)
    rw [Units.val_mul, Units.val_mul, coe_b0gsp, coe_blkD, b0_mul_blkD hd0]
  have hu1 : u1 K ∈ fixOf (conjAut 2 K (b0gsp hd0)) := by
    change conjAut 2 K (b0gsp hd0) (proj 2 K (T1 K)) = proj 2 K (T1 K)
    rw [conjAut_proj]
    apply proj_eq_of_coe_eq_neg
    have hA : ((b0gsp hd0 : gsp 2 K) : GL (Fin 2 ⊕ Fin 2) K) * T1 K =
        -(((T1 K : StatedSp 2 K) : GL (Fin 2 ⊕ Fin 2) K) * (b0gsp hd0 : gsp 2 K)) := by
      apply Units.ext
      rw [Units.val_mul, Units.val_neg, Units.val_mul, coe_b0gsp, coe_T1, b0_mul_T1]
    rw [coe_conjSp, hA, neg_mul, mul_inv_cancel_right, Units.val_neg]
  have hB := elemTwo_zpowers (u1_mul_u1 (K := K))
  have hB2 := card_zpowers_of_sq (u1_mul_u1 (K := K)) (u1_ne_one h2)
  have hBR : ∀ b ∈ zpowers (u1 K), ∀ r ∈ ψ.range, b * r = r * b := by
    intro b hb r hr
    have hle : zpowers (u1 K) ≤ centralizer (ψ.range : Set _) := by
      refine (zpowers_le).mpr ?_
      rw [mem_centralizer_iff]
      rintro _ ⟨g, rfl⟩
      rw [hψ, MonoidHom.comp_apply, u1, ← map_mul, ← map_mul, T1_mul_blkD hd0]
    exact (mem_centralizer_iff.mp (hle hb) r hr).symm
  obtain ⟨hEB, hcard⟩ := elemTwo_of_centralizer hRs hRnab hEr hE hB hBR
  refine ⟨_, sup_le (hEr.trans hRfix) ((zpowers_le).mpr hu1), hEB, ?_⟩
  calc 8 = 4 * 2 := by norm_num
    _ ≤ Nat.card E * Nat.card (zpowers (u1 K)) := by rw [hB2]; exact Nat.mul_le_mul_right 2 hE4
    _ ≤ _ := hcard

end CFSG.ComponentClassification.HarrisLit.Hin

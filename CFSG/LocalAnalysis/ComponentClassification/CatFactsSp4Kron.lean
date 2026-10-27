module

public import CFSG.LocalAnalysis.ComponentInitial.SymplecticHigherAutomorphismData

public noncomputable section

namespace CFSG.ComponentClassification.CatFactsSp4

open Matrix CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial
open SymplecticHigher SymplecticFlag

variable {K : Type} [Field K]

@[expose] def J₁ : Matrix (Fin 2) (Fin 2) K := !![0, 1; -1, 0]

@[expose] def kron (g h : Matrix (Fin 2) (Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K :=
  fromBlocks (g 0 0 • h) (g 0 1 • h) (g 1 0 • h) (g 1 1 • h)

theorem kron_mul (g h g' h' : Matrix (Fin 2) (Fin 2) K) :
    kron g h * kron g' h' = kron (g * g') (h * h') := by
  simp only [kron, fromBlocks_multiply, Matrix.smul_mul, Matrix.mul_smul, smul_smul, ← add_smul,
    Matrix.mul_apply, Fin.sum_univ_two]
  congr 1 <;> congr 1 <;> ring

theorem kron_transpose (g h : Matrix (Fin 2) (Fin 2) K) : (kron g h)ᵀ = kron gᵀ hᵀ := by
  simp only [kron, fromBlocks_transpose, transpose_smul, transpose_apply]

theorem kron_one_one : kron (1 : Matrix (Fin 2) (Fin 2) K) 1 = 1 := by
  rw [kron, ← fromBlocks_one]
  simp

theorem kron_smul_left (c : K) (g h : Matrix (Fin 2) (Fin 2) K) :
    kron (c • g) h = kron g (c • h) := by
  simp only [kron, Matrix.smul_apply, smul_eq_mul, smul_smul]
  congr 1 <;> rw [mul_comm]

theorem formJ_eq_kron : formJ 2 K = kron J₁ 1 := by
  simp [formJ, kron, J₁]

theorem transpose_mul_J₁_mul {R : Type*} [CommRing R] (g : Matrix (Fin 2) (Fin 2) R) :
    gᵀ * !![0, 1; -1, 0] * g = g.det • !![0, 1; -1, 0] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, det_fin_two] <;> ring

theorem kron_left_injective (X Y : Matrix (Fin 2) (Fin 2) K) (h : kron J₁ X = kron J₁ Y) :
    X = Y := by
  have := (fromBlocks_inj.mp h).2.1
  simpa [J₁] using this

theorem kron_symplectic_iff (g h : Matrix (Fin 2) (Fin 2) K) :
    (kron g h)ᵀ * formJ 2 K * kron g h = formJ 2 K ↔ g.det • (hᵀ * h) = 1 := by
  rw [formJ_eq_kron, kron_transpose, kron_mul, kron_mul, Matrix.mul_one,
    show gᵀ * J₁ * g = g.det • J₁ from transpose_mul_J₁_mul g, kron_smul_left]
  exact ⟨kron_left_injective _ _, fun h' => by rw [h']⟩

@[expose] def diag2 (a b : K) : Matrix (Fin 2) (Fin 2) K := !![a, 0; 0, b]

@[expose] def blk (g h : Matrix (Fin 2) (Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K :=
  fromBlocks (diag2 (g 0 0) (h 0 0)) (diag2 (g 0 1) (h 0 1)) (diag2 (g 1 0) (h 1 0))
    (diag2 (g 1 1) (h 1 1))

theorem diag2_mul (a b c d : K) : diag2 a b * diag2 c d = diag2 (a * c) (b * d) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [diag2]

theorem diag2_add (a b c d : K) : diag2 a b + diag2 c d = diag2 (a + c) (b + d) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [diag2]

theorem blk_mul (g h g' h' : Matrix (Fin 2) (Fin 2) K) :
    blk g h * blk g' h' = blk (g * g') (h * h') := by
  simp only [blk, fromBlocks_multiply, diag2_mul, diag2_add, Matrix.mul_apply, Fin.sum_univ_two]

theorem blk_transpose (g h : Matrix (Fin 2) (Fin 2) K) : (blk g h)ᵀ = blk gᵀ hᵀ := by
  have : ∀ a b : K, (diag2 a b)ᵀ = diag2 a b := fun a b => by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [diag2]
  simp only [blk, fromBlocks_transpose, this, transpose_apply]

theorem blk_one_one : blk (1 : Matrix (Fin 2) (Fin 2) K) 1 = 1 := by
  rw [← fromBlocks_one]
  simp only [blk]
  congr 1 <;> ext i j <;> fin_cases i <;> fin_cases j <;> simp [diag2]

theorem formJ_eq_blk : formJ 2 K = blk J₁ J₁ := by
  simp only [formJ, blk, J₁]
  congr 1 <;> ext i j <;> fin_cases i <;> fin_cases j <;> simp [diag2]

theorem blk_injective (g h g' h' : Matrix (Fin 2) (Fin 2) K) (hb : blk g h = blk g' h') :
    g = g' ∧ h = h' := by
  obtain ⟨h1, h2, h3, h4⟩ := fromBlocks_inj.mp hb
  have e : ∀ {a b c d : K}, diag2 a b = diag2 c d → a = c ∧ b = d := fun he =>
    ⟨by simpa [diag2] using congrFun (congrFun he 0) 0,
      by simpa [diag2] using congrFun (congrFun he 1) 1⟩
  refine ⟨?_, ?_⟩ <;> ext i j <;> fin_cases i <;> fin_cases j <;>
    first | exact (e h1).1 | exact (e h1).2 | exact (e h2).1 | exact (e h2).2 |
      exact (e h3).1 | exact (e h3).2 | exact (e h4).1 | exact (e h4).2

theorem blk_symplectic_iff (g h : Matrix (Fin 2) (Fin 2) K) :
    (blk g h)ᵀ * formJ 2 K * blk g h = formJ 2 K ↔ g.det = 1 ∧ h.det = 1 := by
  rw [formJ_eq_blk, blk_transpose, blk_mul, blk_mul,
    show gᵀ * J₁ * g = g.det • J₁ from transpose_mul_J₁_mul g,
    show hᵀ * J₁ * h = h.det • J₁ from transpose_mul_J₁_mul h]
  constructor
  · intro hb
    obtain ⟨h1, h2⟩ := blk_injective _ _ _ _ hb
    exact ⟨by simpa [J₁] using congrFun (congrFun h1 0) 1,
      by simpa [J₁] using congrFun (congrFun h2 0) 1⟩
  · rintro ⟨h1, h2⟩
    rw [h1, h2, one_smul]

theorem formJ_mul_formJ : formJ 2 K * formJ 2 K = -1 := by
  rw [formJ, fromBlocks_multiply, ← fromBlocks_one, fromBlocks_neg]
  simp

theorem isUnit_det_formJ : IsUnit (formJ 2 K).det := by
  have h := congrArg Matrix.det (formJ_mul_formJ (K := K))
  rw [det_mul, det_neg, det_one, Fintype.card_sum, Fintype.card_fin] at h
  norm_num at h
  exact isUnit_iff_ne_zero.mpr (left_ne_zero_of_mul_eq_one h)

theorem isUnit_det_of_symplectic {A : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K}
    (hA : Aᵀ * formJ 2 K * A = formJ 2 K) : IsUnit A.det := by
  have h := congrArg Matrix.det hA
  rw [det_mul, det_mul, det_transpose] at h
  have hJ := isUnit_det_formJ (K := K)
  have h2 : A.det * A.det = 1 := by
    have h3 : (A.det * A.det - 1) * (formJ 2 K).det = 0 := by linear_combination h
    exact sub_eq_zero.mp ((mul_eq_zero.mp h3).resolve_right hJ.ne_zero)
  exact isUnit_iff_ne_zero.mpr (left_ne_zero_of_mul_eq_one h2)

@[expose] def toSp (A : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K)
    (hA : Aᵀ * formJ 2 K * A = formJ 2 K) : StatedSp 2 K :=
  ⟨nonsingInvUnit A (isUnit_det_of_symplectic hA), SymplecticTorusWeyl.mem_statedSp_iff.mpr hA⟩

@[simp] theorem coe_toSp (A : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K)
    (hA : Aᵀ * formJ 2 K * A = formJ 2 K) :
    (((toSp A hA : StatedSp 2 K) : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K)
      = A := rfl

theorem symplectic_of_mem (g : StatedSp 2 K) :
    ((g : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K)ᵀ * formJ 2 K *
      ((g : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) = formJ 2 K :=
  SymplecticTorusWeyl.mem_statedSp_iff.mp g.2

theorem sp_ext {x y : StatedSp 2 K}
    (h : ((x : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) =
      ((y : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K)) : x = y :=
  Subtype.ext (Units.ext h)

theorem mem_spScalars_iff (g : StatedSp 2 K) :
    g ∈ spScalars 2 K ↔
      ((g : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) = 1 ∨
        ((g : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) = -1 := by
  rw [Subgroup.mem_subgroupOf, StatedScalars, MonoidHom.mem_range]
  constructor
  · rintro ⟨c, hc⟩
    have hg : ((g : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) =
        (c : K) • 1 := by
      rw [← hc, GeneralLinearGroup.coe_scalar, smul_one_eq_diagonal]
      rfl
    have hs := symplectic_of_mem g
    simp only [hg, transpose_smul, transpose_one, Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul,
      Matrix.mul_one, smul_smul] at hs
    have hc2 : (c : K) * c = 1 := by
      have := congrFun (congrFun hs (Sum.inl 0)) (Sum.inr 0)
      simpa [formJ] using this
    rcases mul_self_eq_one_iff.mp hc2 with h1 | h1
    · left
      rw [hg, h1, one_smul]
    · right
      rw [hg, h1, neg_smul, one_smul]
  · rintro (h1 | h1)
    · exact ⟨1, Units.ext (by rw [map_one, Units.val_one, h1])⟩
    · refine ⟨-1, Units.ext ?_⟩
      rw [h1, GeneralLinearGroup.coe_scalar, Units.val_neg, Units.val_one]
      ext i j
      by_cases hij : i = j <;> simp [hij, Matrix.neg_apply, one_apply]

end CFSG.ComponentClassification.CatFactsSp4

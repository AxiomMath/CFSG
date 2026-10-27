module

public import CFSG.RankThree.PartTwo.Sec4.Census.Item44RankTwoX

public section

namespace CFSG.ComponentClassification.GSThmB.X11.E8

open Matrix Subgroup CFSG.Assembly.LowTwoRank

variable {F : Type} [Field F]

@[expose] def s2 : Matrix (Fin 2) (Fin 2) F := !![1, 0; 0, -1]

@[expose] def w2 : Matrix (Fin 2) (Fin 2) F := !![0, 1; 1, 0]

@[expose] def mD : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F := fromBlocks s2 0 0 s2

@[expose] def mW : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F := fromBlocks w2 0 0 w2

@[expose] def mJ : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F := fromBlocks 0 1 (-1) 0

theorem s2_mul_self : (s2 : Matrix (Fin 2) (Fin 2) F) * s2 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [s2]

theorem w2_mul_self : (w2 : Matrix (Fin 2) (Fin 2) F) * w2 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [w2]

theorem s2_mul_w2 : (s2 : Matrix (Fin 2) (Fin 2) F) * w2 = -(w2 * s2) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [s2, w2]

theorem s2_transpose : (s2 : Matrix (Fin 2) (Fin 2) F)ᵀ = s2 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [s2]

theorem w2_transpose : (w2 : Matrix (Fin 2) (Fin 2) F)ᵀ = w2 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [w2]

theorem mD_mul_self : (mD : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) * mD = 1 := by
  rw [mD, fromBlocks_multiply, s2_mul_self, ← fromBlocks_one]
  simp

theorem mW_mul_self : (mW : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) * mW = 1 := by
  rw [mW, fromBlocks_multiply, w2_mul_self, ← fromBlocks_one]
  simp

theorem mJ_mul_self : (mJ : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) * mJ = -1 := by
  rw [mJ, fromBlocks_multiply, ← fromBlocks_one, fromBlocks_neg]
  simp

theorem mJ_mul_neg : (mJ : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) * -mJ = 1 := by
  rw [mul_neg, mJ_mul_self, neg_neg]

theorem neg_mul_mJ : -(mJ : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) * mJ = 1 := by
  rw [neg_mul, mJ_mul_self, neg_neg]

theorem mD_mul_mW : (mD : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) * mW = -(mW * mD) := by
  rw [mD, mW, fromBlocks_multiply, fromBlocks_multiply, fromBlocks_neg, s2_mul_w2]
  simp

theorem mD_mul_mJ : (mD : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) * mJ = mJ * mD := by
  rw [mD, mJ, fromBlocks_multiply, fromBlocks_multiply]
  simp

theorem mW_mul_mJ : (mW : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) * mJ = mJ * mW := by
  rw [mW, mJ, fromBlocks_multiply, fromBlocks_multiply]
  simp

theorem mD_sp : (mD : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F)ᵀ * fromBlocks 0 1 (-1) 0 * mD =
    fromBlocks 0 1 (-1) 0 := by
  rw [mD, fromBlocks_transpose, fromBlocks_multiply, fromBlocks_multiply, s2_transpose]
  simp [s2_mul_self]

theorem mW_sp : (mW : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F)ᵀ * fromBlocks 0 1 (-1) 0 * mW =
    fromBlocks 0 1 (-1) 0 := by
  rw [mW, fromBlocks_transpose, fromBlocks_multiply, fromBlocks_multiply, w2_transpose]
  simp [w2_mul_self]

theorem mJ_sp : (mJ : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F)ᵀ * fromBlocks 0 1 (-1) 0 * mJ =
    fromBlocks 0 1 (-1) 0 := by
  rw [mJ, fromBlocks_transpose, fromBlocks_multiply, fromBlocks_multiply]
  simp

@[expose] def gD : GL (Fin 2 ⊕ Fin 2) F := ⟨mD, mD, mD_mul_self, mD_mul_self⟩

@[expose] def gW : GL (Fin 2 ⊕ Fin 2) F := ⟨mW, mW, mW_mul_self, mW_mul_self⟩

@[expose] def gJ : GL (Fin 2 ⊕ Fin 2) F := ⟨mJ, -mJ, mJ_mul_neg, neg_mul_mJ⟩

theorem gD_mem : (gD : GL (Fin 2 ⊕ Fin 2) F) ∈ StatedSp 2 F := subset_closure mD_sp

theorem gW_mem : (gW : GL (Fin 2 ⊕ Fin 2) F) ∈ StatedSp 2 F := subset_closure mW_sp

theorem gJ_mem : (gJ : GL (Fin 2 ⊕ Fin 2) F) ∈ StatedSp 2 F := subset_closure mJ_sp

abbrev img (g : GL (Fin 2 ⊕ Fin 2) F) (hg : g ∈ StatedSp 2 F) : StatedProj (StatedSp 2 F) :=
  QuotientGroup.mk (⟨g, hg⟩ : StatedSp 2 F)

theorem exists_scalar_of_img_eq_one {g : GL (Fin 2 ⊕ Fin 2) F} {hg : g ∈ StatedSp 2 F}
    (h : img g hg = 1) : ∃ c : F, (g : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) = scalar _ c := by
  rw [img, QuotientGroup.eq_one_iff, mem_subgroupOf] at h
  obtain ⟨c, hc⟩ := h
  refine ⟨c, ?_⟩
  have h1 := congrArg Units.val hc
  rw [GeneralLinearGroup.coe_scalar] at h1
  exact h1.symm

theorem img_eq_of_neg {g h : GL (Fin 2 ⊕ Fin 2) F} {hg : g ∈ StatedSp 2 F} {hh : h ∈ StatedSp 2 F}
    (e : (g : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) = -(h : Matrix _ _ F)) :
    img g hg = img h hh := by
  have key : ((g⁻¹ * h : GL (Fin 2 ⊕ Fin 2) F) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) =
      -1 := by
    have h1 : (g : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) *
        ((g⁻¹ * h : GL (Fin 2 ⊕ Fin 2) F) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) =
        (g : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) * (-1) := by
      rw [Units.val_mul, ← mul_assoc, Units.mul_inv, one_mul, mul_neg_one, e, neg_neg]
    exact (Units.isUnit g).mul_left_cancel h1
  rw [img, img, QuotientGroup.eq, mem_subgroupOf]
  refine ⟨-1, Units.ext ?_⟩
  rw [GeneralLinearGroup.coe_scalar]
  change scalar _ ((-1 : Fˣ) : F) =
    ((g⁻¹ * h : GL (Fin 2 ⊕ Fin 2) F) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F)
  rw [key]
  ext i j
  by_cases hij : i = j
  · subst hij
    simp [scalar_apply]
  · simp [scalar_apply, hij]

theorem img_eq_of_eq {g h : GL (Fin 2 ⊕ Fin 2) F} {hg : g ∈ StatedSp 2 F}
    {hh : h ∈ StatedSp 2 F} (e : g = h) : img g hg = img h hh := by
  subst e
  rfl

theorem img_mul {g h : GL (Fin 2 ⊕ Fin 2) F} (hg : g ∈ StatedSp 2 F) (hh : h ∈ StatedSp 2 F) :
    img g hg * img h hh = img (g * h) (mul_mem hg hh) := rfl

theorem img_one : img (1 : GL (Fin 2 ⊕ Fin 2) F) (one_mem _) = 1 := rfl

abbrev xD : StatedProj (StatedSp 2 F) := img gD gD_mem

abbrev xW : StatedProj (StatedSp 2 F) := img gW gW_mem

abbrev xJ : StatedProj (StatedSp 2 F) := img gJ gJ_mem

theorem xD_mul_self : (xD : StatedProj (StatedSp 2 F)) * xD = 1 := by
  rw [img_mul, ← img_one]
  exact img_eq_of_eq (Units.ext mD_mul_self)

theorem xW_mul_self : (xW : StatedProj (StatedSp 2 F)) * xW = 1 := by
  rw [img_mul, ← img_one]
  exact img_eq_of_eq (Units.ext mW_mul_self)

theorem xJ_mul_self : (xJ : StatedProj (StatedSp 2 F)) * xJ = 1 := by
  rw [img_mul, ← img_one]
  refine img_eq_of_neg ?_
  change mJ * mJ = -(1 : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F)
  exact mJ_mul_self

theorem xD_mul_xW : (xD : StatedProj (StatedSp 2 F)) * xW = xW * xD := by
  rw [img_mul, img_mul]
  exact img_eq_of_neg mD_mul_mW

theorem xD_mul_xJ : (xD : StatedProj (StatedSp 2 F)) * xJ = xJ * xD := by
  rw [img_mul, img_mul]
  exact img_eq_of_eq (Units.ext mD_mul_mJ)

theorem xW_mul_xJ : (xW : StatedProj (StatedSp 2 F)) * xJ = xJ * xW := by
  rw [img_mul, img_mul]
  exact img_eq_of_eq (Units.ext mW_mul_mJ)

theorem scalar_apply' (c : F) (i j : Fin 2 ⊕ Fin 2) :
    (scalar (Fin 2 ⊕ Fin 2) c : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) i j =
      if i = j then c else 0 := by
  simp [scalar_apply, diagonal_apply]

theorem independent (h2 : (2 : F) ≠ 0) (a b c : ZMod 2) :
    (xD : StatedProj (StatedSp 2 F)) ^ a.val * xW ^ b.val * xJ ^ c.val = 1 →
      a = 0 ∧ b = 0 ∧ c = 0 := by
  have h1 : (1 : F) ≠ -1 := fun h => h2 (by linear_combination h)
  have hv : ∀ t : ZMod 2, t = 0 ∨ t = 1 := by decide
  have e0 : (0 : ZMod 2).val = 0 := rfl
  have e1 : (1 : ZMod 2).val = 1 := rfl
  intro h
  rcases hv a with rfl | rfl <;> rcases hv b with rfl | rfl <;> rcases hv c with rfl | rfl <;>
    simp only [e0, e1, pow_zero, pow_one, one_mul, mul_one] at h
  · exact ⟨rfl, rfl, rfl⟩
  all_goals exfalso
  · obtain ⟨d, hd⟩ := exists_scalar_of_img_eq_one h
    have := congrFun (congrFun hd (.inl 0)) (.inr 0)
    simp [gJ, mJ, scalar_apply'] at this
  · obtain ⟨d, hd⟩ := exists_scalar_of_img_eq_one h
    have := congrFun (congrFun hd (.inl 0)) (.inl 1)
    simp [gW, mW, w2, scalar_apply'] at this
  · rw [img_mul] at h
    obtain ⟨d, hd⟩ := exists_scalar_of_img_eq_one h
    have := congrFun (congrFun hd (.inl 0)) (.inr 1)
    simp [gW, gJ, mW, mJ, w2, fromBlocks_multiply, scalar_apply'] at this
  · obtain ⟨d, hd⟩ := exists_scalar_of_img_eq_one h
    have e0 := congrFun (congrFun hd (.inl 0)) (.inl 0)
    have e1 := congrFun (congrFun hd (.inl 1)) (.inl 1)
    simp [gD, mD, s2, scalar_apply'] at e0 e1
    exact h1 (e0.trans e1.symm)
  · rw [img_mul] at h
    obtain ⟨d, hd⟩ := exists_scalar_of_img_eq_one h
    have := congrFun (congrFun hd (.inl 0)) (.inr 0)
    simp [gD, gJ, mD, mJ, s2, fromBlocks_multiply, scalar_apply'] at this
  · rw [img_mul] at h
    obtain ⟨d, hd⟩ := exists_scalar_of_img_eq_one h
    have := congrFun (congrFun hd (.inl 0)) (.inl 1)
    simp [gD, gW, mD, mW, s2, w2, fromBlocks_multiply, scalar_apply'] at this
  · rw [img_mul, img_mul] at h
    obtain ⟨d, hd⟩ := exists_scalar_of_img_eq_one h
    have := congrFun (congrFun hd (.inl 0)) (.inr 1)
    simp [gD, gW, gJ, mD, mW, mJ, s2, w2, fromBlocks_multiply, scalar_apply'] at this

theorem three_le_pRank_statedProj_statedSp_two [Finite F] (h2 : (2 : F) ≠ 0) :
    3 ≤ CFSG.pRank 2 (StatedProj (StatedSp 2 F)) :=
  RankThree.PartTwo.Sec4.Census.three_le_pRank_of_involutions xD_mul_self xW_mul_self
    xJ_mul_self xD_mul_xW xD_mul_xJ xW_mul_xJ (independent h2)

end CFSG.ComponentClassification.GSThmB.X11.E8

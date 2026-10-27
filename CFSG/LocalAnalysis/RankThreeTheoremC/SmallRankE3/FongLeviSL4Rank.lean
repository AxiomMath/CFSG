module

public import CFSG.GroupTheory.PGroup.RankTwoCommute
public import CFSG.LinearAlgebra.SL2MinimalFaithfulMatrix

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.FongLevi

open Subgroup

section Blocks

variable {F : Type} [Field F]

def sl4Block (A D : Matrix (Fin 2) (Fin 2) F) : Matrix (Fin 4) (Fin 4) F :=
  Matrix.reindex (finSumFinEquiv : Fin 2 ⊕ Fin 2 ≃ Fin 4) (finSumFinEquiv : Fin 2 ⊕ Fin 2 ≃ Fin 4)
    (Matrix.fromBlocks A 0 0 D)

theorem sl4_symm_castAdd (i : Fin 2) :
    (finSumFinEquiv : Fin 2 ⊕ Fin 2 ≃ Fin 4).symm (Fin.castAdd 2 i) = Sum.inl i :=
  finSumFinEquiv_symm_apply_castAdd i

theorem sl4_symm_natAdd (i : Fin 2) :
    (finSumFinEquiv : Fin 2 ⊕ Fin 2 ≃ Fin 4).symm (Fin.natAdd 2 i) = Sum.inr i :=
  finSumFinEquiv_symm_apply_natAdd i

theorem sl4Block_inl (A D : Matrix (Fin 2) (Fin 2) F) (i j : Fin 2) :
    sl4Block A D (Fin.castAdd 2 i) (Fin.castAdd 2 j) = A i j := by
  simp only [sl4Block, Matrix.reindex_apply, Matrix.submatrix_apply, sl4_symm_castAdd,
    Matrix.fromBlocks_apply₁₁]

theorem sl4Block_inr (A D : Matrix (Fin 2) (Fin 2) F) (i j : Fin 2) :
    sl4Block A D (Fin.natAdd 2 i) (Fin.natAdd 2 j) = D i j := by
  simp only [sl4Block, Matrix.reindex_apply, Matrix.submatrix_apply, sl4_symm_natAdd,
    Matrix.fromBlocks_apply₂₂]

theorem sl4Block_one : sl4Block (1 : Matrix (Fin 2) (Fin 2) F) 1 = 1 := by
  unfold sl4Block
  rw [Matrix.fromBlocks_one]
  exact map_one (Matrix.reindexRingEquiv F (finSumFinEquiv : Fin 2 ⊕ Fin 2 ≃ Fin 4))

theorem sl4Block_mul (A A' D D' : Matrix (Fin 2) (Fin 2) F) :
    sl4Block (A * A') (D * D') = sl4Block A D * sl4Block A' D' := by
  have h := map_mul (Matrix.reindexRingEquiv F (finSumFinEquiv : Fin 2 ⊕ Fin 2 ≃ Fin 4))
    (Matrix.fromBlocks A 0 0 D) (Matrix.fromBlocks A' 0 0 D')
  rw [Matrix.fromBlocks_multiply] at h
  simp only [mul_zero, zero_mul, add_zero, zero_add] at h
  exact h

theorem det_sl4Block (A D : Matrix (Fin 2) (Fin 2) F) :
    (sl4Block A D).det = A.det * D.det := by
  unfold sl4Block
  rw [Matrix.det_reindex_self, Matrix.det_fromBlocks_zero₂₁]

def sl4Blk1 : Matrix.SpecialLinearGroup (Fin 2) F →* Matrix.SpecialLinearGroup (Fin 4) F where
  toFun x := ⟨sl4Block x.1 1, by
    rw [det_sl4Block, Matrix.SpecialLinearGroup.det_coe, Matrix.det_one, mul_one]⟩
  map_one' := by
    apply Subtype.ext
    show sl4Block 1 1 = 1
    exact sl4Block_one
  map_mul' x y := by
    apply Subtype.ext
    show sl4Block (x.1 * y.1) 1 = sl4Block x.1 1 * sl4Block y.1 1
    have h := sl4Block_mul x.1 y.1 1 1
    rw [mul_one] at h
    exact h

def sl4Blk2 : Matrix.SpecialLinearGroup (Fin 2) F →* Matrix.SpecialLinearGroup (Fin 4) F where
  toFun x := ⟨sl4Block 1 x.1, by
    rw [det_sl4Block, Matrix.SpecialLinearGroup.det_coe, Matrix.det_one, one_mul]⟩
  map_one' := by
    apply Subtype.ext
    show sl4Block 1 1 = 1
    exact sl4Block_one
  map_mul' x y := by
    apply Subtype.ext
    show sl4Block 1 (x.1 * y.1) = sl4Block 1 x.1 * sl4Block 1 y.1
    have h := sl4Block_mul 1 1 x.1 y.1
    rw [one_mul] at h
    exact h

theorem sl4Blk1_injective : Function.Injective (sl4Blk1 (F := F)) := by
  rw [injective_iff_map_eq_one]
  intro x hx
  have h : sl4Block x.1 1 = 1 := congrArg Subtype.val hx
  apply Subtype.ext
  show x.1 = 1
  ext i j
  have hij := congrFun (congrFun h (Fin.castAdd 2 i)) (Fin.castAdd 2 j)
  rw [sl4Block_inl] at hij
  rw [hij]
  by_cases hk : i = j
  · subst hk
    rw [Matrix.one_apply_eq, Matrix.one_apply_eq]
  · rw [Matrix.one_apply_ne hk,
      Matrix.one_apply_ne (fun h' => hk (Fin.castAdd_injective 2 2 h'))]

theorem sl4Blk2_injective : Function.Injective (sl4Blk2 (F := F)) := by
  rw [injective_iff_map_eq_one]
  intro x hx
  have h : sl4Block 1 x.1 = 1 := congrArg Subtype.val hx
  apply Subtype.ext
  show x.1 = 1
  ext i j
  have hij := congrFun (congrFun h (Fin.natAdd 2 i)) (Fin.natAdd 2 j)
  rw [sl4Block_inr] at hij
  rw [hij]
  by_cases hk : i = j
  · subst hk
    rw [Matrix.one_apply_eq, Matrix.one_apply_eq]
  · rw [Matrix.one_apply_ne hk,
      Matrix.one_apply_ne (fun h' => hk (Fin.natAdd_injective 2 2 h'))]

theorem sl4Blk_commute (x : Matrix.SpecialLinearGroup (Fin 2) F) :
    Commute (sl4Blk1 x) (sl4Blk2 x) := by
  show sl4Blk1 x * sl4Blk2 x = sl4Blk2 x * sl4Blk1 x
  apply Subtype.ext
  show sl4Block x.1 1 * sl4Block 1 x.1 = sl4Block 1 x.1 * sl4Block x.1 1
  have h1 := sl4Block_mul x.1 1 1 x.1
  have h2 := sl4Block_mul 1 x.1 x.1 1
  calc sl4Block x.1 1 * sl4Block 1 x.1 = sl4Block (x.1 * 1) (1 * x.1) := h1.symm
    _ = sl4Block (1 * x.1) (x.1 * 1) := by simp only [mul_one, one_mul]
    _ = sl4Block 1 x.1 * sl4Block x.1 1 := h2

end Blocks

theorem two_le_pRank_sl4_of_dvd {F : Type} [Field F] [Finite F] {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hdvd : p ∣ Nat.card F ^ 2 - 1) :
    2 ≤ CFSG.Open.pRank p (⊤ : Subgroup (Matrix.SpecialLinearGroup (Fin 4) F)) := by
  clear hp2
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : Finite (Matrix.SpecialLinearGroup (Fin 2) F) :=
    Finite.of_injective (Subtype.val : Matrix.SpecialLinearGroup (Fin 2) F → Matrix (Fin 2) (Fin 2) F)
      Subtype.val_injective
  haveI : Finite (Matrix.SpecialLinearGroup (Fin 4) F) :=
    Finite.of_injective (Subtype.val : Matrix.SpecialLinearGroup (Fin 4) F → Matrix (Fin 4) (Fin 4) F)
      Subtype.val_injective
  have hcard : p ∣ Nat.card (Matrix.SpecialLinearGroup (Fin 2) F) := by
    rw [CFSG.SL2MinimalFaithful.card_specialLinearGroup_fin_two]
    exact Dvd.dvd.mul_left hdvd _
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' p hcard
  have hx1 : x ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at hx
    exact hp.one_lt.ne hx
  have hA : orderOf (sl4Blk1 x) = p := by
    rw [orderOf_injective sl4Blk1 (sl4Blk1_injective (F := F)) x, hx]
  have hB : orderOf (sl4Blk2 x) = p := by
    rw [orderOf_injective sl4Blk2 (sl4Blk2_injective (F := F)) x, hx]
  have hnot : sl4Blk2 x ∉ Subgroup.zpowers (sl4Blk1 x) := by
    intro hmem
    obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp hmem
    have h1 : sl4Blk1 (x ^ n) = sl4Blk2 x := by
      rw [map_zpow]
      exact hn
    have h2 : x.1 = 1 := by
      ext i j
      have hij : sl4Block (x ^ n).1 1 (Fin.natAdd 2 i) (Fin.natAdd 2 j) =
          sl4Block 1 x.1 (Fin.natAdd 2 i) (Fin.natAdd 2 j) :=
        congrFun (congrFun (congrArg Subtype.val h1) (Fin.natAdd 2 i)) (Fin.natAdd 2 j)
      rw [sl4Block_inr, sl4Block_inr] at hij
      exact hij.symm
    exact hx1 (Subtype.ext h2)
  exact CFSG.GroupTheory.two_le_pRank_of_commute (Subgroup.mem_top _) (Subgroup.mem_top _) hA hB
    (sl4Blk_commute x) hnot

end CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.FongLevi

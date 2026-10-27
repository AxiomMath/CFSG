module

public import TauCeti.LinearAlgebra.Matrix.BlockSucc
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LieType.SpecialLinear.CurtisDatum.RankOne
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge

public section

namespace CFSG.LieType.SpecialLinear

open Matrix CFSG.LieType.Steinberg CFSG.LieType.RootSystem CFSG.LieType.Universal
  CFSG.LieType.Universal.SpecialLinear
open scoped MatrixGroups

noncomputable section

variable (m : ℕ) (F : Type) [Field F]

@[expose] def blockEquivFirst : Fin 1 ⊕ Fin (m+1) ≃ Fin (m+2) :=
  (finSumFinEquiv (m := 1) (n := m+1)).trans (finCongr (by omega : 1 + (m+1) = m+2))

private theorem blockEquivFirst_apply_inl (i : Fin 1) :
    blockEquivFirst m (Sum.inl i) =
      Fin.cast (by omega : 1 + (m+1) = m+2) (Fin.castAdd (m+1) i) := by
  simp [blockEquivFirst, finSumFinEquiv_apply_left]

private theorem blockEquivFirst_apply_inr (j : Fin (m+1)) :
    blockEquivFirst m (Sum.inr j) =
      Fin.cast (by omega : 1 + (m+1) = m+2) (Fin.natAdd 1 j) := by
  simp [blockEquivFirst, finSumFinEquiv_apply_right]

private theorem blockEquivFirst_symm_zero : (blockEquivFirst m).symm 0 = Sum.inl 0 := by
  apply (blockEquivFirst m).injective
  rw [Equiv.apply_symm_apply, blockEquivFirst_apply_inl]
  rfl

private theorem blockEquivFirst_symm_succ (j : Fin (m+1)) :
    (blockEquivFirst m).symm j.succ = Sum.inr j := by
  apply (blockEquivFirst m).injective
  rw [Equiv.apply_symm_apply, blockEquivFirst_apply_inr]
  ext
  simp [Fin.natAdd, Fin.succ, Nat.add_comm]

@[expose] def fromBlocksFirst (A : Matrix (Fin 1) (Fin 1) F) (B : Matrix (Fin 1) (Fin (m+1)) F)
    (C : Matrix (Fin (m+1)) (Fin 1) F) (D : Matrix (Fin (m+1)) (Fin (m+1)) F) :
    Matrix (Fin (m+2)) (Fin (m+2)) F :=
  Matrix.reindexAlgEquiv F F (blockEquivFirst m) (Matrix.fromBlocks A B C D)

theorem fromBlocksFirst_apply_zero_zero {A : Matrix (Fin 1) (Fin 1) F}
    {B : Matrix (Fin 1) (Fin (m+1)) F} {C : Matrix (Fin (m+1)) (Fin 1) F}
    {D : Matrix (Fin (m+1)) (Fin (m+1)) F} :
    fromBlocksFirst m F A B C D 0 0 = A 0 0 := by
  simp [fromBlocksFirst, Matrix.coe_reindexAlgEquiv, Matrix.reindex_apply,
    Matrix.submatrix_apply, blockEquivFirst_symm_zero,
    Matrix.fromBlocks_apply₁₁]

theorem fromBlocksFirst_apply_zero_succ {A : Matrix (Fin 1) (Fin 1) F}
    {B : Matrix (Fin 1) (Fin (m+1)) F} {C : Matrix (Fin (m+1)) (Fin 1) F}
    {D : Matrix (Fin (m+1)) (Fin (m+1)) F} (j : Fin (m+1)) :
    fromBlocksFirst m F A B C D 0 j.succ = B 0 j := by
  simp [fromBlocksFirst, Matrix.coe_reindexAlgEquiv, Matrix.reindex_apply,
    Matrix.submatrix_apply, blockEquivFirst_symm_zero, blockEquivFirst_symm_succ,
    Matrix.fromBlocks_apply₁₂]

theorem fromBlocksFirst_apply_succ_zero {A : Matrix (Fin 1) (Fin 1) F}
    {B : Matrix (Fin 1) (Fin (m+1)) F} {C : Matrix (Fin (m+1)) (Fin 1) F}
    {D : Matrix (Fin (m+1)) (Fin (m+1)) F} (i : Fin (m+1)) :
    fromBlocksFirst m F A B C D i.succ 0 = C i 0 := by
  simp [fromBlocksFirst, Matrix.coe_reindexAlgEquiv, Matrix.reindex_apply,
    Matrix.submatrix_apply, blockEquivFirst_symm_zero, blockEquivFirst_symm_succ,
    Matrix.fromBlocks_apply₂₁]

theorem fromBlocksFirst_apply_succ_succ {A : Matrix (Fin 1) (Fin 1) F}
    {B : Matrix (Fin 1) (Fin (m+1)) F} {C : Matrix (Fin (m+1)) (Fin 1) F}
    {D : Matrix (Fin (m+1)) (Fin (m+1)) F} (i j : Fin (m+1)) :
    fromBlocksFirst m F A B C D i.succ j.succ = D i j := by
  simp [fromBlocksFirst, Matrix.coe_reindexAlgEquiv, Matrix.reindex_apply,
    Matrix.submatrix_apply, blockEquivFirst_symm_succ, Matrix.fromBlocks_apply₂₂]

@[expose] def embedSuccMat (g : Matrix (Fin (m+1)) (Fin (m+1)) F) :
    Matrix (Fin (m+2)) (Fin (m+2)) F :=
  fromBlocksFirst m F 1 0 0 g

private theorem embedSuccMat_apply_zero_zero (g : Matrix (Fin (m+1)) (Fin (m+1)) F) :
    embedSuccMat m F g 0 0 = 1 := by
  rw [embedSuccMat, fromBlocksFirst_apply_zero_zero]
  simp

theorem embedSuccMat_apply_zero_succ (g : Matrix (Fin (m+1)) (Fin (m+1)) F)
    (j : Fin (m+1)) : embedSuccMat m F g 0 j.succ = 0 := by
  rw [embedSuccMat, fromBlocksFirst_apply_zero_succ]
  simp

theorem embedSuccMat_apply_succ_zero (g : Matrix (Fin (m+1)) (Fin (m+1)) F)
    (i : Fin (m+1)) : embedSuccMat m F g i.succ 0 = 0 := by
  rw [embedSuccMat, fromBlocksFirst_apply_succ_zero]
  simp

theorem embedSuccMat_apply_succ_succ (g : Matrix (Fin (m+1)) (Fin (m+1)) F)
    (i j : Fin (m+1)) : embedSuccMat m F g i.succ j.succ = g i j := by
  rw [embedSuccMat, fromBlocksFirst_apply_succ_succ]

private theorem embedSuccMat_mul (g h : Matrix (Fin (m+1)) (Fin (m+1)) F) :
    embedSuccMat m F (g * h) = embedSuccMat m F g * embedSuccMat m F h := by
  rw [embedSuccMat, embedSuccMat, embedSuccMat, fromBlocksFirst,
    fromBlocksFirst, fromBlocksFirst, ← map_mul, Matrix.fromBlocks_multiply]
  simp

private theorem embedSuccMat_one : embedSuccMat m F (1 : Matrix (Fin (m+1)) (Fin (m+1)) F) = 1 := by
  rw [embedSuccMat, fromBlocksFirst, Matrix.fromBlocks_one, map_one]

private theorem det_embedSuccMat (g : Matrix (Fin (m+1)) (Fin (m+1)) F) :
    (embedSuccMat m F g).det = g.det := by
  rw [embedSuccMat, fromBlocksFirst, Matrix.det_reindexAlgEquiv,
    Matrix.det_fromBlocks_zero₂₁, Matrix.det_one, one_mul]

@[expose] def embedSucc :
    SpecialLinearGroup (Fin (m+1)) F →* SpecialLinearGroup (Fin (m+2)) F where
  toFun g := ⟨embedSuccMat m F (g : Matrix (Fin (m+1)) (Fin (m+1)) F), by
    rw [det_embedSuccMat]; exact g.2⟩
  map_one' := by
    apply Subtype.ext
    change embedSuccMat m F (1 : Matrix (Fin (m+1)) (Fin (m+1)) F) = 1
    rw [embedSuccMat_one]
  map_mul' g h := by
    apply Subtype.ext
    change embedSuccMat m F ((g * h : SpecialLinearGroup (Fin (m+1)) F) :
      Matrix (Fin (m+1)) (Fin (m+1)) F) =
      embedSuccMat m F (g : Matrix (Fin (m+1)) (Fin (m+1)) F) *
        embedSuccMat m F (h : Matrix (Fin (m+1)) (Fin (m+1)) F)
    rw [Matrix.SpecialLinearGroup.coe_mul, embedSuccMat_mul]

@[simp] theorem coe_embedSucc (g : SpecialLinearGroup (Fin (m+1)) F) :
    ((embedSucc m F g : SpecialLinearGroup (Fin (m+2)) F) :
      Matrix (Fin (m+2)) (Fin (m+2)) F) =
      embedSuccMat m F (g : Matrix (Fin (m+1)) (Fin (m+1)) F) := rfl

@[expose] def embedCastSuccMat (g : Matrix (Fin (m+1)) (Fin (m+1)) F) :
    Matrix (Fin (m+2)) (Fin (m+2)) F :=
  Matrix.blockSucc g

@[expose] def embedCastSucc :
    SpecialLinearGroup (Fin (m+1)) F →* SpecialLinearGroup (Fin (m+2)) F where
  toFun g := ⟨embedCastSuccMat m F (g : Matrix (Fin (m+1)) (Fin (m+1)) F), by
    rw [embedCastSuccMat, Matrix.det_blockSucc]; exact g.2⟩
  map_one' := by
    apply Subtype.ext
    change embedCastSuccMat m F (1 : Matrix (Fin (m+1)) (Fin (m+1)) F) = 1
    rw [embedCastSuccMat, Matrix.blockSucc_one]
  map_mul' g h := by
    apply Subtype.ext
    change embedCastSuccMat m F ((g * h : SpecialLinearGroup (Fin (m+1)) F) :
      Matrix (Fin (m+1)) (Fin (m+1)) F) =
      embedCastSuccMat m F (g : Matrix (Fin (m+1)) (Fin (m+1)) F) *
        embedCastSuccMat m F (h : Matrix (Fin (m+1)) (Fin (m+1)) F)
    rw [Matrix.SpecialLinearGroup.coe_mul, embedCastSuccMat, embedCastSuccMat,
      embedCastSuccMat, Matrix.blockSucc_mul]

@[simp] theorem coe_embedCastSucc (g : SpecialLinearGroup (Fin (m+1)) F) :
    ((embedCastSucc m F g : SpecialLinearGroup (Fin (m+2)) F) :
      Matrix (Fin (m+2)) (Fin (m+2)) F) =
      embedCastSuccMat m F (g : Matrix (Fin (m+1)) (Fin (m+1)) F) := rfl

@[simp] theorem fin_succ_ne_zero' {n : ℕ} (i : Fin n) :
    (0 : Fin (n+1)) ≠ i.succ := (Fin.succ_ne_zero i).symm

@[simp] theorem fin_last_ne_castSucc' {n : ℕ} (i : Fin n) :
    (Fin.last n : Fin (n+1)) ≠ i.castSucc := (Fin.castSucc_ne_last i).symm

@[simp] theorem fin_zero_ne_succ_castSucc' {n : ℕ} (i : Fin n) :
    (0 : Fin (n+2)) ≠ i.succ.castSucc := by
  intro h
  have h' := congrArg Fin.val h
  simp only [Fin.val_zero, Fin.val_castSucc, Fin.val_succ] at h'
  exact Nat.succ_ne_zero i.val h'.symm

@[simp] theorem fin_succ_eq_succ_castSucc_iff {n : ℕ} (a : Fin (n+1)) (i : Fin n) :
    a.succ = i.succ.castSucc ↔ a = i.castSucc := by
  rw [← Fin.succ_castSucc, Fin.succ_inj]

@[simp] theorem fin_castSucc_eq_castSucc_iff {n : ℕ} (a b : Fin n) :
    a.castSucc = b.castSucc ↔ a = b :=
  ⟨fun h => Fin.castSucc_injective n h, fun h => by rw [h]⟩

@[simp] theorem fin_zero_ne_succ_succ' {n : ℕ} (i : Fin n) :
    (0 : Fin (n+2)) ≠ i.succ.succ := (Fin.succ_ne_zero i.succ).symm

@[simp] theorem fin_castSucc_eq_succ_castSucc_iff {n : ℕ} (a : Fin (n+1)) (i : Fin n) :
    a.castSucc = i.castSucc.succ ↔ a = i.succ := by
  rw [Fin.succ_castSucc, fin_castSucc_eq_castSucc_iff]

@[simp] theorem fin_last_ne_succ_castSucc' {n : ℕ} (i : Fin n) :
    (Fin.last (n+1) : Fin (n+2)) ≠ i.castSucc.succ := by
  intro h
  have h' := congrArg Fin.val h
  simp only [Fin.val_last, Fin.val_castSucc, Fin.val_succ] at h'
  omega

private theorem embedSuccMat_transvection {i j : Fin (m+1)} (c : F) :
    embedSuccMat m F (1 + Matrix.single i j c) =
      1 + Matrix.single i.succ j.succ c := by
  ext a b
  rcases Fin.eq_zero_or_eq_succ a with rfl | ⟨a, rfl⟩ <;>
    rcases Fin.eq_zero_or_eq_succ b with rfl | ⟨b, rfl⟩ <;>
    simp [embedSuccMat_apply_zero_zero, embedSuccMat_apply_zero_succ,
      embedSuccMat_apply_succ_zero, embedSuccMat_apply_succ_succ,
      Matrix.one_apply, Matrix.single_apply, Fin.succ_inj, fin_succ_ne_zero']

theorem embedSucc_transvection {i j : Fin (m+1)} (hij : i ≠ j) (c : F) :
    embedSucc m F (SpecialLinearGroup.transvection hij c) =
      SpecialLinearGroup.transvection (fun h => hij (Fin.succ_inj.mp h)) c := by
  apply Subtype.ext
  change embedSuccMat m F (1 + Matrix.single i j c) =
    (1 + Matrix.single i.succ j.succ c : Matrix (Fin (m+2)) (Fin (m+2)) F)
  exact embedSuccMat_transvection m F c

private theorem embedCastSuccMat_transvection {i j : Fin (m+1)} (c : F) :
    embedCastSuccMat m F (1 + Matrix.single i j c) =
      1 + Matrix.single i.castSucc j.castSucc c := by
  ext a b
  rcases Fin.eq_castSucc_or_eq_last a with ⟨a, rfl⟩ | rfl <;>
    rcases Fin.eq_castSucc_or_eq_last b with ⟨b, rfl⟩ | rfl <;>
    simp [embedCastSuccMat, Matrix.blockSucc_castSucc_castSucc,
      Matrix.blockSucc_castSucc_last, Matrix.blockSucc_last_castSucc,
      Matrix.blockSucc_last_last, Matrix.one_apply, Matrix.single_apply,
      Fin.castSucc_ne_last, fin_last_ne_castSucc']

theorem embedCastSucc_transvection {i j : Fin (m+1)} (hij : i ≠ j) (c : F) :
    embedCastSucc m F (SpecialLinearGroup.transvection hij c) =
      SpecialLinearGroup.transvection
        (fun h => hij ((fin_castSucc_eq_castSucc_iff _ _).mp h)) c := by
  apply Subtype.ext
  change embedCastSuccMat m F (1 + Matrix.single i j c) =
    (1 + Matrix.single i.castSucc j.castSucc c : Matrix (Fin (m+2)) (Fin (m+2)) F)
  exact embedCastSuccMat_transvection m F c

theorem embedSucc_weylRep (i : Fin m) :
    embedSucc m F (weylRep m F i) = weylRep (m+1) F i.succ := by
  unfold weylRep
  rw [map_mul, map_mul]
  simp only [embedSucc_transvection]

theorem embedCastSucc_weylRep (i : Fin m) :
    embedCastSucc m F (weylRep m F i) = weylRep (m+1) F i.castSucc := by
  unfold weylRep
  rw [map_mul, map_mul]
  simp only [embedCastSucc_transvection]

theorem embedSucc_hdiag (i : Fin m) (u : Fˣ) :
    embedSucc m F (hdiag m F i u) = hdiag (m+1) F i.succ u := by
  apply Subtype.ext
  rw [hdiag, hdiag, coe_embedSucc, SpecialLinearGroup.diag2nUnit_coe,
    SpecialLinearGroup.diag2nUnit_coe]
  ext a b
  rcases Fin.eq_zero_or_eq_succ a with rfl | ⟨a, rfl⟩ <;>
    rcases Fin.eq_zero_or_eq_succ b with rfl | ⟨b, rfl⟩ <;>
    simp [embedSuccMat_apply_zero_zero, embedSuccMat_apply_zero_succ,
      embedSuccMat_apply_succ_zero, embedSuccMat_apply_succ_succ,
      Matrix.diagonal_apply, Fin.succ_inj]

theorem embedCastSucc_hdiag (i : Fin m) (u : Fˣ) :
    embedCastSucc m F (hdiag m F i u) = hdiag (m+1) F i.castSucc u := by
  apply Subtype.ext
  rw [hdiag, hdiag, coe_embedCastSucc, SpecialLinearGroup.diag2nUnit_coe,
    SpecialLinearGroup.diag2nUnit_coe, Fin.succ_castSucc]
  ext a b
  rcases Fin.eq_castSucc_or_eq_last a with ⟨a, rfl⟩ | rfl <;>
    rcases Fin.eq_castSucc_or_eq_last b with ⟨b, rfl⟩ | rfl <;>
    simp [embedCastSuccMat, Matrix.blockSucc_castSucc_castSucc,
      Matrix.blockSucc_castSucc_last, Matrix.blockSucc_last_castSucc,
      Matrix.blockSucc_last_last, Matrix.diagonal_apply,
      Fin.castSucc_ne_last, fin_last_ne_castSucc',
      fin_castSucc_eq_succ_castSucc_iff, fin_last_ne_succ_castSucc']

end

end CFSG.LieType.SpecialLinear

module

public import CFSG.Open.StatedAPI
public import CFSG.LinearAlgebra.CubeRootBlock

public section

namespace CFSG.ClassicalGroups.Symplectic.Sp6ThreeLocal

open Matrix CFSG.Open CFSG.Open.StatedAPI CFSG.LinearAlgebra
open scoped MatrixGroups

variable {K : Type} [Field K]

@[expose] def blockMatrix (g : Fin 3 → Matrix (Fin 2) (Fin 2) K) :
    Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) K :=
  fromBlocks (diagonal fun i => g i 0 0) (diagonal fun i => g i 0 1)
    (diagonal fun i => g i 1 0) (diagonal fun i => g i 1 1)

theorem blockMatrix_mul (g h : Fin 3 → Matrix (Fin 2) (Fin 2) K) :
    blockMatrix g * blockMatrix h = blockMatrix fun i => g i * h i := by
  unfold blockMatrix
  rw [fromBlocks_multiply]
  ext (i | i) (j | j) <;>
    by_cases hij : i = j <;>
    simp [hij, Matrix.mul_apply, Fin.sum_univ_two, Matrix.diagonal_apply]

theorem blockMatrix_one : blockMatrix (fun _ => (1 : Matrix (Fin 2) (Fin 2) K)) = 1 := by
  unfold blockMatrix
  ext (i | i) (j | j) <;>
    by_cases hij : i = j <;>
    simp [hij, Matrix.one_apply, Matrix.diagonal_apply]

theorem blockMatrix_transpose_mul_J (m : Fin 3 → Matrix (Fin 2) (Fin 2) K) :
    (blockMatrix m)ᵀ * fromBlocks 0 1 (-1) 0 * blockMatrix m =
      fromBlocks 0 (diagonal fun i => (m i).det) (-diagonal fun i => (m i).det) 0 := by
  unfold blockMatrix
  rw [fromBlocks_transpose, fromBlocks_multiply, fromBlocks_multiply]
  simp only [diagonal_transpose, Matrix.mul_zero, Matrix.zero_mul, Matrix.mul_one, Matrix.mul_neg,
    Matrix.neg_mul, zero_add, add_zero, diagonal_mul_diagonal]
  ext (i | i) (j | j) <;>
    simp [Matrix.diagonal_apply, Matrix.det_fin_two, fromBlocks_apply₁₁, fromBlocks_apply₁₂,
      fromBlocks_apply₂₁, fromBlocks_apply₂₂] <;>
    by_cases h : i = j <;> simp [h] <;> ring

theorem blockMatrix_transpose_mul (g : Fin 3 → SL(2, K)) :
    (blockMatrix fun i => (g i : Matrix (Fin 2) (Fin 2) K))ᵀ * fromBlocks 0 1 (-1) 0 *
        blockMatrix (fun i => (g i : Matrix (Fin 2) (Fin 2) K)) =
      (fromBlocks 0 1 (-1) 0 : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) K) := by
  rw [blockMatrix_transpose_mul_J]
  simp [Matrix.SpecialLinearGroup.det_coe]

theorem blockMatrix_mul_blockMatrix_inv (g : Fin 3 → SL(2, K)) :
    (blockMatrix fun i => (g i : Matrix (Fin 2) (Fin 2) K)) *
      blockMatrix (fun i => (((g i)⁻¹ : SL(2, K)) : Matrix (Fin 2) (Fin 2) K)) = 1 := by
  rw [blockMatrix_mul]
  simp only [← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel, Matrix.SpecialLinearGroup.coe_one]
  exact blockMatrix_one

theorem blockMatrix_inv_mul_blockMatrix (g : Fin 3 → SL(2, K)) :
    blockMatrix (fun i => (((g i)⁻¹ : SL(2, K)) : Matrix (Fin 2) (Fin 2) K)) *
      (blockMatrix fun i => (g i : Matrix (Fin 2) (Fin 2) K)) = 1 := by
  rw [blockMatrix_mul]
  simp only [← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel, Matrix.SpecialLinearGroup.coe_one]
  exact blockMatrix_one

@[expose] noncomputable def blockUnit (g : Fin 3 → SL(2, K)) : GL (Fin 3 ⊕ Fin 3) K :=
  ⟨blockMatrix fun i => (g i : Matrix (Fin 2) (Fin 2) K),
    blockMatrix fun i => (((g i)⁻¹ : SL(2, K)) : Matrix (Fin 2) (Fin 2) K),
    blockMatrix_mul_blockMatrix_inv g, blockMatrix_inv_mul_blockMatrix g⟩

@[expose] noncomputable def blockGL : (Fin 3 → SL(2, K)) →* GL (Fin 3 ⊕ Fin 3) K where
  toFun := blockUnit
  map_one' := by
    apply Units.ext
    exact blockMatrix_one
  map_mul' g h := by
    apply Units.ext
    change (blockMatrix fun i => (((g * h) i : SL(2, K)) : Matrix (Fin 2) (Fin 2) K)) =
      (blockMatrix fun i => (g i : Matrix (Fin 2) (Fin 2) K)) *
        blockMatrix fun i => (h i : Matrix (Fin 2) (Fin 2) K)
    rw [blockMatrix_mul]
    congr 1

@[expose] noncomputable def block : (Fin 3 → SL(2, K)) →* StatedSp 3 K :=
  blockGL.codRestrict (StatedSp 3 K) fun g => by
    rw [mem_statedSp_iff]
    exact blockMatrix_transpose_mul g

@[simp] theorem coe_block (g : Fin 3 → SL(2, K)) :
    (((block g : StatedSp 3 K) : GL (Fin 3 ⊕ Fin 3) K) : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) K) =
      blockMatrix fun i => (g i : Matrix (Fin 2) (Fin 2) K) :=
  rfl

theorem commute_iff_coe_commute (x y : StatedSp 3 K) :
    Commute x y ↔
      Commute (((x : GL (Fin 3 ⊕ Fin 3) K) : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) K))
        (((y : GL (Fin 3 ⊕ Fin 3) K) : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) K)) := by
  unfold Commute SemiconjBy
  rw [Subtype.ext_iff, Units.ext_iff]
  rfl

theorem block_injective : Function.Injective (block : (Fin 3 → SL(2, K)) →* StatedSp 3 K) := by
  rw [injective_iff_map_eq_one]
  intro g hg
  have h := congrArg (fun x : StatedSp 3 K => (((x : GL (Fin 3 ⊕ Fin 3) K) :
    Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) K))) hg
  simp only [coe_block] at h
  funext i
  have h00 := congrFun (congrFun h (Sum.inl i)) (Sum.inl i)
  have h01 := congrFun (congrFun h (Sum.inl i)) (Sum.inr i)
  have h10 := congrFun (congrFun h (Sum.inr i)) (Sum.inl i)
  have h11 := congrFun (congrFun h (Sum.inr i)) (Sum.inr i)
  simp [blockMatrix] at h00 h01 h10 h11
  ext a b
  fin_cases a <;> fin_cases b <;> simp [h00, h01, h10, h11]

theorem blockMatrix_apply_inl_inl_of_ne (g : Fin 3 → Matrix (Fin 2) (Fin 2) K) {i j : Fin 3}
    (hij : i ≠ j) : blockMatrix g (Sum.inl i) (Sum.inl j) = 0 := by
  simp [blockMatrix, Matrix.diagonal_apply_ne _ hij]

theorem not_mem_range_block_of_apply_ne {g : StatedSp 3 K} {i j : Fin 3} (hij : i ≠ j)
    (h : ((g : GL (Fin 3 ⊕ Fin 3) K) : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) K)
      (Sum.inl i) (Sum.inl j) ≠ 0) :
    g ∉ (block : (Fin 3 → SL(2, K)) →* StatedSp 3 K).range := by
  rintro ⟨z, rfl⟩
  exact h (by rw [coe_block]; exact blockMatrix_apply_inl_inl_of_ne _ hij)

@[expose] noncomputable def c₀ {s : SL(2, K)} (hs : IsCubeRootBlock s) :
    Multiplicative (Fin 3 → ZMod 3) →* StatedSp 3 K where
  toFun v := block fun i => s ^ (Multiplicative.toAdd v i).val
  map_one' := by
    rw [← map_one block]
    congr 1
  map_mul' v w := by
    rw [← map_mul block]
    congr 1
    funext i
    exact (cubePowHom s hs.pow_three).map_mul (Multiplicative.ofAdd (Multiplicative.toAdd v i))
      (Multiplicative.ofAdd (Multiplicative.toAdd w i))

theorem c₀_apply {s : SL(2, K)} (hs : IsCubeRootBlock s) (v : Multiplicative (Fin 3 → ZMod 3)) :
    c₀ hs v = block fun i => s ^ (Multiplicative.toAdd v i).val :=
  rfl

theorem c₀_ofAdd_vec {s : SL(2, K)} (hs : IsCubeRootBlock s) (x y z : ZMod 3) :
    c₀ hs (Multiplicative.ofAdd ![x, y, z]) = block ![s ^ x.val, s ^ y.val, s ^ z.val] := by
  rw [c₀_apply]
  congr 1
  funext i
  fin_cases i <;> rfl

theorem c₀_point_110 {s : SL(2, K)} (hs : IsCubeRootBlock s) :
    c₀ hs (Multiplicative.ofAdd ![1, 1, 0]) = block ![s, s, 1] := by
  have h1 : (1 : ZMod 3).val = 1 := rfl
  rw [c₀_ofAdd_vec]
  congr 1
  funext i
  fin_cases i <;> simp [h1]

theorem c₀_point_111 {s : SL(2, K)} (hs : IsCubeRootBlock s) :
    c₀ hs (Multiplicative.ofAdd ![1, 1, 1]) = block ![s, s, s] := by
  have h1 : (1 : ZMod 3).val = 1 := rfl
  rw [c₀_ofAdd_vec]
  congr 1
  funext i
  fin_cases i <;> simp [h1]

theorem c₀_point_001 {s : SL(2, K)} (hs : IsCubeRootBlock s) :
    c₀ hs (Multiplicative.ofAdd ![0, 0, 1]) = block ![1, 1, s] := by
  have h1 : (1 : ZMod 3).val = 1 := rfl
  rw [c₀_ofAdd_vec]
  congr 1
  funext i
  fin_cases i <;> simp [h1]

theorem c₀_ofAdd_single {s : SL(2, K)} (hs : IsCubeRootBlock s) (i : Fin 3) :
    c₀ hs (Multiplicative.ofAdd (Pi.single i 1)) = block fun j => if j = i then s else 1 := by
  have h1 : (1 : ZMod 3).val = 1 := rfl
  rw [c₀_apply]
  congr 1
  funext j
  by_cases h : j = i
  · subst h
    simp [h1]
  · simp [h, Pi.single_apply]

theorem c₀_injective {s : SL(2, K)} (hs : IsCubeRootBlock s) : Function.Injective (c₀ hs) := by
  rw [injective_iff_map_eq_one]
  intro v hv
  have h : block (fun i => s ^ (Multiplicative.toAdd v i).val) = block 1 := by
    rw [← c₀_apply hs, hv, map_one]
  have h2 := block_injective h
  apply Multiplicative.toAdd.injective
  funext i
  have h3 := congrFun h2 i
  exact (hs.pow_val_eq_one_iff _).mp h3

end CFSG.ClassicalGroups.Symplectic.Sp6ThreeLocal

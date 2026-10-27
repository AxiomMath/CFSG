module

public import CFSG.ClassicalGroups.SpecialLinear.SLnThreeLocalDefs
import CFSG.LinearAlgebra.CubeRootBlock

public section

namespace CFSG.ClassicalGroups.SLnThreeLocal

open Matrix CFSG.Open CFSG.LinearAlgebra
open scoped MatrixGroups

variable {K : Type} [Field K]

private abbrev hn6 : 6 = 6 ∨ 6 = 7 := Or.inl rfl

private theorem eq_zero_or_one_of_card_two [Finite K] (hK : Nat.card K = 2) (x : K) :
    x = 0 ∨ x = 1 := by
  by_cases h : x = 0
  · exact Or.inl h
  · exact Or.inr (by
      haveI : Subsingleton Kˣ := (Nat.card_eq_one_iff_unique.mp (by rw [Nat.card_units, hK])).1
      have h' := congrArg Units.val (Subsingleton.elim (Units.mk0 x h) 1)
      simpa using h')

private theorem two_eq_zero_of_card_two [Finite K] (hK : Nat.card K = 2) : (2 : K) = 0 := by
  rcases eq_zero_or_one_of_card_two hK (2 : K) with h | h
  · exact h
  · exfalso
    have h' : (2 : K) = 1 + 1 := by ring
    rw [h'] at h
    exact one_ne_zero (add_right_cancel (h.trans (zero_add 1).symm))

private theorem neg_one_eq_one_of_card_two [Finite K] (hK : Nat.card K = 2) : (-1 : K) = 1 := by
  have h2 : (2 : K) = 0 := two_eq_zero_of_card_two hK
  linear_combination -h2

private theorem three_ne_zero_of_card_two [Finite K] (hK : Nat.card K = 2) : (3 : K) ≠ 0 := by
  have h2 : (2 : K) = 0 := two_eq_zero_of_card_two hK
  intro h3
  have h : (3 : K) = 2 + 1 := by ring
  rw [h, h2, zero_add] at h3
  exact one_ne_zero h3

private theorem one_add_blockS [Finite K] (hK : Nat.card K = 2) :
    (1 : Matrix (Fin 2) (Fin 2) K) + blockS K = blockS K * blockS K := by
  have hneg : (-1 : K) = 1 := neg_one_eq_one_of_card_two hK
  ext i j
  fin_cases i <;> fin_cases j <;> simp [blockS, Matrix.mul_apply, Fin.sum_univ_two, hneg]

private theorem blockDiagonal_mul_apply_blk {γ : Type} (M : Fin 3 → Matrix (Fin 2) (Fin 2) K)
    (N : Matrix Blk γ K) (p : Fin 2) (i : Fin 3) (c : γ) :
    (blockDiagonal M * N) (p, i) c = ∑ p', M i p p' * N (p', i) c := by
  simp [Matrix.mul_apply, Fintype.sum_prod_type, Matrix.blockDiagonal_apply, ite_mul]

private theorem mul_blockDiagonal_apply_blk {γ : Type} (M : Fin 3 → Matrix (Fin 2) (Fin 2) K)
    (N : Matrix γ Blk K) (r : γ) (q : Fin 2) (j : Fin 3) :
    (N * blockDiagonal M) r (q, j) = ∑ q', N r (q', j) * M j q' q := by
  simp [Matrix.mul_apply, Fintype.sum_prod_type, Matrix.blockDiagonal_apply, mul_ite]

private theorem exists_blockDiagonal_of_commute_blockS [Finite K] (h3 : (3 : K) ≠ 0)
    (A : Matrix Blk Blk K)
    (hA : ∀ i : Fin 3, blockDiagonal (fun j => if j = i then blockS K else 1) * A =
      A * blockDiagonal (fun j => if j = i then blockS K else 1)) :
    ∃ B : Fin 3 → Matrix (Fin 2) (Fin 2) K,
      (∀ i, Commute (B i) (blockS K)) ∧ A = blockDiagonal B := by
  have hs : IsCubeRootBlock (cubeRootBlock K) := isCubeRootBlock_cubeRootBlock h3
  have hdiag : ∀ i : Fin 3, Commute (Matrix.of fun p q => A (p, i) (q, i)) (blockS K) := by
    intro i
    ext p q
    have h := congrFun (congrFun (hA i) (p, i)) (q, i)
    rw [blockDiagonal_mul_apply_blk, mul_blockDiagonal_apply_blk] at h
    simpa [Matrix.mul_apply] using h.symm
  have hoff : ∀ i j : Fin 3, i ≠ j → ∀ p q : Fin 2, A (p, i) (q, j) = 0 := by
    intro i j hij p q
    have hw : blockS K * (Matrix.of fun p' q' => A (p', i) (q', j)) =
        Matrix.of fun p' q' => A (p', i) (q', j) := by
      ext p' q'
      have h := congrFun (congrFun (hA i) (p', i)) (q', j)
      rw [blockDiagonal_mul_apply_blk, mul_blockDiagonal_apply_blk] at h
      simpa [Ne.symm hij, Matrix.mul_apply, Matrix.one_apply] using h
    have hz := hs.eq_zero_of_mul_left_eq hw
    have := congrFun (congrFun hz p) q
    simpa using this
  refine ⟨fun i => Matrix.of fun p q => A (p, i) (q, i), hdiag, ?_⟩
  ext x y
  obtain ⟨p, i⟩ := x
  obtain ⟨q, j⟩ := y
  by_cases hij : i = j
  · subst hij
    simp [Matrix.blockDiagonal_apply_eq]
  · rw [hoff i j hij p q, Matrix.blockDiagonal_apply_ne _ _ _ hij]

private theorem exists_blockDiagonal_of_commute [Finite K] (h3 : (3 : K) ≠ 0)
    (M : Matrix (Blk ⊕ Fin 0) (Blk ⊕ Fin 0) K)
    (hM : ∀ i : Fin 3,
      fromBlocks (blockDiagonal fun j => if j = i then blockS K else 1) 0 0 1 * M =
        M * fromBlocks (blockDiagonal fun j => if j = i then blockS K else 1) 0 0 1) :
    ∃ A : Fin 3 → Matrix (Fin 2) (Fin 2) K,
      (∀ i, Commute (A i) (blockS K)) ∧ M = fromBlocks (blockDiagonal A) 0 0 1 := by
  have hrel : ∀ i : Fin 3, blockDiagonal (fun j => if j = i then blockS K else 1) * M.toBlocks₁₁ =
      M.toBlocks₁₁ * blockDiagonal (fun j => if j = i then blockS K else 1) := by
    intro i
    have h := hM i
    rw [← fromBlocks_toBlocks M] at h
    simp only [fromBlocks_multiply, Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add,
      Matrix.mul_one, Matrix.one_mul] at h
    exact (fromBlocks_inj.mp h).1
  obtain ⟨A, hA, hAeq⟩ := exists_blockDiagonal_of_commute_blockS h3 M.toBlocks₁₁ hrel
  have h12 : M.toBlocks₁₂ = 0 := Subsingleton.elim _ _
  have h21 : M.toBlocks₂₁ = 0 := Subsingleton.elim _ _
  have h22 : M.toBlocks₂₂ = 1 := by ext i; exact i.elim0
  refine ⟨A, hA, ?_⟩
  conv_lhs => rw [← fromBlocks_toBlocks M]
  rw [hAeq, h12, h21, h22]

private theorem exists_blockPowGL_of_commute [Finite K] (hK : Nat.card K = 2)
    (h3 : (3 : K) ≠ 0) {A : Matrix (Fin 2) (Fin 2) K}
    (hcomm : Commute A (blockS K)) (hdet : A.det ≠ 0) :
    ∃ k : ZMod 3, A = ((blockPowGL K k : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) := by
  have hs : IsCubeRootBlock (cubeRootBlock K) := isCubeRootBlock_cubeRootBlock h3
  obtain ⟨x, y, rfl⟩ := hs.commute_iff.mp hcomm
  have hd : x ^ 2 - x * y + y ^ 2 ≠ 0 := by
    intro h0
    exact hdet (by rw [hs.det_smul_one_add_smul]; exact h0)
  rcases eq_zero_or_one_of_card_two hK x with rfl | rfl
  · rcases eq_zero_or_one_of_card_two hK y with rfl | rfl
    · exact absurd (by norm_num) hd
    · refine ⟨1, ?_⟩
      rw [blockPowGL_one]
      simp only [zero_smul, one_smul, zero_add]
      rfl
  · rcases eq_zero_or_one_of_card_two hK y with rfl | rfl
    · refine ⟨0, ?_⟩
      rw [blockPowGL_zero]
      simp only [one_smul, zero_smul, add_zero]
      rfl
    · refine ⟨2, ?_⟩
      have h2 : ((blockPowGL K 2 : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) =
          blockS K * blockS K := by
        simp [blockPowGL, blockSGL, pow_two, show (2 : ZMod 3).val = 2 from rfl]
      rw [h2]
      simp only [one_smul]
      exact one_add_blockS hK


private theorem reindex_embMat (X : Matrix Blk Blk K) :
    Matrix.reindexRingEquiv K (blkEquiv hn6) (embMat hn6 X) = fromBlocks X 0 0 1 :=
  (Matrix.reindex (blkEquiv hn6) (blkEquiv hn6)).apply_symm_apply (fromBlocks X 0 0 1)

private theorem reindex_coe_c₀ (v : Multiplicative (Fin 3 → ZMod 3)) :
    Matrix.reindexRingEquiv K (blkEquiv hn6)
        (((c₀ K hn6 v : StatedSL 6 K) : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) =
      fromBlocks (blockDiagonal fun j => ((blockPowGL K (Multiplicative.toAdd v j) :
        GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K)) 0 0 1 := by
  rw [coe_c₀, coe_blkGL]
  exact reindex_embMat _

private theorem fromBlocks_commute_of_mem_centralizer
    {g : StatedSL 6 K}
    (hg : g ∈ Subgroup.centralizer ((c₀ K hn6).range : Set (StatedSL 6 K))) (i : Fin 3) :
    fromBlocks (blockDiagonal fun j => if j = i then blockS K else 1) 0 0 1 *
        Matrix.reindexRingEquiv K (blkEquiv hn6)
          (((g : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K)) =
      Matrix.reindexRingEquiv K (blkEquiv hn6)
          (((g : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K)) *
        fromBlocks (blockDiagonal fun j => if j = i then blockS K else 1) 0 0 1 := by
  have h := Subgroup.mem_centralizer_iff.mp hg (c₀ K hn6 (Multiplicative.ofAdd (Pi.single i 1)))
    ⟨Multiplicative.ofAdd (Pi.single i 1), rfl⟩
  have h' := congrArg (fun x : StatedSL 6 K =>
    Matrix.reindexRingEquiv K (blkEquiv hn6)
      (((x : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K))) h
  simp only [Subgroup.coe_mul, Units.val_mul, map_mul] at h'
  rw [reindex_coe_c₀] at h'
  have hX : (fun j => ((blockPowGL K (Multiplicative.toAdd
      (Multiplicative.ofAdd (Pi.single i 1 : Fin 3 → ZMod 3)) j) : GL (Fin 2) K) :
        Matrix (Fin 2) (Fin 2) K)) = fun j => if j = i then blockS K else 1 := by
    funext j
    by_cases hj : j = i
    · subst hj
      simp [blockPowGL_one, blockSGL]
    · simp [hj, blockPowGL_zero]
  rwa [hX] at h'

private theorem det_ne_zero_reindex_coe (g : StatedSL 6 K) :
    (Matrix.reindexRingEquiv K (blkEquiv hn6)
      (((g : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K))).det ≠ 0 := by
  intro h0
  have h1 : ((g : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) *
      (((g⁻¹ : StatedSL 6 K) : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) = 1 := by
    rw [← Units.val_mul, ← Subgroup.coe_mul, mul_inv_cancel, Subgroup.coe_one, Units.val_one]
  have h2 : Matrix.reindexRingEquiv K (blkEquiv hn6)
        (((g : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K)) *
      Matrix.reindexRingEquiv K (blkEquiv hn6)
        ((((g⁻¹ : StatedSL 6 K) : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K)) = 1 := by
    rw [← map_mul, h1, map_one]
  have h := congrArg Matrix.det h2
  rw [Matrix.det_mul, h0, Matrix.det_one, zero_mul] at h
  exact one_ne_zero h.symm

private theorem mem_range_of_mem_centralizer [Finite K] (hK : Nat.card K = 2)
    {g : StatedSL 6 K}
    (hg : g ∈ Subgroup.centralizer ((c₀ K hn6).range : Set (StatedSL 6 K))) :
    g ∈ (c₀ K hn6).range := by
  have h3 : (3 : K) ≠ 0 := three_ne_zero_of_card_two hK
  set M : Matrix (Blk ⊕ Fin 0) (Blk ⊕ Fin 0) K :=
    Matrix.reindexRingEquiv K (blkEquiv hn6)
      (((g : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K)) with hM
  obtain ⟨A, hAcomm, hMeq⟩ := exists_blockDiagonal_of_commute h3 M (fun i => by
    rw [hM]; exact fromBlocks_commute_of_mem_centralizer hg i)
  have hdetM : M.det ≠ 0 := by
    rw [hM]; exact det_ne_zero_reindex_coe g
  have hdetA : ∀ i, (A i).det ≠ 0 := by
    have hMdet : M.det = (blockDiagonal A).det := by
      rw [hMeq, Matrix.det_fromBlocks_zero₁₂, Matrix.det_one, mul_one]
    have hprod : (∏ i, (A i).det) ≠ 0 := by
      rw [show (∏ i, (A i).det) = (blockDiagonal A).det from (Matrix.det_blockDiagonal A).symm]
      rw [← hMdet]
      exact hdetM
    intro i
    exact (Finset.prod_ne_zero_iff.mp hprod) i (Finset.mem_univ i)
  choose k hk using fun i => exists_blockPowGL_of_commute hK h3 (hAcomm i) (hdetA i)
  have hblock : blockDiagonal A = blockDiagonal (fun i =>
      ((blockPowGL K (k i) : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K)) := by
    congr 1
    funext i
    exact hk i
  have hMeq' : M = Matrix.reindexRingEquiv K (blkEquiv hn6)
      (((c₀ K hn6 (Multiplicative.ofAdd k) : StatedSL 6 K) : GL (Fin 6) K) :
        Matrix (Fin 6) (Fin 6) K) := by
    rw [hMeq, hblock, ← reindex_embMat, reindex_coe_c₀, reindex_embMat]
    simp only [toAdd_ofAdd]
  have hMg : g = c₀ K hn6 (Multiplicative.ofAdd k) := by
    apply Subtype.ext
    apply Units.ext
    exact (Matrix.reindexRingEquiv K (blkEquiv hn6)).injective (by rw [← hM]; exact hMeq')
  exact MonoidHom.mem_range.mpr ⟨Multiplicative.ofAdd k, hMg.symm⟩

theorem card_centralizer_range_c₀_six [Finite K] (hK : Nat.card K = 2) :
    Nat.card (Subgroup.centralizer
      ((c₀ K (Or.inl rfl : 6 = 6 ∨ 6 = 7)).range : Set (StatedSL 6 K))) = 27 := by
  show Nat.card (Subgroup.centralizer ((c₀ K hn6).range : Set (StatedSL 6 K))) = 27
  have hcent : Subgroup.centralizer ((c₀ K hn6).range : Set (StatedSL 6 K)) =
      (c₀ K hn6).range := by
    refine le_antisymm (fun g hg => mem_range_of_mem_centralizer hK hg) ?_
    intro g hg
    obtain ⟨v, rfl⟩ := MonoidHom.mem_range.mp hg
    refine Subgroup.mem_centralizer_iff.mpr fun x hx => ?_
    obtain ⟨w, rfl⟩ := MonoidHom.mem_range.mp hx
    rw [← map_mul, ← map_mul, mul_comm]
  rw [hcent]
  have hcard : Nat.card (c₀ K hn6).range = Nat.card (Multiplicative (Fin 3 → ZMod 3)) :=
    Nat.card_range_of_injective (c₀_injective hn6)
  rw [hcard, Nat.card_eq_fintype_card]
  simp [Fintype.card_fun, ZMod.card, Fintype.card_fin]

end CFSG.ClassicalGroups.SLnThreeLocal

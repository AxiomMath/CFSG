module

public import CFSG.ClassicalGroups.SpecialLinear.SLnThreeLocalDefs
import CFSG.ClassicalGroups.SpecialLinear.SLnThreeLocalReal
import CFSG.LinearAlgebra.CubeRootBlock

public section

namespace CFSG.ClassicalGroups.SLnThreeLocal

open Matrix CFSG.Open CFSG.LinearAlgebra
open scoped MatrixGroups

variable {K : Type} [Field K]

private theorem blockDiagonal_mul_apply_blk {γ : Type} (M : Fin 3 → Matrix (Fin 2) (Fin 2) K)
    (N : Matrix Blk γ K) (p : Fin 2) (i : Fin 3) (c : γ) :
    (blockDiagonal M * N) (p, i) c = ∑ p', M i p p' * N (p', i) c := by
  simp [Matrix.mul_apply, Fintype.sum_prod_type, Matrix.blockDiagonal_apply, ite_mul]

private theorem mul_blockDiagonal_apply_blk {γ : Type} (M : Fin 3 → Matrix (Fin 2) (Fin 2) K)
    (N : Matrix γ Blk K) (r : γ) (q : Fin 2) (j : Fin 3) :
    (N * blockDiagonal M) r (q, j) = ∑ q', N r (q', j) * M j q' q := by
  simp [Matrix.mul_apply, Fintype.sum_prod_type, Matrix.blockDiagonal_apply, mul_ite]

private theorem eq_fromBlocks_of_commute_blockPowGL [Finite K] (h3 : (3 : K) ≠ 0) {ι : Type}
    [Fintype ι] [DecidableEq ι] (G : Matrix (Blk ⊕ ι) (Blk ⊕ ι) K)
    (hG : ∀ v : Multiplicative (Fin 3 → ZMod 3),
      fromBlocks (blockDiagonal fun i => ((blockPowGL K (Multiplicative.toAdd v i) :
          GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K)) 0 0 1 * G =
        G * fromBlocks (blockDiagonal fun i => ((blockPowGL K (Multiplicative.toAdd v i) :
          GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K)) 0 0 1) :
    G = fromBlocks (blockDiagonal fun i => Matrix.of fun p q => G (.inl (p, i)) (.inl (q, i)))
      0 0 G.toBlocks₂₂ := by
  have hs := isCubeRootBlock_cubeRootBlock (K := K) h3
  have hS : ((cubeRootBlock K : SL(2, K)) : Matrix (Fin 2) (Fin 2) K) = blockS K := rfl
  have hrel : ∀ i : Fin 3,
      blockDiagonal (fun j => if j = i then blockS K else 1) * G.toBlocks₁₁ =
          G.toBlocks₁₁ * blockDiagonal (fun j => if j = i then blockS K else 1) ∧
        blockDiagonal (fun j => if j = i then blockS K else 1) * G.toBlocks₁₂ = G.toBlocks₁₂ ∧
        G.toBlocks₂₁ = G.toBlocks₂₁ * blockDiagonal (fun j => if j = i then blockS K else 1) := by
    intro i
    have hX : (fun j => ((blockPowGL K (Multiplicative.toAdd
        (Multiplicative.ofAdd (Pi.single i 1 : Fin 3 → ZMod 3)) j) : GL (Fin 2) K) :
          Matrix (Fin 2) (Fin 2) K)) = fun j => if j = i then blockS K else 1 := by
      funext j
      by_cases hj : j = i
      · subst hj
        simp [blockPowGL_one, blockSGL]
      · simp [hj, blockPowGL_zero]
    have h := hG (Multiplicative.ofAdd (Pi.single i 1))
    rw [hX, ← fromBlocks_toBlocks G] at h
    simp only [fromBlocks_multiply, Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add,
      Matrix.mul_one, Matrix.one_mul] at h
    obtain ⟨h1, h2, h3, -⟩ := fromBlocks_inj.mp h
    exact ⟨h1, h2, h3⟩
  have hB : G.toBlocks₁₂ = 0 := by
    ext ⟨p, i⟩ t
    have hw : ((cubeRootBlock K : SL(2, K)) : Matrix (Fin 2) (Fin 2) K) *
        Matrix.of (fun p' (_ : Fin 2) => G.toBlocks₁₂ (p', i) t) =
          Matrix.of (fun p' (_ : Fin 2) => G.toBlocks₁₂ (p', i) t) := by
      ext p' q'
      have h := congrFun (congrFun (hrel i).2.1 (p', i)) t
      rw [blockDiagonal_mul_apply_blk] at h
      simpa [hS, Matrix.mul_apply] using h
    simpa using congrFun (congrFun (hs.eq_zero_of_mul_left_eq hw) p) 0
  have hC : G.toBlocks₂₁ = 0 := by
    ext t ⟨q, i⟩
    have hw : Matrix.of (fun (_ : Fin 2) q' => G.toBlocks₂₁ t (q', i)) *
        ((cubeRootBlock K : SL(2, K)) : Matrix (Fin 2) (Fin 2) K) =
          Matrix.of (fun (_ : Fin 2) q' => G.toBlocks₂₁ t (q', i)) := by
      ext p' q'
      have h := congrFun (congrFun (hrel i).2.2 t) (q', i)
      rw [mul_blockDiagonal_apply_blk] at h
      simpa [hS, Matrix.mul_apply] using h.symm
    simpa using congrFun (congrFun (hs.eq_zero_of_mul_right_eq hw) 0) q
  have hA : ∀ i j : Fin 3, i ≠ j → ∀ p q : Fin 2, G.toBlocks₁₁ (p, i) (q, j) = 0 := by
    intro i j hij p q
    have hw : ((cubeRootBlock K : SL(2, K)) : Matrix (Fin 2) (Fin 2) K) *
        Matrix.of (fun p' q' => G.toBlocks₁₁ (p', i) (q', j)) =
          Matrix.of (fun p' q' => G.toBlocks₁₁ (p', i) (q', j)) := by
      ext p' q'
      have h := congrFun (congrFun (hrel i).1 (p', i)) (q', j)
      rw [blockDiagonal_mul_apply_blk, mul_blockDiagonal_apply_blk] at h
      simpa [hS, Matrix.mul_apply, Ne.symm hij, Matrix.one_apply] using h
    simpa using congrFun (congrFun (hs.eq_zero_of_mul_left_eq hw) p) q
  conv_lhs => rw [← fromBlocks_toBlocks G]
  rw [hB, hC]
  refine fromBlocks_inj.mpr ⟨?_, rfl, rfl, rfl⟩
  ext ⟨p, i⟩ ⟨q, j⟩
  by_cases hij : i = j
  · subst hij
    simp [Matrix.blockDiagonal_apply_eq, Matrix.toBlocks₁₁]
  · rw [hA i j hij, Matrix.blockDiagonal_apply_ne _ _ _ hij]

private theorem natCard_GL_dvd_six [Finite K] (hK : Nat.card K = 2) {m : ℕ} (hm : m ≤ 2) :
    Nat.card (GL (Fin m) K) ∣ 6 := by
  have := Fintype.ofFinite K
  rw [Matrix.card_GL_field, ← Nat.card_eq_fintype_card, hK]
  interval_cases m <;> simp [Fin.prod_univ_two]

private theorem eq_one_of_pow_seven_of_card_two [Finite K] (hK : Nat.card K = 2) {m : ℕ}
    (hm : m ≤ 2) {N : Matrix (Fin m) (Fin m) K} (hN : N ^ 7 = 1) : N = 1 := by
  obtain ⟨u, rfl⟩ : ∃ u : GL (Fin m) K, (u : Matrix (Fin m) (Fin m) K) = N :=
    ⟨⟨N, N ^ 6, by rw [← pow_succ']; exact hN, by rw [← pow_succ]; exact hN⟩, rfl⟩
  have h6 : u ^ 6 = 1 :=
    orderOf_dvd_iff_pow_eq_one.mp ((orderOf_dvd_natCard u).trans (natCard_GL_dvd_six hK hm))
  have h7 : u ^ 7 = 1 := Units.ext (by rw [Units.val_pow_eq_pow_val, hN, Units.val_one])
  rw [pow_succ, h6, one_mul] at h7
  rw [h7, Units.val_one]

private theorem eq_one_of_commute_blockPowGL_of_pow_seven [Finite K] (hK : Nat.card K = 2)
    {m : ℕ} (hm : m ≤ 2) (G : Matrix (Blk ⊕ Fin m) (Blk ⊕ Fin m) K)
    (hG : ∀ v : Multiplicative (Fin 3 → ZMod 3),
      fromBlocks (blockDiagonal fun i => ((blockPowGL K (Multiplicative.toAdd v i) :
          GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K)) 0 0 1 * G =
        G * fromBlocks (blockDiagonal fun i => ((blockPowGL K (Multiplicative.toAdd v i) :
          GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K)) 0 0 1)
    (h7 : G ^ 7 = 1) : G = 1 := by
  have h3 : (3 : K) ≠ 0 := three_ne_zero_of_natCard_mod_three (by rw [hK])
  obtain ⟨a, D, rfl⟩ : ∃ (a : Fin 3 → Matrix (Fin 2) (Fin 2) K) (D : Matrix (Fin m) (Fin m) K),
      G = fromBlocks (blockDiagonal a) 0 0 D :=
    ⟨_, _, eq_fromBlocks_of_commute_blockPowGL h3 G hG⟩
  rw [fromBlocks_diagonal_pow, ← blockDiagonal_pow, ← fromBlocks_one, ← blockDiagonal_one] at h7
  obtain ⟨ha, -, -, hD⟩ := fromBlocks_inj.mp h7
  have ha1 : a = 1 := funext fun i => eq_one_of_pow_seven_of_card_two hK le_rfl
    (by simpa using congrFun (blockDiagonal_injective ha) i)
  rw [ha1, eq_one_of_pow_seven_of_card_two hK hm hD, blockDiagonal_one, fromBlocks_one]

theorem not_seven_dvd_card_centralizer_range_c₀ [Finite K] (hK : Nat.card K = 2) :
    ¬ 7 ∣ Nat.card (Subgroup.centralizer
      ((c₀ K (Or.inr rfl : 7 = 6 ∨ 7 = 7)).range : Set (StatedSL 7 K))) := by
  have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  intro h7
  obtain ⟨⟨g, hg⟩, hgo⟩ := exists_prime_orderOf_dvd_card' 7 h7
  have hg7 : ((g : GL (Fin 7) K) : Matrix (Fin 7) (Fin 7) K) ^ 7 = 1 := by
    have h := pow_orderOf_eq_one (⟨g, hg⟩ : Subgroup.centralizer
      ((c₀ K (Or.inr rfl : 7 = 6 ∨ 7 = 7)).range : Set (StatedSL 7 K)))
    rw [hgo] at h
    have h' : g ^ 7 = 1 := by
      have := congrArg Subtype.val h
      rwa [Subgroup.coe_pow, Subgroup.coe_one] at this
    rw [← Units.val_pow_eq_pow_val, ← Subgroup.coe_pow, h', Subgroup.coe_one, Units.val_one]
  let R := Matrix.reindexRingEquiv K (blkEquiv (Or.inr rfl : 7 = 6 ∨ 7 = 7))
  have hR : ∀ X : Matrix Blk Blk K,
      R (embMat (Or.inr rfl : 7 = 6 ∨ 7 = 7) X) = fromBlocks X 0 0 1 := fun X =>
    (Matrix.reindex (blkEquiv (Or.inr rfl : 7 = 6 ∨ 7 = 7))
      (blkEquiv (Or.inr rfl : 7 = 6 ∨ 7 = 7))).apply_symm_apply (fromBlocks X 0 0 1)
  have hcomm : ∀ v : Multiplicative (Fin 3 → ZMod 3),
      fromBlocks (blockDiagonal fun i => ((blockPowGL K (Multiplicative.toAdd v i) :
          GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K)) 0 0 1 *
          R ((g : GL (Fin 7) K) : Matrix (Fin 7) (Fin 7) K) =
        R ((g : GL (Fin 7) K) : Matrix (Fin 7) (Fin 7) K) *
          fromBlocks (blockDiagonal fun i => ((blockPowGL K (Multiplicative.toAdd v i) :
            GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K)) 0 0 1 := by
    intro v
    rw [← hR, ← map_mul, ← map_mul]
    have h := Subgroup.mem_centralizer_iff.mp hg (c₀ K (Or.inr rfl) v) ⟨v, rfl⟩
    have h' := congrArg (fun x : StatedSL 7 K => ((x : GL (Fin 7) K) :
      Matrix (Fin 7) (Fin 7) K)) h
    simp only [Subgroup.coe_mul, Units.val_mul] at h'
    exact congrArg R h'
  have hG1 := eq_one_of_commute_blockPowGL_of_pow_seven hK (by norm_num) _ hcomm
    (by rw [← map_pow, hg7, map_one])
  have hg1 : g = 1 := Subtype.ext (Units.ext (R.injective (hG1.trans (map_one R).symm)))
  subst hg1
  rw [Subgroup.orderOf_mk, orderOf_one] at hgo
  omega

end CFSG.ClassicalGroups.SLnThreeLocal

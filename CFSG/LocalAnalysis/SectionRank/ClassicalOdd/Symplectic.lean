module

public import CFSG.LocalAnalysis.SectionRank.ClassicalOdd.Basic

public section

namespace CFSG.SectionRank.ClassicalOdd

open CFSG.Open CFSG.Assembly.LowTwoRank Matrix

variable {K : Type} [Field K] {n : ℕ}

@[expose] def spSym (hn : 2 ≤ n) (x : (Fin n → K) × K) : Matrix (Fin n) (Fin n) K :=
  diagonal x.1 +
    x.2 • (single ⟨0, by omega⟩ ⟨1, by omega⟩ 1 + single ⟨1, by omega⟩ ⟨0, by omega⟩ 1)

theorem spSym_transpose (hn : 2 ≤ n) (x : (Fin n → K) × K) : (spSym hn x)ᵀ = spSym hn x := by
  simp only [spSym, transpose_add, transpose_smul, diagonal_transpose, transpose_single]
  rw [add_comm (single _ _ _)]

theorem spSym_add (hn : 2 ≤ n) (x y : (Fin n → K) × K) :
    spSym hn (x + y) = spSym hn x + spSym hn y := by
  simp only [spSym, Prod.fst_add, Prod.snd_add, add_smul]
  rw [show diagonal (x.1 + y.1) = diagonal x.1 + diagonal y.1 from (diagonal_add _ _).symm]
  abel

theorem spSym_zero (hn : 2 ≤ n) : spSym hn (0 : (Fin n → K) × K) = 0 := by
  simp [spSym]

theorem spSym_diag (hn : 2 ≤ n) (x : (Fin n → K) × K) (i : Fin n) : spSym hn x i i = x.1 i := by
  simp only [spSym, Matrix.add_apply, Matrix.smul_apply, diagonal_apply_eq, single_apply,
    smul_eq_mul]
  split_ifs <;> first | (exfalso; simp only [Fin.ext_iff] at *; omega) | simp

theorem spSym_zero_one (hn : 2 ≤ n) (x : (Fin n → K) × K) :
    spSym hn x ⟨0, by omega⟩ ⟨1, by omega⟩ = x.2 := by
  simp [spSym, diagonal_apply_ne]

theorem spSym_injective (hn : 2 ≤ n) : Function.Injective (spSym (K := K) hn) := by
  intro x y h
  have h01 := congrFun (congrFun h ⟨0, by omega⟩) ⟨1, by omega⟩
  rw [spSym_zero_one, spSym_zero_one] at h01
  refine Prod.ext (funext fun i => ?_) h01
  have := congrFun (congrFun h i) i
  rwa [spSym_diag, spSym_diag] at this

@[expose] noncomputable def spHom (hn : 2 ≤ n) :
    Multiplicative ((Fin n → K) × K) →* GL (Fin n ⊕ Fin n) K :=
  glOfAdd (fun x => fromBlocks 1 (spSym hn x) 0 1) (by rw [spSym_zero, fromBlocks_one])
    (fun x y => by
      rw [fromBlocks_multiply, spSym_add]
      simp only [mul_one, mul_zero, add_zero, one_mul, zero_mul, zero_add]
      rw [add_comm])

theorem spHom_injective (hn : 2 ≤ n) : Function.Injective (spHom (K := K) hn) :=
  glOfAdd_injective fun _ _ h => spSym_injective hn (fromBlocks_inj.1 h).2.1

theorem spHom_mem (hn : 2 ≤ n) (x) : spHom (K := K) hn x ∈ StatedSp n K := by
  refine Subgroup.subset_closure ?_
  change (fromBlocks 1 (spSym hn x.toAdd) 0 1)ᵀ * fromBlocks 0 1 (-1) 0 *
    fromBlocks 1 (spSym hn x.toAdd) 0 1 = fromBlocks 0 1 (-1) 0
  rw [fromBlocks_transpose, fromBlocks_multiply, fromBlocks_multiply, spSym_transpose]
  simp

theorem spHom_mulVec (hn : 2 ≤ n) (x) :
    (spHom (K := K) hn x : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) *ᵥ
      Pi.single (Sum.inl ⟨0, by omega⟩) 1 = Pi.single (Sum.inl ⟨0, by omega⟩) 1 := by
  rw [spHom, coe_glOfAdd, mulVec_single_one]
  ext i
  rcases i with i | i <;> simp [one_apply, Pi.single_apply]

theorem le_pRank_Sp (hn : 2 ≤ n) [Finite K] {p f : ℕ} [Fact p.Prime]
    (hK : Nat.card K = p ^ f) :
    f * (n + 1) ≤ pRank p (⊤ : Subgroup (StatedProj (StatedSp n K))) := by
  have := charP_of_card hK
  refine le_pRank_statedProj (Fact.out : p.Prime).one_lt multiplicative_comm
    (pow_char_eq_one (K := K)) ?_ (spHom hn) (spHom_injective hn) (spHom_mem hn)
    (v := Pi.single (Sum.inl ⟨0, by omega⟩) 1) (by simp) (spHom_mulVec hn)
  rw [Nat.card_congr Multiplicative.toAdd, Nat.card_prod, Nat.card_fun, hK,
    Nat.card_eq_fintype_card, Fintype.card_fin, ← pow_mul, ← pow_add, mul_add, mul_one]

end CFSG.SectionRank.ClassicalOdd

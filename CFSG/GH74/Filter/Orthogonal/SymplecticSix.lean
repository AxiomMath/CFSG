module

public import CFSG.GH74.Filter.Statements
public import CFSG.GH74.Filter.Witness
public import CFSG.LocalAnalysis.SectionRank.ClassicalOdd.Basic

public section

namespace CFSG.GH74.Filter

open CFSG.SectionRank CFSG.SectionRank.ClassicalOdd CFSG.Assembly.LowTwoRank Matrix

section SymmetricBlocks

variable {K : Type} [Field K] {n : ℕ}

@[expose] def symMat (x : Sym2 (Fin n) → K) : Matrix (Fin n) (Fin n) K :=
  Matrix.of fun i j => x s(i, j)

omit [Field K] in
theorem symMat_transpose (x : Sym2 (Fin n) → K) : (symMat x)ᵀ = symMat x := by
  ext i j
  simp [symMat, Sym2.eq_swap]

theorem symMat_add (x y : Sym2 (Fin n) → K) : symMat (x + y) = symMat x + symMat y := by
  ext i j
  rfl

theorem symMat_zero : symMat (0 : Sym2 (Fin n) → K) = 0 := by
  ext i j
  rfl

omit [Field K] in
theorem symMat_injective : Function.Injective (symMat (K := K) (n := n)) := by
  intro x y h
  funext z
  induction z using Sym2.ind with
  | _ i j => exact congrFun (congrFun h i) j

@[expose] noncomputable def symHom :
    Multiplicative (Sym2 (Fin n) → K) →* GL (Fin n ⊕ Fin n) K :=
  glOfAdd (fun x => fromBlocks 1 (symMat x) 0 1) (by rw [symMat_zero, fromBlocks_one])
    (fun x y => by
      rw [fromBlocks_multiply, symMat_add]
      simp only [mul_one, mul_zero, add_zero, one_mul, zero_mul, zero_add]
      rw [add_comm])

theorem symHom_injective : Function.Injective (symHom (K := K) (n := n)) :=
  glOfAdd_injective fun _ _ h => symMat_injective (fromBlocks_inj.1 h).2.1

theorem symHom_mem (x : Multiplicative (Sym2 (Fin n) → K)) : symHom x ∈ StatedSp n K := by
  refine Subgroup.subset_closure ?_
  change (fromBlocks 1 (symMat x.toAdd) 0 1)ᵀ * fromBlocks 0 1 (-1) 0 *
    fromBlocks 1 (symMat x.toAdd) 0 1 = fromBlocks 0 1 (-1) 0
  rw [fromBlocks_transpose, fromBlocks_multiply, fromBlocks_multiply, symMat_transpose]
  simp

theorem symHom_mulVec (hn : 1 ≤ n) (x : Multiplicative (Sym2 (Fin n) → K)) :
    (symHom x : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) *ᵥ
      Pi.single (Sum.inl ⟨0, by omega⟩) 1 = Pi.single (Sum.inl ⟨0, by omega⟩) 1 := by
  rw [symHom, coe_glOfAdd, mulVec_single_one]
  ext i
  rcases i with i | i <;> simp [one_apply, Pi.single_apply]

theorem le_pRank_Sp_sym (hn : 1 ≤ n) [Finite K] {p f : ℕ} [Fact p.Prime]
    (hK : Nat.card K = p ^ f) :
    f * ((n + 1).choose 2) ≤ CFSG.Open.pRank p (⊤ : Subgroup (StatedProj (StatedSp n K))) := by
  have := charP_of_card hK
  refine le_pRank_statedProj (Fact.out : p.Prime).one_lt multiplicative_comm
    (pow_char_eq_one (K := K)) ?_ symHom symHom_injective symHom_mem
    (v := Pi.single (Sum.inl ⟨0, by omega⟩) 1) (by simp) (symHom_mulVec hn)
  rw [card_multiplicative_fun hK, Sym2.card, Fintype.card_fin]

end SymmetricBlocks

theorem t_PSp_three_two : S_PSp_three_two := by
  intro G _ _ hm
  obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := hm
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h := le_pRank_Sp_sym (n := 3) (p := 2) (f := 1) (by norm_num) hK
  rw [← pRank_top_eq_of_mulEquiv (by norm_num) e] at h
  apply not_gen4_of_twoRank
  change 4 < CFSG.Open.pRank 2 (⊤ : Subgroup G)
  have h6 : (3 + 1).choose 2 = 6 := by decide
  omega

end CFSG.GH74.Filter

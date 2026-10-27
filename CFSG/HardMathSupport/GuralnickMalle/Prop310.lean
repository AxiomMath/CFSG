module

public import CFSG.HardMathSupport.GuralnickMalle.LRank
public import CFSG.HardMathSupport.GuralnickMalle.Gerstenhaber

public section

namespace CFSG.HardMathSupport.GuralnickMalle

open CFSG.Open
open Module

variable {n : ℕ} {K : Type} [Field K]

theorem commonKernel_unipotentAlgebra (A : Subgroup (GL (Fin n) K)) :
    commonKernel (unipotentAlgebra A) = fixSubGen (glNaturalRep n K) A := by
  simpa [commonKernel] using iInf_ker_unipotentAlgebra (K := K) A

theorem finrank_unipotentAlgebra_le {p : ℕ} [CharP K p] (hp : p.Prime)
    {A : Subgroup (GL (Fin n) K)} (hA : IsElemAbelian p A) :
    finrank K (unipotentAlgebra A) ≤
      finrank K (fixSubGen (glNaturalRep n K) A) *
        (n - finrank K (fixSubGen (glNaturalRep n K) A)) := by
  have h := finrank_le_commonKernel_mul (K := K) (V := Fin n → K) (unipotentAlgebra A)
    (fun f hf g hg => unipotentAlgebra_mul_mem hf hg)
    (fun f hf g hg => unipotentAlgebra_commute hA.1 hf hg)
    (fun f hf => unipotentAlgebra_isNilpotent hp hA hf)
  rwa [commonKernel_unipotentAlgebra, Module.finrank_fin_fun] at h

theorem card_le_pow_of_elemAbelian {p : ℕ} [Finite K] [CharP K p] (hp : p.Prime)
    {A : Subgroup (GL (Fin n) K)} (hA : IsElemAbelian p A) :
    Nat.card A ≤
      Nat.card K ^ ((n - finrank K (fixSubGen (glNaturalRep n K) A)) *
        finrank K (fixSubGen (glNaturalRep n K) A)) := by
  have h1 := card_le_pow_finrank_unipotentAlgebra (K := K) (A := A) hA
  have h2 := finrank_unipotentAlgebra_le (K := K) hp hA
  have h3 : Nat.card K ^ finrank K (unipotentAlgebra A) ≤
      Nat.card K ^ ((n - finrank K (fixSubGen (glNaturalRep n K) A)) *
        finrank K (fixSubGen (glNaturalRep n K) A)) := by
    refine Nat.pow_le_pow_right (Nat.card_pos) ?_
    rw [Nat.mul_comm]
    exact h2
  exact h1.trans h3

theorem card_le_pow_half_sq {p : ℕ} [Finite K] [CharP K p] (hp : p.Prime)
    {A : Subgroup (GL (Fin n) K)} (hA : IsElemAbelian p A) :
    Nat.card A ≤ Nat.card K ^ (n ^ 2 / 4) := by
  have h := card_le_pow_of_elemAbelian (K := K) hp hA
  have hd : finrank K (fixSubGen (glNaturalRep n K) A) ≤ n := by
    simpa using Submodule.finrank_le (fixSubGen (glNaturalRep n K) A)
  refine h.trans (Nat.pow_le_pow_right (Nat.card_pos) ?_)
  rw [Nat.mul_comm]
  exact mul_sub_le_sq_div_four hd

theorem pRank_statedSL (n p a : ℕ) (K : Type) [Field K] [Finite K] [CharP K p]
    (hp : p.Prime) (hK : Nat.card K = p ^ a) :
    CFSG.Open.pRank p (StatedSL n K) = a * (n ^ 2 / 4) := by
  have hbound : ∀ k ∈ {k : ℕ | ∃ E : Subgroup (GL (Fin n) K),
      E ≤ StatedSL n K ∧ IsElemAbelian p E ∧ Nat.card E = p ^ k}, k ≤ a * (n ^ 2 / 4) := by
    rintro k ⟨E, -, hE, hEcard⟩
    have h := card_le_pow_half_sq (K := K) hp hE
    rw [hEcard, hK, ← pow_mul] at h
    exact (Nat.pow_le_pow_iff_right hp.one_lt).1 h
  have hbdd : BddAbove {k : ℕ | ∃ E : Subgroup (GL (Fin n) K),
      E ≤ StatedSL n K ∧ IsElemAbelian p E ∧ Nat.card E = p ^ k} :=
    ⟨a * (n ^ 2 / 4), hbound⟩
  refine le_antisymm ?_ ?_
  · unfold CFSG.Open.pRank
    exact csSup_le' hbound
  · obtain ⟨A, hA, hAcard⟩ := exists_elemAbelian_card_eq_statedSL' (n := n) (p := p) (K := K) hp
    let E : Subgroup (GL (Fin n) K) := A.map (StatedSL n K).subtype
    have hEel : IsElemAbelian p E := hA.map (StatedSL n K).subtype
    have hEcard : Nat.card E = p ^ (a * (n ^ 2 / 4)) := by
      rw [Subgroup.card_map_of_injective (StatedSL n K).subtype_injective, hAcard, hK, ← pow_mul]
    unfold CFSG.Open.pRank
    exact le_csSup hbdd ⟨E, Subgroup.map_subtype_le A, hEel, hEcard⟩

end CFSG.HardMathSupport.GuralnickMalle

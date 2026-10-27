module

public import CFSG.LieType.SeitzGeneration.SubfieldPairSLCore
public import CFSG.RankThree.PartOne.CTP.SeitzMaxSLPair
public import CFSG.LieType.SeitzGeneration.RootPairSL2

public section

namespace CFSG.LieType.SeitzGeneration

open Matrix CFSG.RankThree.PartOne.CTP
open CFSG.ComponentClassification.CatalogueBHigherLinearAction (slConjugation)

variable {n : ℕ} {K : Type} [Field K]

section Diag

variable {k : Subfield K}

theorem sq_diag_mem (u φ : Fin n → K) (hφu : φ ⬝ᵥ u = 0) (hoff : ∀ r s, r ≠ s → u r * φ s ∈ k)
    (r : Fin n) : (u r * φ r) ^ 2 ∈ k := by
  have h0 : (u r * φ r) * (φ ⬝ᵥ u) = 0 := by rw [hφu, mul_zero]
  rw [dotProduct, Finset.mul_sum, ← Finset.add_sum_erase _ _ (Finset.mem_univ r)] at h0
  have h1 : (u r * φ r) ^ 2 = -∑ s ∈ Finset.univ.erase r, (u r * φ s) * (u s * φ r) := by
    have e : ∀ s : Fin n, (u r * φ r) * (φ s * u s) = (u r * φ s) * (u s * φ r) := by
      intro s; ring
    rw [sq]
    simp only [e] at h0
    linear_combination h0
  rw [h1]
  refine k.neg_mem (k.sum_mem fun s hs => ?_)
  have hsr : s ≠ r := Finset.ne_of_mem_erase hs
  exact k.mul_mem (hoff r s hsr.symm) (hoff s r hsr)

end Diag

section Conj

@[expose] def colVec (A : GL (Fin n) K) (c : Fin n) : Fin n → K :=
  (A : Matrix (Fin n) (Fin n) K) *ᵥ (Pi.single c 1 : Fin n → K)

@[expose] def rowVec (A : GL (Fin n) K) (d : Fin n) : Fin n → K :=
  (Pi.single d 1 : Fin n → K) ᵥ* ((A⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)

theorem rowVec_dotProduct_colVec (A : GL (Fin n) K) {c d : Fin n} (hcd : c ≠ d) :
    rowVec A d ⬝ᵥ colVec A c = 0 := by
  rw [rowVec, colVec, dotProduct_mulVec, vecMul_vecMul, Units.inv_mul, vecMul_one,
    dotProduct_single_one]
  simp [hcd.symm]

theorem slConjugation_transvection (A : GL (Fin n) K) {c d : Fin n} (hcd : c ≠ d) (t : K) :
    slConjugation n K A (SpecialLinearGroup.transvection hcd t) =
      tv (colVec A c) (t • rowVec A d)
        (by rw [smul_dotProduct, rowVec_dotProduct_colVec A hcd, smul_zero]) := by
  rw [transvection_eq_tv hcd t, slConjugation_tv]
  apply Subtype.ext
  rw [tv_coe, tv_coe, colVec, rowVec, smul_vecMul]

theorem slConjugation_transvection_apply (A : GL (Fin n) K) {c d : Fin n} (hcd : c ≠ d) (t : K)
    (r s : Fin n) :
    ((slConjugation n K A (SpecialLinearGroup.transvection hcd t) :
      SpecialLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K) r s =
        (1 : Matrix (Fin n) (Fin n) K) r s + t * (colVec A c r * rowVec A d s) := by
  rw [slConjugation_transvection A hcd t, tv_coe, Matrix.add_apply, vecMulVec_apply,
    Pi.smul_apply, smul_eq_mul]
  ring

end Conj

section Main

variable [Finite K] {k : Subfield K} {p : ℕ}

theorem exists_offDiag_not_mem (hp : p.Prime) (hp2 : p ≠ 2) (hK : Nat.card K = Nat.card k ^ p)
    (A : GL (Fin n) K)
    (hne : (slSub n k).map (slConjugation n K A).toMonoidHom ≠ slSub n k) :
    ∃ c d : Fin n, c ≠ d ∧ ∃ r s : Fin n, r ≠ s ∧ colVec A c r * rowVec A d s ∉ k := by
  by_contra hall
  push Not at hall
  refine hne (map_conj_slSub_eq A fun i j hij t ht => ?_)
  rw [mem_slSub]
  intro r s
  rw [slConjugation_transvection_apply A hij t r s]
  have hdiag : colVec A i r * rowVec A j r ∈ k := by
    have hsq := sq_diag_mem (colVec A i) (rowVec A j) (rowVec_dotProduct_colVec A hij)
      (fun r' s' hr's' => hall i j hij r' s' hr's') r
    exact mem_of_quadratic hp hp2 hK (α := 0) (β := -(colVec A i r * rowVec A j r) ^ 2)
      k.zero_mem (k.neg_mem hsq) (by ring)
  have hentry : colVec A i r * rowVec A j s ∈ k := by
    by_cases hrs : r = s
    · subst hrs
      exact hdiag
    · exact hall i j hij r s hrs
  refine k.add_mem ?_ (k.mul_mem ht hentry)
  by_cases hrs : r = s
  · subst hrs
    simp [k.one_mem]
  · simp [Matrix.one_apply_ne hrs, k.zero_mem]

end Main

end CFSG.LieType.SeitzGeneration

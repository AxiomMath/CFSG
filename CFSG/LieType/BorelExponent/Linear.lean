module

public import CFSG.LieType.BorelExponent.Defs
public import CFSG.LocalAnalysis.ComponentInitial.LinearCoverModel
public import CFSG.LocalAnalysis.ComponentInitial.LinearHigherSylowNormalizer

public section

namespace CFSG.LieType.BorelExponent

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag

variable {K : Type} [Field K] {n : ℕ}

theorem pow_card_sub_one_mem_unitriangular_of_mem_upperTriangular [Finite K]
    {A : SpecialLinearGroup (Fin n) K} (hA : A ∈ upperTriangular n K) :
    A ^ (Nat.card K - 1) ∈ unitriangular n K := by
  have := Fintype.ofFinite K
  have hA' : (A : Matrix (Fin n) (Fin n) K).IsUpperTriangular :=
    mem_upperTriangular_iff_isUpperTriangular.mp hA
  have hdiag : ∀ k : ℕ, ∀ i : Fin n,
      ((A : Matrix (Fin n) (Fin n) K) ^ k) i i = (A : Matrix (Fin n) (Fin n) K) i i ^ k := by
    intro k
    induction k with
    | zero => intro i; simp
    | succ k ih =>
      intro i
      rw [pow_succ, mul_apply_self_of_isUpperTriangular (hA'.pow k) hA', ih, pow_succ]
  refine ⟨Subgroup.pow_mem _ hA _, fun i =>
    (congrFun (congrFun (Matrix.SpecialLinearGroup.coe_pow A _) i) i).trans ((hdiag _ i).trans ?_)⟩
  rw [Nat.card_eq_fintype_card]
  apply FiniteField.pow_card_sub_one_eq_one
  intro h0
  have h1 := coe_inv_apply_self_of_isUpperTriangular hA' i
  rw [h0, zero_mul] at h1
  exact zero_ne_one h1

theorem pow_card_sub_one_mem_projUnitriangular [Finite K] {b : projectiveSL n K}
    (hb : b ∈ projUpperTriangular n K) : b ^ (Nat.card K - 1) ∈ projUnitriangular n K := by
  obtain ⟨A, hA, rfl⟩ := hb
  exact ⟨_, pow_card_sub_one_mem_unitriangular_of_mem_upperTriangular hA, map_pow _ _ _⟩

theorem borelExponentAt_PSL : BorelExponentAt .PSL := by
  intro X _ _ m f hadm hLie
  obtain ⟨K, hK, hfin, hcard, ⟨e⟩⟩ := LinearCover.exists_mulEquiv_projectiveSL_of_lieModel hLie
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have := Fintype.ofFinite K
  have : CharP K 2 := charP_of_card_eq_prime_pow (by rw [← Nat.card_eq_fintype_card, hcard])
  have hm : 1 ≤ m := by
    have h := hadm
    simp [CFSG.Open.StatedLieAdmissible] at h
    omega
  obtain ⟨P, hP⟩ := exists_sylow_projUnitriangular (K := K) (n := m) 2 hm
  refine HasBorelExponent.of_mulEquiv e.symm (hasBorelExponent_of_sylow P ?_)
  intro x hx
  rw [hP, normalizer_projUnitriangular 2] at hx
  rw [hP]
  have h := pow_card_sub_one_mem_projUnitriangular hx
  rwa [hcard] at h

end CFSG.LieType.BorelExponent

end

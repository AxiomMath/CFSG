module

public import CFSG.ClassicalGroups.Linear.CentreGroups

public section

namespace CFSG.ClassicalGroups.Linear.Model

open Matrix CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
open CFSG.LargeExtraspecial.S4
open scoped MatrixGroups

theorem cube_apply_of_charTwo' {K V : Type} [Field K] [CharP K 2] [AddCommGroup V] [Module K V]
    {c c' : V} {φ φ' : V → K} {T : V → V}
    (hT : ∀ y, T y = y + φ' y • c' + (φ y + φ' y) • c)
    (hφT : ∀ y, φ (T y) = φ y + φ' y) (hφ'T : ∀ y, φ' (T y) = φ y + 2 * φ' y) (x : V) :
    T (T (T x)) = x := by
  have h2K : (2 : K) = 0 := CharTwo.two_eq_zero
  have h1 : T x = x + φ' x • c' + (φ x + φ' x) • c := hT x
  have h2 : T (T x) = T x + (φ x + 2 * φ' x) • c' + (2 * φ x + 3 * φ' x) • c := by
    rw [hT (T x), hφT x, hφ'T x]
    module
  have h3 : T (T (T x)) = T (T x) + (3 * φ x + 5 * φ' x) • c' + (5 * φ x + 8 * φ' x) • c := by
    rw [hT (T (T x)), hφT (T x), hφ'T (T x), hφT x, hφ'T x]
    module
  have hc8 : 8 * φ x + 12 * φ' x = 0 := by linear_combination (4 * φ x + 6 * φ' x) * h2K
  have hc4 : 4 * φ x + 8 * φ' x = 0 := by linear_combination (2 * φ x + 4 * φ' x) * h2K
  have hfin : T (T (T x)) = x + (8 * φ x + 12 * φ' x) • c + (4 * φ x + 8 * φ' x) • c' := by
    rw [h3, h2, h1]
    module
  rw [hfin, hc8, hc4]
  simp

theorem mulVec_transv_mul_transv {n : ℕ} {K : Type} [Field K] {c c' a a' : Fin n → K}
    (h2 : a ⬝ᵥ c' = 1) (y : Fin n → K) :
    ((1 + vecMulVec c a) * (1 + vecMulVec c' a')) *ᵥ y =
      y + (a' ⬝ᵥ y) • c' + ((a ⬝ᵥ y) + (a' ⬝ᵥ y)) • c := by
  rw [← Matrix.mulVec_mulVec, CFSG.LargeExtraspecial.S4.one_add_vecMulVec_mulVec c a,
    CFSG.LargeExtraspecial.S4.one_add_vecMulVec_mulVec c' a' y, dotProduct_add, dotProduct_smul,
    h2, smul_eq_mul, mul_one]

theorem pow_three_eq_one_of_transv {n : ℕ} {K : Type} [Field K] [CharP K 2]
    {c c' a a' : Fin n → K} (h1 : a ⬝ᵥ c = 0) (h2 : a ⬝ᵥ c' = 1) (h3 : a' ⬝ᵥ c = 1)
    (h4 : a' ⬝ᵥ c' = 0) {N : Matrix (Fin n) (Fin n) K}
    (hN : ∀ y, N *ᵥ y = y + (a' ⬝ᵥ y) • c' + ((a ⬝ᵥ y) + (a' ⬝ᵥ y)) • c) :
    N ^ 3 = 1 := by
  have hφT : ∀ y, a ⬝ᵥ (N *ᵥ y) = (a ⬝ᵥ y) + (a' ⬝ᵥ y) := by
    intro y
    rw [hN y]
    simp only [dotProduct_add, dotProduct_smul, smul_eq_mul, h1, h2, mul_zero, mul_one, add_zero]
  have hφ'T : ∀ y, a' ⬝ᵥ (N *ᵥ y) = (a ⬝ᵥ y) + 2 * (a' ⬝ᵥ y) := by
    intro y
    rw [hN y]
    simp only [dotProduct_add, dotProduct_smul, smul_eq_mul, h3, h4, mul_zero, mul_one, add_zero]
    ring
  have hcube : ∀ x, N *ᵥ (N *ᵥ (N *ᵥ x)) = x :=
    fun x => cube_apply_of_charTwo' (c := c) (c' := c') (T := fun y => N *ᵥ y)
      (φ := fun y => a ⬝ᵥ y) (φ' := fun y => a' ⬝ᵥ y) hN hφT hφ'T x
  apply Matrix.toLin'.injective
  apply LinearMap.ext
  intro x
  simp only [Matrix.toLin'_apply, Matrix.one_mulVec]
  rw [pow_three, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
  exact hcube x

theorem not_isPGroup_cg_sup (n : ℕ) (K : Type) [Field K] [CharP K 2] (c c' : Fin n → K)
    (hc : c ≠ 0) (hc' : c' ∉ Submodule.span K {c}) :
    ¬ IsPGroup 2 ↥(cg n K c ⊔ cg n K c') := by
  have hcn : c ∉ Submodule.span K {c'} := by
    intro h
    obtain ⟨t, ht⟩ := Submodule.mem_span_singleton.mp h
    have ht0 : t ≠ 0 := by
      rintro rfl
      exact hc (by rw [← ht, zero_smul])
    have hc'eq : c' = t⁻¹ • c := by
      rw [← ht, smul_smul, inv_mul_cancel₀ ht0, one_smul]
    apply hc'
    rw [hc'eq]
    exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self c)
  obtain ⟨a, h2, ha⟩ := exists_vec_of_notMem hc'
  obtain ⟨a', h3, ha'⟩ := exists_vec_of_notMem hcn
  have h1 : a ⬝ᵥ c = 0 := ha c (Submodule.mem_span_singleton_self c)
  have h4 : a' ⬝ᵥ c' = 0 := ha' c' (Submodule.mem_span_singleton_self c')
  have hXmem : psl n K (transvSL h1) ∈ cg n K c := by
    have hmem : ((transvSL h1 : StatedSL n K) : GL (Fin n) K) ∈ transvCenter n K c :=
      ⟨a, h1, coe_transvSL h1⟩
    unfold cg transvImage
    exact Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.mpr hmem)
  have hX'mem : psl n K (transvSL h4) ∈ cg n K c' := by
    have hmem : ((transvSL h4 : StatedSL n K) : GL (Fin n) K) ∈ transvCenter n K c' :=
      ⟨a', h4, coe_transvSL h4⟩
    unfold cg transvImage
    exact Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.mpr hmem)
  have hYM : (((transvSL h1 * transvSL h4 : StatedSL n K) : GL (Fin n) K) :
      Matrix (Fin n) (Fin n) K) = (1 + vecMulVec c a) * (1 + vecMulVec c' a') := by
    rw [Subgroup.coe_mul, Units.val_mul, coe_transvSL h1, coe_transvSL h4]
  have hNcube : ((1 + vecMulVec c a) * (1 + vecMulVec c' a')) ^ 3 = 1 :=
    pow_three_eq_one_of_transv (N := (1 + vecMulVec c a) * (1 + vecMulVec c' a')) h1 h2 h3 h4
      (fun y => mulVec_transv_mul_transv h2 y)
  have hns : ((transvSL h1 * transvSL h4 : StatedSL n K) : GL (Fin n) K) ∉
      StatedScalars (Fin n) K := by
    rintro ⟨u, hu⟩
    have hvec : (((transvSL h1 * transvSL h4 : StatedSL n K) : GL (Fin n) K) :
        Matrix (Fin n) (Fin n) K) *ᵥ c' = (u : K) • c' := by
      rw [← hu, GeneralLinearGroup.coe_scalar]
      ext i
      simp [Matrix.scalar_apply, Matrix.mulVec_diagonal]
    have hYc' : (((transvSL h1 * transvSL h4 : StatedSL n K) : GL (Fin n) K) :
        Matrix (Fin n) (Fin n) K) *ᵥ c' = c' + c := by
      rw [hYM, mulVec_transv_mul_transv h2 c', h4, h2]
      simp only [zero_smul, add_zero, one_smul]
    have hsum : c' + c = (u : K) • c' := hYc'.symm.trans hvec
    have hc_eq : c = ((u : K) - 1) • c' := by
      rw [sub_smul, one_smul, ← hsum]
      abel
    exact hcn (Submodule.mem_span_singleton.mpr ⟨(u : K) - 1, hc_eq.symm⟩)
  have hYcube : (transvSL h1 * transvSL h4 : StatedSL n K) ^ 3 = 1 := by
    apply Subtype.ext
    apply Units.ext
    rw [Subgroup.coe_pow, Units.val_pow_eq_pow_val, Subgroup.coe_one, Units.val_one, hYM]
    exact hNcube
  have hs3 : psl n K (transvSL h1 * transvSL h4) ^ 3 = 1 := by
    rw [← map_pow, hYcube, map_one]
  have hs1 : psl n K (transvSL h1 * transvSL h4) ≠ 1 := psl_ne_one hns
  have hord : orderOf (psl n K (transvSL h1 * transvSL h4)) = 3 := orderOf_eq_prime hs3 hs1
  have hY : psl n K (transvSL h1 * transvSL h4) ∈ cg n K c ⊔ cg n K c' := by
    rw [map_mul]
    exact mul_mem (Subgroup.mem_sup_left hXmem) (Subgroup.mem_sup_right hX'mem)
  intro hP
  obtain ⟨k, hk⟩ := hP ⟨psl n K (transvSL h1 * transvSL h4), hY⟩
  have hpow : psl n K (transvSL h1 * transvSL h4) ^ 2 ^ k = 1 := by
    have h := congrArg Subtype.val hk
    rw [Subgroup.coe_pow, Subgroup.coe_one] at h
    exact h
  have hdvd : orderOf (psl n K (transvSL h1 * transvSL h4)) ∣ 2 ^ k :=
    orderOf_dvd_of_pow_eq_one hpow
  rw [hord] at hdvd
  have h32 : 3 ∣ 2 := Nat.Prime.dvd_of_dvd_pow Nat.prime_three hdvd
  omega

end CFSG.ClassicalGroups.Linear.Model

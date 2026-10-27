module

public import CFSG.ClassicalInvolution.Phan.PhanDn.StdFamilyDisj

public section

namespace CFSG.ClassicalInvolution.PhanDn

open CFSG.ClassicalInvolution.Phan CFSG.ClassicalGroups.Unitary CFSG.LieType.Universal.Unitary
  CFSG.ClassicalGroups.Orthogonal CFSG.ClassicalInvolution.Models.OrthogonalPairs
  CFSG.LieType.BorelTits
open QuadraticMap

variable {F K : Type} [Field F] [Field K] [Finite K] [Algebra F K] {f : ℕ} [CharP K 2]
variable (E : QuadExt F K (unitaryInvolution K 2 f))

@[expose] noncomputable def nodeVec {m : ℕ} (k : Fin m) (x y : K) : Fin (m + 1) → K :=
  Pi.single ⟨k.val, by omega⟩ x + Pi.single ⟨k.val + 1, by omega⟩ y

omit [Finite K] [CharP K 2] in
theorem nodeVec_apply_left {m : ℕ} (k : Fin m) (x y : K) :
    nodeVec k x y ⟨k.val, by omega⟩ = x := by
  simp [nodeVec, Fin.ext_iff]

omit [Finite K] [CharP K 2] in
theorem nodeVec_apply_right {m : ℕ} (k : Fin m) (x y : K) :
    nodeVec k x y ⟨k.val + 1, by omega⟩ = y := by
  simp [nodeVec, Fin.ext_iff]

omit [Finite K] [CharP K 2] in
theorem nodeVec_apply_of_ne {m : ℕ} (k : Fin m) (x y : K) {d : Fin (m + 1)}
    (h1 : d.val ≠ k.val) (h2 : d.val ≠ k.val + 1) : nodeVec k x y d = 0 := by
  simp [nodeVec, Fin.ext_iff, h1, h2]

omit [Finite K] [CharP K 2] in
theorem smul_nodeVec {m : ℕ} (k : Fin m) (a x y : K) :
    a • nodeVec k x y = nodeVec k (a * x) (a * y) := by
  funext d
  simp only [nodeVec, Pi.smul_apply, Pi.add_apply, Pi.single_apply, smul_eq_mul]
  split_ifs <;> ring

theorem sum_mul_sigma_nodeVec {m : ℕ} (k : Fin m) (x y : K) (v : Fin (m + 1) → K) :
    ∑ i, v i * unitaryInvolution K 2 f (nodeVec k x y i) =
      v ⟨k.val, by omega⟩ * unitaryInvolution K 2 f x +
        v ⟨k.val + 1, by omega⟩ * unitaryInvolution K 2 f y := by
  have hne : (⟨k.val, by omega⟩ : Fin (m + 1)) ≠ ⟨k.val + 1, by omega⟩ := by
    simp [Fin.ext_iff]
  simp only [nodeVec, Pi.add_apply, map_add, mul_add, Finset.sum_add_distrib, Pi.single_apply,
    apply_ite (unitaryInvolution K 2 f), map_zero, mul_ite, mul_zero, Finset.sum_ite_eq',
    Finset.mem_univ, if_true]

theorem algebraMap_polar_Qn_nodeVec {m : ℕ} (k : Fin m) (x y : K) (v : Fin (m + 1) → K) :
    algebraMap F K (polar (Qn E (m + 1)) v (nodeVec k x y)) =
      (v ⟨k.val, by omega⟩ * unitaryInvolution K 2 f x +
        v ⟨k.val + 1, by omega⟩ * unitaryInvolution K 2 f y) +
      unitaryInvolution K 2 f (v ⟨k.val, by omega⟩ * unitaryInvolution K 2 f x +
        v ⟨k.val + 1, by omega⟩ * unitaryInvolution K 2 f y) := by
  rw [algebraMap_polar_Qn, sum_mul_sigma_nodeVec]

theorem algebraMap_Qn_nodeVec {m : ℕ} (k : Fin m) (x y : K) :
    algebraMap F K (Qn E (m + 1) (nodeVec k x y)) =
      x * unitaryInvolution K 2 f x + y * unitaryInvolution K 2 f y := by
  rw [algebraMap_Qn, sum_mul_sigma_nodeVec, nodeVec_apply_left, nodeVec_apply_right]

include E in
theorem exists_su_transv {x y a : K}
    (hxy : x * unitaryInvolution K 2 f x + y * unitaryInvolution K 2 f y = 0)
    (ha : unitaryInvolution K 2 f a = a) :
    ∃ A : Su K 2 f 2, ((A : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) =
      !![1 + a * (x * unitaryInvolution K 2 f x), a * (x * unitaryInvolution K 2 f y);
        a * (y * unitaryInvolution K 2 f x), 1 + a * (y * unitaryInvolution K 2 f y)] := by
  set σ := unitaryInvolution K 2 f with hσ
  have hinv : ∀ c, σ (σ c) = c := E.isUnitary.invol
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  set M : Matrix (Fin 2) (Fin 2) K :=
    !![1 + a * (x * σ x), a * (x * σ y); a * (y * σ x), 1 + a * (y * σ y)] with hM
  have hdet : M.det = 1 := by
    rw [hM, Matrix.det_fin_two_of]
    linear_combination a * hxy
  have hU : conjTr σ M * M = 1 := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [hM, conjTr, Matrix.mul_apply, Fin.sum_univ_two, map_add, map_mul, ha, hinv]
    · linear_combination (a * x * σ x) * h2 + (a ^ 2 * x * σ x) * hxy
    · linear_combination (a * x * σ y) * h2 + (a ^ 2 * x * σ y) * hxy
    · linear_combination (a * y * σ x) * h2 + (a ^ 2 * y * σ x) * hxy
    · linear_combination (a * y * σ y) * h2 + (a ^ 2 * y * σ y) * hxy
  exact ⟨⟨Matrix.GeneralLinearGroup.mkOfDetNeZero M (by rw [hdet]; exact one_ne_zero),
    hdet, hU⟩, rfl⟩

omit [Finite K] [CharP K 2] in
theorem smul_nodeVec_base {m : ℕ} (k : Fin m) (c : F) (x y : K) :
    c • nodeVec k x y = nodeVec k (algebraMap F K c * x) (algebraMap F K c * y) := by
  rw [← smul_nodeVec, algebraMap_smul]

theorem exists_stdChainIota_eq_eichler {m : ℕ} (k : Fin m) {l : K}
    (hl : l + unitaryInvolution K 2 f l = 1) {x y : K}
    (hxy : x * unitaryInvolution K 2 f x + y * unitaryInvolution K 2 f y = 0) (c : F) :
    ∃ A : Su K 2 f 2, stdChainIota (F := F) (f := f) m k A =
      eichler (Qn E (m + 1)) (nodeVec k x y) (c • nodeVec k (l * x) (l * y)) := by
  have hinv : ∀ c, unitaryInvolution K 2 f (unitaryInvolution K 2 f c) = c :=
    E.isUnitary.invol
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  have ha : unitaryInvolution K 2 f (algebraMap F K c) = algebraMap F K c := E.fix c
  obtain ⟨A, hA⟩ := exists_su_transv E hxy ha
  refine ⟨A, ?_⟩
  rw [smul_nodeVec_base]
  set a := algebraMap F K c with ha_def
  have hQu : Qn E (m + 1) (nodeVec k x y) = 0 := by
    apply (algebraMap F K).injective
    rw [algebraMap_Qn_nodeVec, map_zero, hxy]
  have hQw : Qn E (m + 1) (nodeVec k (a * (l * x)) (a * (l * y))) = 0 := by
    apply (algebraMap F K).injective
    rw [algebraMap_Qn_nodeVec, map_zero]
    simp only [map_mul, ha]
    linear_combination (a * a * l * unitaryInvolution K 2 f l) * hxy
  have hpuw : polar (Qn E (m + 1)) (nodeVec k x y) (nodeVec k (a * (l * x)) (a * (l * y))) = 0 := by
    apply (algebraMap F K).injective
    rw [algebraMap_polar_Qn_nodeVec, nodeVec_apply_left, nodeVec_apply_right, map_zero]
    simp only [map_add, map_mul, hinv, ha]
    linear_combination (a * (unitaryInvolution K 2 f l + l)) * hxy
  refine LinearEquiv.ext fun v => funext fun d => ?_
  rw [eichler_apply hQu hpuw, hQw, zero_mul, add_zero, Pi.sub_apply, Pi.add_apply,
    Pi.smul_apply, Pi.smul_apply, Algebra.smul_def, Algebra.smul_def,
    algebraMap_polar_Qn_nodeVec, algebraMap_polar_Qn_nodeVec]
  simp only [map_add, map_mul, hinv, ha]
  by_cases hd0 : d.val = k.val
  · have hd : d = ⟨k.val, by omega⟩ := Fin.ext hd0
    rw [hd, stdChainIota_apply, blockEmb2_smul_apply_left, hA, nodeVec_apply_left, nodeVec_apply_left]
    simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.empty_val', Matrix.cons_val_fin_one]
    linear_combination (-(a * x * (v ⟨k.val, by omega⟩ * unitaryInvolution K 2 f x +
      v ⟨k.val + 1, by omega⟩ * unitaryInvolution K 2 f y))) * hl +
      (a * x * (v ⟨k.val, by omega⟩ * unitaryInvolution K 2 f x +
        v ⟨k.val + 1, by omega⟩ * unitaryInvolution K 2 f y) * unitaryInvolution K 2 f l) * h2
  by_cases hd1 : d.val = k.val + 1
  · have hd : d = ⟨k.val + 1, by omega⟩ := Fin.ext hd1
    rw [hd, stdChainIota_apply, blockEmb2_smul_apply_right, hA, nodeVec_apply_right,
      nodeVec_apply_right]
    simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.empty_val', Matrix.cons_val_fin_one]
    linear_combination (-(a * y * (v ⟨k.val, by omega⟩ * unitaryInvolution K 2 f x +
      v ⟨k.val + 1, by omega⟩ * unitaryInvolution K 2 f y))) * hl +
      (a * y * (v ⟨k.val, by omega⟩ * unitaryInvolution K 2 f x +
        v ⟨k.val + 1, by omega⟩ * unitaryInvolution K 2 f y) * unitaryInvolution K 2 f l) * h2
  · rw [stdChainIota_apply_of_not_mem k A v (by omega), nodeVec_apply_of_ne k _ _ hd0 hd1,
      nodeVec_apply_of_ne k _ _ hd0 hd1]
    ring

theorem algebraMap_polar_Qn_nodeVec_nodeVec {m : ℕ} (k : Fin m) (x y x' y' : K) :
    algebraMap F K (polar (Qn E (m + 1)) (nodeVec k x y) (nodeVec k x' y')) =
      (x * unitaryInvolution K 2 f x' + y * unitaryInvolution K 2 f y') +
        unitaryInvolution K 2 f (x * unitaryInvolution K 2 f x' +
          y * unitaryInvolution K 2 f y') := by
  rw [algebraMap_polar_Qn_nodeVec, nodeVec_apply_left, nodeVec_apply_right]

section Pairs

variable {m : ℕ} (k : Fin m) {l : K} (hl : l + unitaryInvolution K 2 f l = 1)

@[expose] noncomputable def nodeHypPair₁ : HypPair (Qn E (m + 1)) where
  e := nodeVec k 1 1
  f := nodeVec k (l * l) (l * unitaryInvolution K 2 f l)
  Q_e := by
    apply (algebraMap F K).injective
    rw [algebraMap_Qn_nodeVec, map_zero]
    simp only [map_one, mul_one]
    exact CharTwo.add_self_eq_zero 1
  Q_f := by
    apply (algebraMap F K).injective
    rw [algebraMap_Qn_nodeVec, map_zero]
    simp only [map_mul, E.isUnitary.invol]
    linear_combination (l ^ 2 * unitaryInvolution K 2 f l ^ 2) * (CharTwo.two_eq_zero : (2 : K) = 0)
  polar_ef := by
    apply (algebraMap F K).injective
    rw [algebraMap_polar_Qn_nodeVec_nodeVec, map_one]
    simp only [map_add, map_mul, map_one, E.isUnitary.invol]
    linear_combination (l + unitaryInvolution K 2 f l + 1) * hl

@[expose] noncomputable def nodeHypPair₂ : HypPair (Qn E (m + 1)) where
  e := nodeVec k l (unitaryInvolution K 2 f l)
  f := nodeVec k (l * 1) (l * 1)
  Q_e := by
    apply (algebraMap F K).injective
    rw [algebraMap_Qn_nodeVec, map_zero]
    simp only [E.isUnitary.invol]
    linear_combination (l * unitaryInvolution K 2 f l) * (CharTwo.two_eq_zero : (2 : K) = 0)
  Q_f := by
    apply (algebraMap F K).injective
    rw [algebraMap_Qn_nodeVec, map_zero]
    simp only [mul_one]
    linear_combination (l * unitaryInvolution K 2 f l) * (CharTwo.two_eq_zero : (2 : K) = 0)
  polar_ef := by
    apply (algebraMap F K).injective
    rw [algebraMap_polar_Qn_nodeVec_nodeVec, map_one]
    simp only [map_add, map_mul, mul_one, E.isUnitary.invol]
    linear_combination (l + unitaryInvolution K 2 f l + 1) * hl

theorem nodeHypPair_orth : (nodeHypPair₁ E k hl).Orth (nodeHypPair₂ E k hl) := by
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  have hinv := E.isUnitary.invol
  refine ⟨?_, ?_, ?_, ?_⟩ <;> apply (algebraMap F K).injective <;>
    simp only [nodeHypPair₁, nodeHypPair₂, algebraMap_polar_Qn_nodeVec_nodeVec, map_zero, map_add,
      map_mul, mul_one, one_mul, hinv]
  · linear_combination (l + unitaryInvolution K 2 f l) * h2
  · linear_combination (l + unitaryInvolution K 2 f l) * h2
  · linear_combination (l ^ 2 * unitaryInvolution K 2 f l + unitaryInvolution K 2 f l ^ 2 * l) * h2
  · linear_combination (l ^ 2 * unitaryInvolution K 2 f l + l * unitaryInvolution K 2 f l ^ 2) * h2

theorem exists_stdChainIota_eq_eichler_upper (c : F) :
    ∃ A : Su K 2 f 2, stdChainIota (F := F) (f := f) m k A =
      eichler (Qn E (m + 1)) (nodeHypPair₁ E k hl).e (c • (nodeHypPair₂ E k hl).f) :=
  exists_stdChainIota_eq_eichler E k hl (by
    simp only [map_one, mul_one]
    exact CharTwo.add_self_eq_zero 1) c

theorem exists_stdChainIota_eq_eichler_lower (c : F) :
    ∃ A : Su K 2 f 2, stdChainIota (F := F) (f := f) m k A =
      eichler (Qn E (m + 1)) (nodeHypPair₂ E k hl).e (c • (nodeHypPair₁ E k hl).f) :=
  exists_stdChainIota_eq_eichler E k hl (by
    simp only [E.isUnitary.invol]
    linear_combination (l * unitaryInvolution K 2 f l) * (CharTwo.two_eq_zero : (2 : K) = 0)) c

end Pairs

end CFSG.ClassicalInvolution.PhanDn

end

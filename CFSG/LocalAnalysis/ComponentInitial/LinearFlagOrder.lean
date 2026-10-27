module

public import CFSG.LocalAnalysis.ComponentInitial.LinearFlagData
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Card
public import Mathlib.FieldTheory.Finite.Basic
public import Mathlib.GroupTheory.Sylow

public noncomputable section

namespace CFSG.LocalAnalysis.ComponentInitial

namespace LinearFlag

open Matrix

theorem prod_range_succ_eq_prod_Icc (f : ℕ → ℕ) (n : ℕ) :
    ∏ j ∈ Finset.range n, f (j + 1) = ∏ j ∈ Finset.Icc 1 n, f j := by
  induction n with
  | zero => rfl
  | succ n ih => rw [Finset.prod_range_succ, ih, Finset.prod_Icc_succ_top (by omega)]

theorem prod_pow_sub_pow_eq (q n : ℕ) :
    ∏ i : Fin n, (q ^ n - q ^ (i : ℕ)) =
      q ^ (n * (n - 1) / 2) * ∏ j ∈ Finset.Icc 1 n, (q ^ j - 1) := by
  rw [Fin.prod_univ_eq_prod_range (fun i => q ^ n - q ^ i) n]
  have h1 : ∀ i ∈ Finset.range n, q ^ n - q ^ i = q ^ i * (q ^ (n - 1 - i + 1) - 1) := by
    intro i hi
    rw [Finset.mem_range] at hi
    rw [Nat.mul_sub_one, ← pow_add, show i + (n - 1 - i + 1) = n by omega]
  rw [Finset.prod_congr rfl h1, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum,
    Finset.sum_range_id, Finset.prod_range_reflect (fun j => q ^ (j + 1) - 1) n,
    prod_range_succ_eq_prod_Icc (fun j => q ^ j - 1)]

theorem prod_Icc_one_eq (f : ℕ → ℕ) {n : ℕ} (hn : 1 ≤ n) :
    ∏ j ∈ Finset.Icc 1 n, f j = f 1 * ∏ j ∈ Finset.Icc 2 n, f j := by
  rw [Finset.Icc_eq_cons_Ioc hn, Finset.prod_cons]
  rfl

theorem not_dvd_prod_pow_sub_one {p q : ℕ} (hp : p.Prime) (hpq : p ∣ q) (hq : 1 ≤ q) (n : ℕ) :
    ¬ p ∣ ∏ j ∈ Finset.Icc 2 n, (q ^ j - 1) := by
  rw [Prime.dvd_finsetProd_iff hp.prime]
  rintro ⟨j, hj, hdvd⟩
  rw [Finset.mem_Icc] at hj
  have hqj : p ∣ q ^ j := hpq.trans (dvd_pow_self q (by omega))
  have h1 : 1 ≤ q ^ j := Nat.one_le_pow _ _ hq
  have : p ∣ q ^ j - (q ^ j - 1) := Nat.dvd_sub hqj hdvd
  rw [Nat.sub_sub_self h1] at this
  exact hp.one_lt.ne' (Nat.dvd_one.mp this)

variable {K : Type*} [Field K]

theorem card_GL_eq [Finite K] (n : ℕ) :
    Nat.card (GL (Fin n) K) =
      Nat.card K ^ (n * (n - 1) / 2) * ∏ j ∈ Finset.Icc 1 n, (Nat.card K ^ j - 1) := by
  have := Fintype.ofFinite K
  rw [card_GL_field, Nat.card_eq_fintype_card, prod_pow_sub_pow_eq]

theorem card_SL_eq [Finite K] {n : ℕ} (hn : 1 ≤ n) :
    Nat.card (SpecialLinearGroup (Fin n) K) =
      Nat.card K ^ (n * (n - 1) / 2) * ∏ j ∈ Finset.Icc 2 n, (Nat.card K ^ j - 1) := by
  have : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  have h := card_SL_mul_card_units (n := Fin n) (R := K)
  rw [Nat.card_units, card_GL_eq, prod_Icc_one_eq _ hn, pow_one, mul_left_comm,
    mul_comm (Nat.card K - 1)] at h
  have hq : 0 < Nat.card K - 1 := by
    have := Finite.one_lt_card (α := K)
    omega
  exact Nat.eq_of_mul_eq_mul_right hq h

@[expose] def unitriangularMatrix {n : ℕ} (f : {ij : Fin n × Fin n // ij.1 < ij.2} → K) :
    Matrix (Fin n) (Fin n) K :=
  Matrix.of fun i j => if h : i < j then f ⟨(i, j), h⟩ else if i = j then 1 else 0

theorem unitriangularMatrix_isUpperTriangular {n : ℕ}
    (f : {ij : Fin n × Fin n // ij.1 < ij.2} → K) :
    (unitriangularMatrix f).IsUpperTriangular := by
  intro i j hij
  have hji : j < i := hij
  change (if h : i < j then f ⟨(i, j), h⟩ else if i = j then 1 else 0) = 0
  rw [dite_eq_right (not_lt.mpr hji.le), ite_eq_right (ne_of_gt hji)]

theorem unitriangularMatrix_apply_self {n : ℕ} (f : {ij : Fin n × Fin n // ij.1 < ij.2} → K)
    (i : Fin n) : unitriangularMatrix f i i = 1 := by
  change (if h : i < i then f ⟨(i, i), h⟩ else if i = i then 1 else 0) = 1
  rw [dite_eq_right (lt_irrefl i), ite_eq_left rfl]

theorem det_unitriangularMatrix {n : ℕ} (f : {ij : Fin n × Fin n // ij.1 < ij.2} → K) :
    (unitriangularMatrix f).det = 1 := by
  rw [det_of_isUpperTriangular (unitriangularMatrix_isUpperTriangular f)]
  exact Finset.prod_eq_one fun i _ => unitriangularMatrix_apply_self f i

@[expose] def unitriangularEquiv (n : ℕ) :
    unitriangular n K ≃ ({ij : Fin n × Fin n // ij.1 < ij.2} → K) where
  toFun A ij := ((A : SpecialLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K) ij.1.1 ij.1.2
  invFun f := ⟨⟨unitriangularMatrix f, det_unitriangularMatrix f⟩,
    fun _ _ hij => unitriangularMatrix_isUpperTriangular f hij,
    unitriangularMatrix_apply_self f⟩
  left_inv A := by
    obtain ⟨A, hA1, hA2⟩ := A
    refine Subtype.ext (Subtype.ext (Matrix.ext fun i j => ?_))
    change (if h : i < j then (A : Matrix (Fin n) (Fin n) K) i j else if i = j then 1 else 0) =
      (A : Matrix (Fin n) (Fin n) K) i j
    rcases lt_trichotomy i j with h | rfl | h
    · rw [dite_eq_left h]
    · rw [dite_eq_right (lt_irrefl i), ite_eq_left rfl, hA2]
    · rw [dite_eq_right (not_lt.mpr h.le), ite_eq_right (ne_of_gt h), hA1 i j h]
  right_inv f := by
    funext ij
    change (if h : ij.1.1 < ij.1.2 then f ⟨(ij.1.1, ij.1.2), h⟩ else _) = f ij
    rw [dite_eq_left ij.2]

theorem card_unitriangular [Finite K] (n : ℕ) :
    Nat.card (unitriangular n K) = Nat.card K ^ (n * (n - 1) / 2) := by
  rw [Nat.card_congr (unitriangularEquiv n), Nat.card_fun, Nat.card_eq_fintype_card
    (α := {ij : Fin n × Fin n // ij.1 < ij.2}), Fintype.card_subtype,
    Fintype.card_product_filter_lt, Fintype.card_fin, Nat.choose_two_right]

theorem card_scalars_dvd [Finite K] {n : ℕ} (hn : 1 ≤ n) :
    Nat.card (scalars n K) ∣ Nat.card K - 1 := by
  rw [scalars_eq_center, Nat.card_congr
    (SpecialLinearGroup.center_equiv_rootsOfUnity' (⟨0, hn⟩ : Fin n)).toEquiv, ← Nat.card_units]
  exact Subgroup.card_subgroup_dvd_card _

theorem card_projectiveSL [Finite K] (n : ℕ) :
    Nat.card (projectiveSL n K) =
      Nat.card (SpecialLinearGroup (Fin n) K) / Nat.card (scalars n K) := by
  rw [(scalars n K).card_eq_card_quotient_mul_card_subgroup, Nat.mul_div_cancel _ Nat.card_pos]

theorem unitriangular_inf_scalars (n : ℕ) : unitriangular n K ⊓ scalars n K = ⊥ := by
  rw [eq_bot_iff]
  rintro A ⟨⟨-, hA⟩, c, -, hc⟩
  rw [Subgroup.mem_bot]
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · exact Subsingleton.elim _ _
  have hc1 : (c : K) = 1 := by
    have h := hA ⟨0, hn⟩
    rwa [hc, scalar_apply, diagonal_apply_eq] at h
  refine Subtype.ext ?_
  rw [hc, hc1, map_one, SpecialLinearGroup.coe_one]

theorem proj_injOn_unitriangular (n : ℕ) {A B : SpecialLinearGroup (Fin n) K}
    (hA : A ∈ unitriangular n K) (hB : B ∈ unitriangular n K) (h : proj n K A = proj n K B) :
    A = B := by
  have hm : A⁻¹ * B ∈ unitriangular n K ⊓ scalars n K :=
    ⟨(unitriangular n K).mul_mem ((unitriangular n K).inv_mem hA) hB, proj_eq_proj_iff.mp h⟩
  rw [unitriangular_inf_scalars, Subgroup.mem_bot, inv_mul_eq_one] at hm
  exact hm

@[expose] def unitriangularEquivProj (n : ℕ) : unitriangular n K ≃* projUnitriangular n K :=
  MulEquiv.ofBijective ((proj n K).subgroupMap (unitriangular n K))
    ⟨fun A B h => Subtype.ext (proj_injOn_unitriangular n A.2 B.2 (congrArg Subtype.val h)),
      (proj n K).subgroupMap_surjective _⟩

theorem card_projUnitriangular [Finite K] (n : ℕ) :
    Nat.card (projUnitriangular n K) = Nat.card K ^ (n * (n - 1) / 2) := by
  rw [← Nat.card_congr (unitriangularEquivProj n).toEquiv, card_unitriangular]

theorem exists_sylow_unitriangular [Finite K] (p : ℕ) [CharP K p] {n : ℕ} (hn : 1 ≤ n) :
    ∃ P : Sylow p (SpecialLinearGroup (Fin n) K), (P : Subgroup _) = unitriangular n K := by
  have := Fintype.ofFinite K
  obtain ⟨k, hp, hk⟩ := FiniteField.card K p
  have : Fact p.Prime := ⟨hp⟩
  rw [← Nat.card_eq_fintype_card] at hk
  have hpq : p ∣ Nat.card K := by
    rw [hk]
    exact dvd_pow_self p k.ne_zero
  have hU : IsPGroup p (unitriangular n K) := by
    refine IsPGroup.of_card (n := k * (n * (n - 1) / 2)) ?_
    rw [card_unitriangular, hk, pow_mul]
  have hindex : (unitriangular n K).index = ∏ j ∈ Finset.Icc 2 n, (Nat.card K ^ j - 1) := by
    have h := (unitriangular n K).card_mul_index
    rw [card_unitriangular, card_SL_eq hn] at h
    exact Nat.eq_of_mul_eq_mul_left (pow_pos Finite.card_pos _) h
  refine ⟨hU.toSylow ?_, rfl⟩
  rw [hindex]
  exact not_dvd_prod_pow_sub_one hp hpq Finite.card_pos n

theorem exists_sylow_projUnitriangular [Finite K] (p : ℕ) [CharP K p] {n : ℕ} (hn : 1 ≤ n) :
    ∃ P : Sylow p (projectiveSL n K), (P : Subgroup _) = projUnitriangular n K := by
  have := Fintype.ofFinite K
  obtain ⟨k, hp, hk⟩ := FiniteField.card K p
  have : Fact p.Prime := ⟨hp⟩
  rw [← Nat.card_eq_fintype_card] at hk
  have hpq : p ∣ Nat.card K := by
    rw [hk]
    exact dvd_pow_self p k.ne_zero
  have hU : IsPGroup p (projUnitriangular n K) := by
    refine IsPGroup.of_card (n := k * (n * (n - 1) / 2)) ?_
    rw [card_projUnitriangular, hk, pow_mul]
  have hZ := (scalars n K).card_eq_card_quotient_mul_card_subgroup
  have hP := (projUnitriangular n K).card_mul_index
  rw [card_SL_eq hn] at hZ
  rw [card_projUnitriangular] at hP
  have hprod : (projUnitriangular n K).index * Nat.card (scalars n K) =
      ∏ j ∈ Finset.Icc 2 n, (Nat.card K ^ j - 1) := by
    refine Nat.eq_of_mul_eq_mul_left (pow_pos (Finite.card_pos (α := K)) (n * (n - 1) / 2)) ?_
    rw [hZ, ← hP, mul_assoc]
  refine ⟨hU.toSylow fun h => ?_, rfl⟩
  exact not_dvd_prod_pow_sub_one hp hpq Finite.card_pos n (hprod ▸ h.mul_right _)

theorem linear_order [Finite K] (p : ℕ) [CharP K p] (q : ℕ) (hq : Nat.card K = q) {n : ℕ}
    (hn : 2 ≤ n) :
    Nat.card (GL (Fin n) K) = q ^ (n * (n - 1) / 2) * ∏ j ∈ Finset.Icc 1 n, (q ^ j - 1) ∧
      Nat.card (SpecialLinearGroup (Fin n) K) =
        q ^ (n * (n - 1) / 2) * ∏ j ∈ Finset.Icc 2 n, (q ^ j - 1) ∧
      Nat.card (unitriangular n K) = q ^ (n * (n - 1) / 2) ∧
      Nat.card (scalars n K) ∣ q - 1 ∧
      Nat.card (projectiveSL n K) =
        Nat.card (SpecialLinearGroup (Fin n) K) / Nat.card (scalars n K) ∧
      (∃ P : Sylow p (SpecialLinearGroup (Fin n) K), (P : Subgroup _) = unitriangular n K) ∧
      unitriangular n K ⊓ scalars n K = ⊥ ∧
      (∃ P : Sylow p (projectiveSL n K), (P : Subgroup _) = projUnitriangular n K) ∧
      Nat.card (projUnitriangular n K) = q ^ (n * (n - 1) / 2) := by
  subst hq
  have hn1 : 1 ≤ n := by omega
  exact ⟨card_GL_eq n, card_SL_eq hn1, card_unitriangular n, card_scalars_dvd hn1,
    card_projectiveSL n, exists_sylow_unitriangular p hn1, unitriangular_inf_scalars n,
    exists_sylow_projUnitriangular p hn1, card_projUnitriangular n⟩

end LinearFlag

end CFSG.LocalAnalysis.ComponentInitial

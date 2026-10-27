module

public import CFSG.LinearAlgebra.LinearGroups.ProjectiveFixedPoints
public import CFSG.LinearAlgebra.SL2CharTwoFixedVector
public import CFSG.LinearAlgebra.SL2MinimalFaithfulMatrix
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Topology.Compactification.OnePoint.ProjectiveLine

public section

namespace CFSG.LinearAlgebra

open Matrix

variable {K : Type*} [Field K]

theorem exists_eq_smul_of_mulVec_eq_self (x : Matrix.SpecialLinearGroup (Fin 2) K) (hx : x ≠ 1)
    {e v : Fin 2 → K} (he : e ≠ 0)
    (hxe : (x : Matrix (Fin 2) (Fin 2) K) *ᵥ e = e)
    (hxv : (x : Matrix (Fin 2) (Fin 2) K) *ᵥ v = v) :
    ∃ c : K, v = c • e := by
  have hM : (x : Matrix (Fin 2) (Fin 2) K) - 1 ≠ 0 := by
    intro h
    apply hx
    exact Subtype.ext (sub_eq_zero.mp h)
  refine CFSG.LinearGroups.exists_smul_eq_of_mulVec_eq_zero hM he ?_ ?_
  · rw [Matrix.sub_mulVec, hxe, Matrix.one_mulVec, sub_self]
  · rw [Matrix.sub_mulVec, hxv, Matrix.one_mulVec, sub_self]

private theorem inv_mulVec_mulVec (x : Matrix.SpecialLinearGroup (Fin 2) K) (v : Fin 2 → K) :
    (↑x⁻¹ : Matrix (Fin 2) (Fin 2) K) *ᵥ ((x : Matrix (Fin 2) (Fin 2) K) *ᵥ v) = v := by
  rw [Matrix.mulVec_mulVec, ← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel,
    Matrix.SpecialLinearGroup.coe_one, Matrix.one_mulVec]

theorem ne_zero_of_mulVec_eq_smul {x : Matrix.SpecialLinearGroup (Fin 2) K} {e : Fin 2 → K}
    (he : e ≠ 0) {c : K} (hx : (x : Matrix (Fin 2) (Fin 2) K) *ᵥ e = c • e) : c ≠ 0 := by
  rintro rfl
  rw [zero_smul] at hx
  exact he (by rw [← inv_mulVec_mulVec x e, hx, Matrix.mulVec_zero])

theorem inv_mulVec_eq_inv_smul_of_mulVec_eq_smul {x : Matrix.SpecialLinearGroup (Fin 2) K}
    {e : Fin 2 → K} {c : K} (hc : c ≠ 0) (hx : (x : Matrix (Fin 2) (Fin 2) K) *ᵥ e = c • e) :
    (↑x⁻¹ : Matrix (Fin 2) (Fin 2) K) *ᵥ e = c⁻¹ • e := by
  have h := inv_mulVec_mulVec x e
  rw [hx, Matrix.mulVec_smul] at h
  exact (eq_inv_smul_iff₀ hc).mpr h

theorem commutator_mulVec_eq_self_of_mulVec_eq_smul {x y : Matrix.SpecialLinearGroup (Fin 2) K}
    {e : Fin 2 → K} (he : e ≠ 0) {c d : K}
    (hx : (x : Matrix (Fin 2) (Fin 2) K) *ᵥ e = c • e)
    (hy : (y : Matrix (Fin 2) (Fin 2) K) *ᵥ e = d • e) :
    (↑(x * y * x⁻¹ * y⁻¹) : Matrix (Fin 2) (Fin 2) K) *ᵥ e = e := by
  have hc := ne_zero_of_mulVec_eq_smul he hx
  have hd := ne_zero_of_mulVec_eq_smul he hy
  simp only [Matrix.SpecialLinearGroup.coe_mul, ← Matrix.mulVec_mulVec,
    inv_mulVec_eq_inv_smul_of_mulVec_eq_smul hc hx,
    inv_mulVec_eq_inv_smul_of_mulVec_eq_smul hd hy, Matrix.mulVec_smul, hx, hy]
  rw [smul_smul, smul_smul, smul_smul, show d⁻¹ * c⁻¹ * d * c = 1 by field_simp, one_smul]

def lineStabilizer (e : Fin 2 → K) : Subgroup (Matrix.SpecialLinearGroup (Fin 2) K) where
  carrier := {x | (x : Matrix (Fin 2) (Fin 2) K) *ᵥ e = e}
  one_mem' := by
    show (1 : Matrix (Fin 2) (Fin 2) K) *ᵥ e = e
    rw [Matrix.one_mulVec]
  mul_mem' := by
    intro x y hx hy
    show ((x * y : Matrix.SpecialLinearGroup (Fin 2) K) :
      Matrix (Fin 2) (Fin 2) K) *ᵥ e = e
    rw [Matrix.SpecialLinearGroup.coe_mul, ← Matrix.mulVec_mulVec, hy, hx]
  inv_mem' := by
    intro x (hx : (x : Matrix (Fin 2) (Fin 2) K) *ᵥ e = e)
    show ((x⁻¹ : Matrix.SpecialLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) *ᵥ e = e
    simpa using inv_mulVec_eq_inv_smul_of_mulVec_eq_smul (x := x) (c := (1 : K)) one_ne_zero
      (by rwa [one_smul])

theorem mem_lineStabilizer {e : Fin 2 → K} {x : Matrix.SpecialLinearGroup (Fin 2) K} :
    x ∈ lineStabilizer e ↔ (x : Matrix (Fin 2) (Fin 2) K) *ᵥ e = e := Iff.rfl

theorem lineStabilizer_conj_mem {e : Fin 2 → K} {h : Matrix.SpecialLinearGroup (Fin 2) K}
    {c : K} (hc : c ≠ 0)
    (hh : (h : Matrix (Fin 2) (Fin 2) K) *ᵥ e = c • e) :
    ∀ x ∈ lineStabilizer e, h * x * h⁻¹ ∈ lineStabilizer e := by
  intro x hx
  rw [mem_lineStabilizer] at hx ⊢
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul,
    ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, inv_mulVec_eq_inv_smul_of_mulVec_eq_smul hc hh,
    Matrix.mulVec_smul, hx, Matrix.mulVec_smul, hh, smul_smul, inv_mul_cancel₀ hc, one_smul]

theorem lineStabilizer_isPGroup_two [CharP K 2] {e : Fin 2 → K} (he : e ≠ 0) :
    IsPGroup 2 (lineStabilizer e) := by
  intro x
  have hsq : (x : Matrix.SpecialLinearGroup (Fin 2) K) * x = 1 := by
    ext i j
    rw [Matrix.SpecialLinearGroup.coe_mul,
      mul_self_eq_one_of_mulVec_eq_self _ (x : Matrix.SpecialLinearGroup (Fin 2) K).2 he x.2]
    rfl
  exact ⟨1, Subtype.ext (by rw [Subgroup.coe_pow, pow_one, sq, hsq, Subgroup.coe_one])⟩

theorem card_lineStabilizer_dvd [Finite K] [CharP K 2] {e : Fin 2 → K} (he : e ≠ 0) :
    Nat.card (lineStabilizer e) ∣ Nat.card K := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  letI : Fintype K := Fintype.ofFinite K
  obtain ⟨n, hn⟩ := isPGroup_iff_card_dvd_pow.mp (lineStabilizer_isPGroup_two he)
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hn
  obtain ⟨m, -, hm⟩ := FiniteField.card K 2
  have hK : Nat.card K = 2 ^ (m : ℕ) := by rw [Nat.card_eq_fintype_card, hm]
  have hSL : Nat.card (Matrix.SpecialLinearGroup (Fin 2) K) =
      Nat.card K * (Nat.card K ^ 2 - 1) :=
    CFSG.SL2MinimalFaithful.card_specialLinearGroup_fin_two K
  have hdiv : Nat.card (lineStabilizer e) ∣ Nat.card K * (Nat.card K ^ 2 - 1) := by
    rw [← hSL]
    exact Subgroup.card_subgroup_dvd_card _
  have hodd : Odd (Nat.card K ^ 2 - 1) := by
    rw [hK]
    have hm0 : (m : ℕ) ≠ 0 := m.pos.ne'
    have hEven : Even (2 ^ (m : ℕ)) := Even.pow_of_ne_zero even_two hm0
    have h1 : 1 ≤ 2 ^ (m : ℕ) := Nat.one_le_two_pow
    exact Nat.Even.sub_odd (one_le_pow₀ h1)
      (Even.pow_of_ne_zero hEven (n := 2) (by norm_num)) odd_one
  rw [hj] at hdiv ⊢
  exact (Nat.coprime_two_left.mpr hodd).pow_left j |>.dvd_of_dvd_mul_right hdiv

theorem lineStabilizer_eq_of_le [Finite K] [CharP K 2] {e : Fin 2 → K}
    {P : Subgroup (Matrix.SpecialLinearGroup (Fin 2) K)}
    (hP : P ≤ lineStabilizer e) (he : e ≠ 0) (hcard : Nat.card K ≤ Nat.card P) :
    P = lineStabilizer e := by
  refine Subgroup.eq_of_le_of_card_ge hP ?_
  exact (Nat.le_of_dvd (Nat.card_pos) (card_lineStabilizer_dvd he)).trans hcard

theorem exists_eq_smul_of_forall_mulVec_eq_self {e v : Fin 2 → K}
    {P : Subgroup (Matrix.SpecialLinearGroup (Fin 2) K)}
    (hP : P ≤ lineStabilizer e) (hP1 : P ≠ ⊥) (he : e ≠ 0)
    (hv : ∀ x ∈ P, (x : Matrix (Fin 2) (Fin 2) K) *ᵥ v = v) :
    ∃ c : K, v = c • e := by
  obtain ⟨x, hx1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hP1
  exact exists_eq_smul_of_mulVec_eq_self (x : Matrix.SpecialLinearGroup (Fin 2) K)
    (fun h => hx1 (Subtype.ext h)) he (mem_lineStabilizer.mp (hP x.2)) (hv x x.2)

theorem exists_mulVec_eq_smul_of_normalizes {e : Fin 2 → K}
    {P : Subgroup (Matrix.SpecialLinearGroup (Fin 2) K)}
    (hP : P ≤ lineStabilizer e) (hP1 : P ≠ ⊥) (he : e ≠ 0)
    {h : Matrix.SpecialLinearGroup (Fin 2) K}
    (hh : ∀ x ∈ P, h⁻¹ * x * h ∈ P) :
    ∃ c : K, (h : Matrix (Fin 2) (Fin 2) K) *ᵥ e = c • e := by
  obtain ⟨x, hx1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hP1
  have hxe : (x : Matrix (Fin 2) (Fin 2) K) *ᵥ e = e :=
    mem_lineStabilizer.mp (hP x.2)
  have hxh : h⁻¹ * (x : Matrix.SpecialLinearGroup (Fin 2) K) * h ∈ P := hh x x.2
  have hxhL : h⁻¹ * (x : Matrix.SpecialLinearGroup (Fin 2) K) * h ∈
      lineStabilizer e := by
    apply hP
    exact hxh
  have hfix : (x : Matrix (Fin 2) (Fin 2) K) *ᵥ
      ((h : Matrix (Fin 2) (Fin 2) K) *ᵥ e) = (h : Matrix (Fin 2) (Fin 2) K) *ᵥ e := by
    calc (x : Matrix (Fin 2) (Fin 2) K) *ᵥ ((h : Matrix (Fin 2) (Fin 2) K) *ᵥ e)
        = ((x * h : Matrix.SpecialLinearGroup (Fin 2) K) :
            Matrix (Fin 2) (Fin 2) K) *ᵥ e := by
          rw [Matrix.mulVec_mulVec, Matrix.SpecialLinearGroup.coe_mul]
      _ = ((h * (h⁻¹ * x * h) : Matrix.SpecialLinearGroup (Fin 2) K) :
            Matrix (Fin 2) (Fin 2) K) *ᵥ e := by
          rw [show x * h = h * (h⁻¹ * x * h) by group]
      _ = (h : Matrix (Fin 2) (Fin 2) K) *ᵥ
            (((h⁻¹ * x * h : Matrix.SpecialLinearGroup (Fin 2) K) :
              Matrix (Fin 2) (Fin 2) K) *ᵥ e) := by
          rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.mulVec_mulVec]
      _ = (h : Matrix (Fin 2) (Fin 2) K) *ᵥ e := by
          rw [mem_lineStabilizer.mp hxhL]
  exact exists_eq_smul_of_mulVec_eq_self (x : Matrix.SpecialLinearGroup (Fin 2) K)
    (fun hx => hx1 (Subtype.ext hx)) he hxe hfix

theorem zpow_mulVec_eq_zpow_smul_of_mulVec_eq_smul {x : Matrix.SpecialLinearGroup (Fin 2) K}
    {e : Fin 2 → K} {c : K} (hc : c ≠ 0)
    (h : (x : Matrix (Fin 2) (Fin 2) K) *ᵥ e = c • e) (m : ℤ) :
    ((x ^ m : Matrix.SpecialLinearGroup (Fin 2) K) :
      Matrix (Fin 2) (Fin 2) K) *ᵥ e = c ^ m • e := by
  obtain ⟨n, rfl | rfl⟩ := Int.eq_nat_or_neg m
  · rw [zpow_natCast, Matrix.SpecialLinearGroup.coe_pow,
      CFSG.LinearGroups.pow_mulVec_eq_of_mulVec_eq h n, zpow_natCast]
  · rw [zpow_neg x (n : ℤ), zpow_neg c (n : ℤ)]
    have hxinv : ((x⁻¹ : Matrix.SpecialLinearGroup (Fin 2) K) :
        Matrix (Fin 2) (Fin 2) K) *ᵥ e = c⁻¹ • e :=
      inv_mulVec_eq_inv_smul_of_mulVec_eq_smul hc h
    have hpow := CFSG.LinearGroups.pow_mulVec_eq_of_mulVec_eq hxinv n
    simpa [Matrix.SpecialLinearGroup.coe_pow, Matrix.SpecialLinearGroup.coe_inv, inv_pow]
      using hpow

theorem mem_normalizer_lineStabilizer_of_mulVec_eq_smul {e : Fin 2 → K}
    {h : Matrix.SpecialLinearGroup (Fin 2) K} {c : K} (hc : c ≠ 0)
    (hh : (h : Matrix (Fin 2) (Fin 2) K) *ᵥ e = c • e) :
    h ∈ Subgroup.normalizer (lineStabilizer e : Set (Matrix.SpecialLinearGroup (Fin 2) K)) := by
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · intro hx
    exact lineStabilizer_conj_mem hc hh x hx
  · intro hx
    have hc' : c⁻¹ ≠ 0 := inv_ne_zero hc
    have hh' : ((h⁻¹ : Matrix.SpecialLinearGroup (Fin 2) K) :
        Matrix (Fin 2) (Fin 2) K) *ᵥ e = c⁻¹ • e :=
      inv_mulVec_eq_inv_smul_of_mulVec_eq_smul hc hh
    have hconj := lineStabilizer_conj_mem hc' hh' (h * x * h⁻¹) hx
    have hx' : h⁻¹ * (h * x * h⁻¹) * (h⁻¹)⁻¹ = x := by group
    simpa only [hx'] using hconj

end CFSG.LinearAlgebra

end

module

public import CFSG.LieType.Universal.Spin.RootElements
public import CFSG.ClassicalGroups.Orthogonal.Derived
import TauCeti.LinearAlgebra.CliffordAlgebra.Grading

public section

namespace CFSG.LieType.Universal.Spin

open CliffordAlgebra QuadraticMap CFSG.ClassicalGroups.Orthogonal

variable {K : Type*} [Field K] {V : Type*} [AddCommGroup V] [Module K V] {Q : QuadraticForm K V}

theorem exists_list_of_mem_lipschitzGroup {x : (CliffordAlgebra Q)ˣ}
    (hx : x ∈ lipschitzGroup Q) :
    ∃ l : List V, (∀ a ∈ l, Q a ≠ 0) ∧ (x : CliffordAlgebra Q) = (l.map (ι Q)).prod := by
  unfold lipschitzGroup at hx
  induction hx using Subgroup.closure_induction'' with
  | mem x hx =>
    obtain ⟨m, hm⟩ := hx
    refine ⟨[m], ?_, by simp [hm]⟩
    simp only [List.mem_singleton, forall_eq]
    exact (isUnit_of_isUnit_ι' Q (hm ▸ x.isUnit)).ne_zero
  | inv_mem x hx =>
    obtain ⟨m, hm⟩ := hx
    have hQm : Q m ≠ 0 := (isUnit_of_isUnit_ι' Q (hm ▸ x.isUnit)).ne_zero
    refine ⟨[(Q m)⁻¹ • m], ?_, ?_⟩
    · simp only [List.mem_singleton, forall_eq]
      rw [QuadraticMap.map_smul, smul_eq_mul]
      exact mul_ne_zero (mul_ne_zero (inv_ne_zero hQm) (inv_ne_zero hQm)) hQm
    · rw [List.map_singleton, List.prod_singleton]
      refine Units.inv_eq_of_mul_eq_one_left ?_
      rw [← hm, map_smul, smul_mul_assoc, ι_sq_scalar, Algebra.smul_def, ← map_mul,
        inv_mul_cancel₀ hQm, map_one]
  | one => exact ⟨[], by simp, by simp⟩
  | mul x y _ _ hx hy =>
    obtain ⟨l₁, hl₁, hx⟩ := hx
    obtain ⟨l₂, hl₂, hy⟩ := hy
    refine ⟨l₁ ++ l₂, fun a ha => ?_, by
      rw [Units.val_mul, hx, hy, List.map_append, List.prod_append]⟩
    rcases List.mem_append.mp ha with ha | ha
    exacts [hl₁ a ha, hl₂ a ha]

theorem star_prod_map_ι_mul_prod_map_ι (l : List V) :
    star (l.map (ι Q)).prod * (l.map (ι Q)).prod =
      algebraMap K (CliffordAlgebra Q) ((-1) ^ l.length * (l.map Q).prod) := by
  induction l with
  | nil => simp
  | cons a l ih =>
    rw [List.map_cons, List.prod_cons, star_mul, star_ι, List.length_cons, List.map_cons,
      List.prod_cons]
    calc star (l.map (ι Q)).prod * -ι Q a * (ι Q a * (l.map (ι Q)).prod)
        = -(algebraMap K (CliffordAlgebra Q) (Q a) *
            (star (l.map (ι Q)).prod * (l.map (ι Q)).prod)) := by
          rw [mul_neg, neg_mul, mul_assoc, ← mul_assoc (ι Q a), ι_sq_scalar, ← mul_assoc,
            ← Algebra.commutes, mul_assoc]
      _ = algebraMap K (CliffordAlgebra Q) ((-1) ^ (l.length + 1) * (Q a * (l.map Q).prod)) := by
          rw [ih, ← map_mul, ← map_neg]
          congr 1
          ring

theorem ι_mul_ι_eq_ι_neg_reflect_mul {a : V} (ha : Q a ≠ 0) (y : V) :
    ι Q a * ι Q y = ι Q (-(reflect Q a y)) * ι Q a := by
  rw [ι_mul_ι_comm a y, reflect_apply ha, neg_sub, map_sub, map_smul, sub_mul, smul_mul_assoc,
    ι_sq_scalar, Algebra.smul_def, ← (algebraMap K (CliffordAlgebra Q)).map_mul,
    div_mul_cancel₀ _ ha]

theorem prod_map_ι_mul_ι {l : List V} (hl : ∀ a ∈ l, Q a ≠ 0) (v : V) :
    (l.map (ι Q)).prod * ι Q v =
      ι Q ((-1 : K) ^ l.length • (l.map (reflect Q)).prod v) * (l.map (ι Q)).prod := by
  induction l with
  | nil => simp
  | cons a l ih =>
    have ha : Q a ≠ 0 := hl a List.mem_cons_self
    have ih' := ih fun b hb => hl b (List.mem_cons_of_mem a hb)
    rw [List.map_cons, List.prod_cons, mul_assoc, ih', ← mul_assoc,
      ι_mul_ι_eq_ι_neg_reflect_mul ha, mul_assoc, List.map_cons, List.prod_cons,
      LinearEquiv.mul_apply, map_smul, List.length_cons, pow_succ, mul_neg_one, neg_smul]

theorem exists_list_of_mem_spinGroup (x : spinGroup Q) :
    ∃ l : List V, (∀ a ∈ l, Q a ≠ 0) ∧ (x : CliffordAlgebra Q) = (l.map (ι Q)).prod :=
  exists_list_of_mem_lipschitzGroup
    (spinGroup.units_mem_lipschitzGroup (x := spinGroup.toUnits x) x.2)

theorem even_length_of_coe_eq_prod (x : spinGroup Q) {l : List V}
    (hx : (x : CliffordAlgebra Q) = (l.map (ι Q)).prod) : Even l.length := by
  by_contra hodd
  rw [Nat.not_even_iff_odd] at hodd
  have h1 : (x : CliffordAlgebra Q) ∈ evenOdd Q 1 :=
    hx ▸ prod_map_ι_mem_evenOdd_one_of_odd_length hodd
  have h0 : (x : CliffordAlgebra Q) ∈ evenOdd Q 0 := by
    rw [← even_toSubmodule]
    exact (Subalgebra.mem_toSubmodule _).mpr (spinGroup.mem_even x.2)
  have hzero : (x : CliffordAlgebra Q) = 0 :=
    (Submodule.disjoint_def.mp (evenOdd_isCompl Q).disjoint) _ h0 h1
  have h10 : (1 : CliffordAlgebra Q) = 0 := by
    rw [← coe_inv_mul_coe Q x, hzero, mul_zero]
  exact one_ne_zero h10

theorem exists_list_of_spinGroup (x : spinGroup Q) :
    ∃ l : List V, (∀ a ∈ l, Q a ≠ 0) ∧ Even l.length ∧ (l.map Q).prod = 1 ∧
      spinAction Q x = (l.map (reflect Q)).prod := by
  obtain ⟨l, hl, hx⟩ := exists_list_of_mem_spinGroup x
  have hev := even_length_of_coe_eq_prod x hx
  have hnorm : (l.map Q).prod = 1 := by
    have h := spinGroup.star_mul_self_of_mem x.2
    rw [hx, star_prod_map_ι_mul_prod_map_ι, hev.neg_one_pow, one_mul] at h
    exact algebraMap_injective' Q (by rw [h, map_one])
  refine ⟨l, hl, hev, hnorm, LinearEquiv.ext fun v => ?_⟩
  rw [spinAction_apply_eq_iff', hx, prod_map_ι_mul_ι hl, hev.neg_one_pow, one_smul]

end CFSG.LieType.Universal.Spin

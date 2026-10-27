module

public import CFSG.ClassicalGroups.Orthogonal.Derived
import CFSG.ClassicalGroups.Orthogonal.NormClass.ThreeReflections
import CFSG.ClassicalGroups.Orthogonal.Represents
import CFSG.LieType.Universal.SpinOmega.Reflections
public import CFSG.ClassicalGroups.Orthogonal.Hyperbolic

public section

namespace CFSG.ClassicalGroups.Orthogonal

open QuadraticMap

variable {K V : Type} [Field K] [AddCommGroup V] [Module K V] {Q : QuadraticForm K V}

theorem polarNondegOn_span_pair_of_sq_ne {a b : V}
    (hab : polar Q a b ^ 2 ≠ 4 * Q a * Q b) :
    PolarNondegOn Q (Submodule.span K ({a, b} : Set V)) := by
  intro x hx hxorth
  obtain ⟨s, t, rfl⟩ := Submodule.mem_span_pair.mp hx
  have ha : a ∈ Submodule.span K ({a, b} : Set V) := Submodule.subset_span (by simp)
  have hb : b ∈ Submodule.span K ({a, b} : Set V) := Submodule.subset_span (by simp)
  have hxa := hxorth a ha
  have hxb := hxorth b hb
  rw [polar_add_left, polar_smul_left_eq, polar_smul_left_eq, polar_self_eq_two_mul,
    polar_comm] at hxa
  rw [polar_add_left, polar_smul_left_eq, polar_smul_left_eq, polar_self_eq_two_mul] at hxb
  have hs : s = 0 := by
    have h : s * (4 * Q a * Q b - polar Q a b ^ 2) = 0 := by
      linear_combination (2 * Q b) * hxa - polar Q a b * hxb
    exact (mul_eq_zero.mp h).resolve_right (sub_ne_zero.mpr (Ne.symm hab))
  have ht : t = 0 := by
    by_contra ht
    have hB : polar Q a b = 0 := by
      rw [hs, zero_mul, zero_add] at hxa
      exact (mul_eq_zero.mp hxa).resolve_left ht
    have hQb : 2 * Q b = 0 := by
      rw [hs, zero_mul, zero_add] at hxb
      exact (mul_eq_zero.mp hxb).resolve_left ht
    apply hab
    rw [hB]
    linear_combination -(2 * Q a) * hQb
  simp [hs, ht]

theorem finrank_span_pair_of_sq_ne {a b : V}
    (hab : polar Q a b ^ 2 ≠ 4 * Q a * Q b) :
    Module.finrank K (Submodule.span K ({a, b} : Set V)) = 2 := by
  have ha0 : a ≠ 0 := by
    rintro rfl
    exact hab (by simp)
  have hbspan : ∀ c : K, c • a ≠ b := by
    intro c hc
    apply hab
    rw [show b = c • a from hc.symm, map_smul_eq_sq, polar_smul_right_eq,
      polar_self_eq_two_mul]
    ring
  have hlin : LinearIndependent K ![a, b] := (LinearIndependent.pair_iff' ha0).mpr hbspan
  have hrange : Set.range (![a, b] : Fin 2 → V) = ({a, b} : Set V) := by
    ext z
    constructor
    · rintro ⟨i, rfl⟩
      fin_cases i <;> simp
    · rintro (rfl | rfl)
      · exact ⟨0, by simp⟩
      · exact ⟨1, by simp⟩
  have h := finrank_span_eq_card hlin
  rw [hrange] at h
  simpa using h

theorem exists_map_smul_add_smul_eq [Finite K] [FiniteDimensional K V] (h2 : (2 : K) ≠ 0)
    {a b : V} (hab : polar Q a b ^ 2 ≠ 4 * Q a * Q b) (c : K) :
    ∃ s t : K, Q (s • a + t • b) = c := by
  obtain ⟨x, hxP, hxQ⟩ := (polarNondegOn_span_pair_of_sq_ne hab).exists_map_eq h2
    (finrank_span_pair_of_sq_ne hab).ge c
  obtain ⟨s, t, hst⟩ := Submodule.mem_span_pair.mp hxP
  exact ⟨s, t, by rw [hst, hxQ]⟩

private theorem reflect_mul_reflect_eq_sq_of_map_sub_ne_zero {a b : V} (hab : Q a = Q b)
    (hsub : Q (a - b) ≠ 0) :
    reflect Q a * reflect Q b =
      (reflect Q a * reflect Q (a - b)) * (reflect Q a * reflect Q (a - b)) := by
  have hqsub : Q (a - b) = Q a + Q b - polar Q a b := by
    rw [sub_eq_add_neg, QuadraticMap.map_add Q, QuadraticMap.map_neg, polar_neg_right]
    ring
  have hpola : polar Q (a - b) a = Q (a - b) := by
    rw [polar_sub_left, polar_self_eq_two_mul, polar_comm, hqsub, hab]
    ring
  have hconjw : reflect Q (a - b) * reflect Q a * reflect Q (a - b) = reflect Q b := by
    have h := reflect_conj (reflect_mem_orthogonalGroup Q (a - b)) a
    rw [show reflect Q (a - b) a = b by
      rw [reflect_apply hsub a, hpola, div_self hsub, one_smul, sub_sub_cancel]] at h
    rwa [reflect_inv] at h
  rw [← hconjw]
  group

private theorem reflect_mul_reflect_sq_eq_of_three_reflections {x a w y : V}
    (h : reflect Q x * reflect Q a * reflect Q w = reflect Q y) :
    (reflect Q a * reflect Q w) * (reflect Q a * reflect Q w) =
      reflect Q x * reflect Q (reflect Q y x) := by
  have hh : reflect Q a * reflect Q w = reflect Q x * reflect Q y := by
    rw [← h, ← mul_assoc, ← mul_assoc, reflect_mul_self, one_mul]
  rw [hh]
  have hconj : reflect Q y * reflect Q x * reflect Q y = reflect Q (reflect Q y x) := by
    have h' := reflect_conj (reflect_mem_orthogonalGroup Q y) x
    rwa [reflect_inv] at h'
  rw [show (reflect Q x * reflect Q y) * (reflect Q x * reflect Q y) =
    reflect Q x * (reflect Q y * reflect Q x * reflect Q y) by group, hconj]

private theorem reflect_mul_reflect_mem_closure_of_smul {S : Submodule K V} {a b x : V}
    (hb : b ∈ S) (hxS : x ∈ S) (hab : Q a = Q b) {s : K} (hxa : x = s • a)
    {c : K} (hxQ : Q x = c) (hc : c ≠ 0) :
    reflect Q a * reflect Q b ∈ Subgroup.closure (reflect Q '' {y | y ∈ S ∧ Q y = c}) := by
  have hs : s ≠ 0 := by
    rintro rfl
    rw [hxa, zero_smul, QuadraticMap.map_zero Q] at hxQ
    exact hc hxQ.symm
  have hra : reflect Q a = reflect Q x := by
    rw [hxa, CFSG.LieType.Universal.Spin.reflect_smul_of_ne_zero hs a]
  have hrb : reflect Q b = reflect Q (s • b) := by
    rw [CFSG.LieType.Universal.Spin.reflect_smul_of_ne_zero hs b]
  have hsbQ : Q (s • b) = c := by
    rw [map_smul_eq_sq, ← hab, ← map_smul_eq_sq, ← hxa]
    exact hxQ
  rw [hra, hrb]
  exact Subgroup.mul_mem _
    (Subgroup.subset_closure ⟨x, ⟨hxS, hxQ⟩, rfl⟩)
    (Subgroup.subset_closure ⟨s • b, ⟨S.smul_mem _ hb, hsbQ⟩, rfl⟩)

private theorem reflect_mul_reflect_mem_closure_of_map_sub_ne_zero_of_ne_zero (h2 : (2 : K) ≠ 0)
    {S : Submodule K V} {a b x : V} (ha : a ∈ S) (hb : b ∈ S) (hxS : x ∈ S) (hab : Q a = Q b)
    (hQa : Q a ≠ 0) (hsub : Q (a - b) ≠ 0) {s t : K} (hxdef : x = s • a + t • b) (ht : t ≠ 0)
    {c : K} (hxQ : Q x = c) (hc : c ≠ 0) :
    reflect Q a * reflect Q b ∈ Subgroup.closure (reflect Q '' {y | y ∈ S ∧ Q y = c}) := by
  have hb_eq : b = t⁻¹ • x - (s / t) • a := by
    rw [hxdef, smul_add, smul_smul, smul_smul, inv_mul_cancel₀ ht, one_smul]
    rw [div_eq_mul_inv, mul_comm s t⁻¹]
    abel
  have hwcomb : a - b = (-t⁻¹) • x + ((s + t) / t) • a := by
    rw [hb_eq, sub_sub_eq_add_sub, show (s + t) / t = 1 + s / t from by
      rw [add_div, div_self ht, add_comm], neg_smul, add_smul, one_smul]
    abel
  have hxc : Q x ≠ 0 := by rw [hxQ]; exact hc
  set y : V := polar Q x a • (a - b) + polar Q (a - b) a • x - polar Q x (a - b) • a
    with hydef
  have hws : a - b ∈ S := S.sub_mem ha hb
  have hyS : y ∈ S := by
    rw [hydef]
    exact S.sub_mem (S.add_mem (S.smul_mem _ hws) (S.smul_mem _ hxS)) (S.smul_mem _ ha)
  have hQy : Q y = 4 * Q x * Q a * Q (a - b) := by
    rw [hydef]
    exact map_polar_smul_add_polar_smul_sub_polar_smul hwcomb
  have h4 : (4 : K) ≠ 0 := by
    rw [show (4 : K) = 2 * 2 by norm_num]
    exact mul_ne_zero h2 h2
  have hQy0 : Q y ≠ 0 := by
    rw [hQy]
    exact mul_ne_zero (mul_ne_zero (mul_ne_zero h4 hxc) hQa) hsub
  have hry : reflect Q x * reflect Q a * reflect Q (a - b) = reflect Q y := by
    rw [hydef]
    exact reflect_mul_reflect_mul_reflect_eq h2 hwcomb hxc hQa hsub
  rw [reflect_mul_reflect_eq_sq_of_map_sub_ne_zero hab hsub,
    reflect_mul_reflect_sq_eq_of_three_reflections hry]
  refine Subgroup.mul_mem _ (Subgroup.subset_closure ⟨x, ⟨hxS, hxQ⟩, rfl⟩) ?_
  refine Subgroup.subset_closure ⟨reflect Q y x, ⟨?_, ?_⟩, rfl⟩
  · rw [reflect_apply hQy0]
    exact S.sub_mem hxS (S.smul_mem _ hyS)
  · rw [map_of_mem (reflect_mem_orthogonalGroup Q y), hxQ]

private theorem reflect_mul_reflect_mem_closure_of_map_sub_ne_zero [Finite K]
    [FiniteDimensional K V] (h2 : (2 : K) ≠ 0) {S : Submodule K V} {a b : V} (ha : a ∈ S)
    (hb : b ∈ S) (hab : Q a = Q b) (hdisc : polar Q a b ^ 2 ≠ 4 * Q a * Q b) (hQa : Q a ≠ 0)
    (hsub : Q (a - b) ≠ 0) {c : K} (hc : c ≠ 0) :
    reflect Q a * reflect Q b ∈ Subgroup.closure (reflect Q '' {x | x ∈ S ∧ Q x = c}) := by
  obtain ⟨s, t, hst⟩ :=
    exists_map_smul_add_smul_eq (Q := Q) (a := a) (b := b) h2 hdisc c
  set x : V := s • a + t • b with hxdef
  have hxS : x ∈ S := by
    rw [hxdef]
    exact S.add_mem (S.smul_mem _ ha) (S.smul_mem _ hb)
  have hxQ : Q x = c := by
    rw [hxdef]
    exact hst
  by_cases ht : t = 0
  · refine reflect_mul_reflect_mem_closure_of_smul (s := s) hb hxS hab ?_ hxQ hc
    rw [hxdef, ht, zero_smul, add_zero]
  · exact reflect_mul_reflect_mem_closure_of_map_sub_ne_zero_of_ne_zero h2 ha hb hxS hab hQa
      hsub hxdef ht hxQ hc

theorem reflect_mul_reflect_mem_closure_of_sq_ne [Finite K] [FiniteDimensional K V]
    (h2 : (2 : K) ≠ 0) {S : Submodule K V} {a b : V} (ha : a ∈ S) (hb : b ∈ S) (hab : Q a = Q b)
    (hdisc : polar Q a b ^ 2 ≠ 4 * Q a * Q b) {c : K} (hc : c ≠ 0) :
    reflect Q a * reflect Q b ∈ Subgroup.closure (reflect Q '' {x | x ∈ S ∧ Q x = c}) := by
  have h4 : (4 : K) ≠ 0 := by
    rw [show (4 : K) = 2 * 2 by norm_num]
    exact mul_ne_zero h2 h2
  by_cases hQa : Q a = 0
  · have hQb : Q b = 0 := by rw [← hab, hQa]
    rw [reflect_of_map_eq_zero hQa, reflect_of_map_eq_zero hQb, one_mul]
    exact Subgroup.one_mem _
  · by_cases hsub : Q (a - b) = 0
    · have hqsum : Q (a + b) = 4 * Q a - Q (a - b) := by
        have h1 : Q (a + b) = Q a + Q b + polar Q a b := QuadraticMap.map_add Q a b
        have h2' : Q (a - b) = Q a + Q b - polar Q a b := by
          rw [sub_eq_add_neg, QuadraticMap.map_add Q, QuadraticMap.map_neg, polar_neg_right]
          ring
        rw [h1, h2', hab]
        ring
      have hsub' : Q (a - -b) ≠ 0 := by
        rw [sub_neg_eq_add, hqsum, hsub, sub_zero]
        exact mul_ne_zero h4 hQa
      have hab' : Q a = Q (-b) := by
        rw [QuadraticMap.map_neg]
        exact hab
      have hdisc' : polar Q a (-b) ^ 2 ≠ 4 * Q a * Q (-b) := by
        have h1 : polar Q a (-b) ^ 2 = polar Q a b ^ 2 := by
          rw [polar_neg_right]
          ring
        rw [h1, QuadraticMap.map_neg]
        exact hdisc
      have hmain := reflect_mul_reflect_mem_closure_of_map_sub_ne_zero h2 ha (S.neg_mem hb)
        hab' hdisc' hQa hsub' hc
      have hneg : reflect Q (-b) = reflect Q b := by
        rw [show (-b : V) = (-1 : K) • b from (neg_one_smul K b).symm,
          CFSG.LieType.Universal.Spin.reflect_smul_of_ne_zero
            (neg_ne_zero.mpr one_ne_zero) b]
      simpa [hneg] using hmain
    · exact reflect_mul_reflect_mem_closure_of_map_sub_ne_zero h2 ha hb hab hdisc hQa hsub hc

end CFSG.ClassicalGroups.Orthogonal

end

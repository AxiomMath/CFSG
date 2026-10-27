module

public import CFSG.ClassicalGroups.Orthogonal.Hyperbolic
import Mathlib.FieldTheory.Finite.Basic

public section

namespace CFSG.ClassicalGroups.Orthogonal

open QuadraticMap Polynomial

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] {Q : QuadraticForm K V}

theorem PolarNondegOn.exists_map_ne_zero {S : Submodule K V} (hS : PolarNondegOn Q S)
    (hS0 : S ≠ ⊥) : ∃ x ∈ S, Q x ≠ 0 := by
  by_contra hcon
  push Not at hcon
  obtain ⟨x, hxS, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hS0
  refine hx0 (hS x hxS fun y hy => ?_)
  have h1 := hcon (x + y) (S.add_mem hxS hy)
  have h2 := hcon x hxS
  have h3 := hcon y hy
  show Q (x + y) - Q x - Q y = 0
  rw [h1, h2, h3]
  ring

private theorem exists_polar_eq_zero_map_ne_zero_of_singular (h2 : (2 : K) ≠ 0)
    {S : Submodule K V} (hS : PolarNondegOn Q S) {b z : V} (hbS : b ∈ S) (hzS : z ∈ S)
    (hbb : polar Q b b ≠ 0) (hbz : polar Q b z = 0) (hz0 : z ≠ 0) (hQz : Q z = 0) :
    ∃ w ∈ S, polar Q b w = 0 ∧ Q w ≠ 0 := by
  obtain ⟨y, hyS, hy⟩ := hS.exists_polar_ne_zero hzS hz0
  set k' : K := polar Q b y / polar Q b b with hk'
  set y' : V := y - k' • b with hy'
  have hy'S : y' ∈ S := S.sub_mem hyS (S.smul_mem _ hbS)
  have hby' : polar Q b y' = 0 := by
    rw [hy', polar_sub_right, polar_smul_right_eq, hk']
    field_simp
    ring
  have hzb : polar Q z b = 0 := by rw [polar_comm, hbz]
  have hzy' : polar Q z y' ≠ 0 := by
    rw [hy', polar_sub_right, polar_smul_right_eq, hzb, mul_zero, sub_zero]
    exact hy
  by_cases hp : Q (z + y') = 0
  · refine ⟨z - y', S.sub_mem hzS hy'S, ?_, ?_⟩
    · rw [polar_sub_right, hbz, hby', sub_zero]
    · intro hm
      apply hzy'
      have e1 : Q (z + y') = Q z + Q y' + polar Q z y' := by
        rw [QuadraticMap.map_add Q z y']
      have e2 : Q (z - y') = Q z + Q y' - polar Q z y' := by
        rw [sub_eq_add_neg, QuadraticMap.map_add Q z (-y'), QuadraticMap.map_neg,
          polar_neg_right]
        ring
      rw [e1, hQz] at hp
      rw [e2, hQz] at hm
      have : (2 : K) * polar Q z y' = 0 := by linear_combination hp - hm
      exact (mul_eq_zero.mp this).resolve_left h2
  · refine ⟨z + y', S.add_mem hzS hy'S, ?_, hp⟩
    rw [polar_add_right, hbz, hby', add_zero]

theorem PolarNondegOn.exists_polar_eq_zero_map_ne_zero [FiniteDimensional K V] (h2 : (2 : K) ≠ 0)
    {S : Submodule K V} (hS : PolarNondegOn Q S) (hdim : 2 ≤ Module.finrank K S) {b : V}
    (hbS : b ∈ S) (hQb : Q b ≠ 0) : ∃ z ∈ S, polar Q b z = 0 ∧ Q z ≠ 0 := by
  have hb0 : b ≠ 0 := fun h => hQb (by rw [h]; exact QuadraticMap.map_zero Q)
  have hbb : polar Q b b ≠ 0 := by
    rw [QuadraticMap.polar_self, two_nsmul, ← two_mul]
    exact mul_ne_zero h2 hQb
  obtain ⟨c, hcS, hcb⟩ : ∃ c ∈ S, c ∉ Submodule.span K {b} := by
    by_contra hcon
    push Not at hcon
    have hle : S ≤ Submodule.span K {b} := fun c hc => hcon c hc
    have h1 := Submodule.finrank_mono hle
    rw [finrank_span_singleton hb0] at h1
    omega
  set k : K := polar Q b c / polar Q b b with hk
  set z₁ : V := c - k • b with hz₁
  have hz₁S : z₁ ∈ S := S.sub_mem hcS (S.smul_mem _ hbS)
  have hbz₁ : polar Q b z₁ = 0 := by
    rw [hz₁, polar_sub_right, polar_smul_right_eq, hk]
    field_simp
    ring
  have hz₁0 : z₁ ≠ 0 := by
    intro h
    apply hcb
    have : c = k • b := by rw [hz₁] at h; exact sub_eq_zero.mp h
    rw [this]
    exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self b)
  by_cases hQz₁ : Q z₁ = 0
  · exact exists_polar_eq_zero_map_ne_zero_of_singular h2 hS hbS hz₁S hbb hbz₁ hz₁0 hQz₁
  · exact ⟨z₁, hz₁S, hbz₁, hQz₁⟩

theorem PolarNondegOn.exists_map_eq [Finite K] [FiniteDimensional K V] (h2 : (2 : K) ≠ 0)
    {S : Submodule K V} (hS : PolarNondegOn Q S) (hdim : 2 ≤ Module.finrank K S) (c : K) :
    ∃ x ∈ S, Q x = c := by
  classical
  let : Fintype K := Fintype.ofFinite K
  have hchar : ringChar K ≠ 2 := by
    intro h
    exact h2 ((ringChar.spec K 2).mpr (h ▸ dvd_rfl))
  have hcard : Fintype.card K % 2 = 1 := FiniteField.odd_card_of_char_ne_two hchar
  have hS0 : S ≠ ⊥ := fun h => by
    rw [h, finrank_bot] at hdim
    omega
  obtain ⟨b, hbS, hQb⟩ := hS.exists_map_ne_zero hS0
  obtain ⟨b', hb'S, hbb', hQb'⟩ := hS.exists_polar_eq_zero_map_ne_zero h2 hdim hbS hQb
  have hf : degree (C (Q b) * X ^ 2 : K[X]) = 2 := degree_C_mul_X_pow 2 hQb
  have hg : degree (C (Q b') * X ^ 2 - C c : K[X]) = 2 := by
    have h : degree (C c : K[X]) < degree (C (Q b') * X ^ 2 : K[X]) := by
      rw [degree_C_mul_X_pow 2 hQb']
      exact lt_of_le_of_lt degree_C_le (by norm_num)
    rw [degree_sub_eq_left_of_degree_lt h, degree_C_mul_X_pow 2 hQb']
    norm_num
  obtain ⟨s, r, hsr⟩ := FiniteField.exists_root_sum_quadratic hf hg hcard
  have hsr' : Q b * (s * s) + Q b' * (r * r) = c := by
    simp only [eval_mul, eval_C, eval_pow, eval_X, eval_sub] at hsr
    linear_combination hsr
  refine ⟨s • b + r • b', S.add_mem (S.smul_mem _ hbS) (S.smul_mem _ hb'S), ?_⟩
  rw [QuadraticMap.map_add Q, map_smul_eq_sq, map_smul_eq_sq, polar_smul_left_eq,
    polar_smul_right_eq, hbb', ← hsr']
  ring

end CFSG.ClassicalGroups.Orthogonal

end

module

public import CFSG.ClassicalGroups.Orthogonal.Eichler
public import Mathlib.Tactic.Positivity.Finset

public section

namespace CFSG.ClassicalInvolution.Q3.TL4

open QuadraticMap CFSG.ClassicalGroups.Orthogonal

variable {K : Type*} [Field K] {V : Type*} [AddCommGroup V] [Module K V] {Q : QuadraticForm K V}

structure Trip (Q : QuadraticForm K V) where
  p : V
  q : V
  a : V
  Qp : Q p = 0
  Qq : Q q = 0
  pq : polar Q p q = 1
  pa : polar Q p a = 0
  qa : polar Q q a = 0
  Qa : Q a ≠ 0

namespace Trip

variable (T : Trip Q)

@[expose] def span : Submodule K V := Submodule.span K {T.p, T.q, T.a}

@[expose] def eich : Set (V ≃ₗ[K] V) :=
  {E | ∃ v w, v ∈ T.span ∧ w ∈ T.span ∧ Q v = 0 ∧ polar Q v w = 0 ∧ eichler Q v w = E}

theorem p_mem : T.p ∈ T.span := Submodule.subset_span (by simp)

theorem q_mem : T.q ∈ T.span := Submodule.subset_span (by simp)

theorem a_mem : T.a ∈ T.span := Submodule.subset_span (by simp)

theorem p_ne_zero : T.p ≠ 0 := by
  intro h
  have := T.pq
  rw [h, polar_zero_left] at this
  exact zero_ne_one this

theorem mem_span_iff {w : V} : w ∈ T.span ↔ ∃ α β γ : K, w = α • T.p + β • T.q + γ • T.a := by
  constructor
  · intro hw
    obtain ⟨α, z, hz, rfl⟩ := Submodule.mem_span_insert.mp hw
    obtain ⟨β, γ, rfl⟩ := Submodule.mem_span_pair.mp hz
    exact ⟨α, β, γ, by abel⟩
  · rintro ⟨α, β, γ, rfl⟩
    exact add_mem (add_mem (Submodule.smul_mem _ _ T.p_mem) (Submodule.smul_mem _ _ T.q_mem))
      (Submodule.smul_mem _ _ T.a_mem)

theorem pp : polar Q T.p T.p = 0 := polar_self_eq_zero T.Qp

theorem qq : polar Q T.q T.q = 0 := polar_self_eq_zero T.Qq

theorem qp : polar Q T.q T.p = 1 := by rw [polar_comm]; exact T.pq

theorem ap : polar Q T.a T.p = 0 := by rw [polar_comm]; exact T.pa

theorem aq : polar Q T.a T.q = 0 := by rw [polar_comm]; exact T.qa

theorem aa : polar Q T.a T.a = 2 * Q T.a := by
  rw [polar_self, two_smul, two_mul]

theorem polar_eq_zero_of_perp {x : V} (hp : polar Q x T.p = 0) (hq : polar Q x T.q = 0)
    (ha : polar Q x T.a = 0) {w : V} (hw : w ∈ T.span) : polar Q x w = 0 := by
  obtain ⟨α, β, γ, rfl⟩ := T.mem_span_iff.mp hw
  rw [polar_add_right, polar_add_right, polar_smul_right_eq, polar_smul_right_eq,
    polar_smul_right_eq, hp, hq, ha]
  ring

theorem Q_comb (α β γ : K) : Q (α • T.p + β • T.q + γ • T.a) = α * β + γ ^ 2 * Q T.a := by
  rw [QuadraticMap.map_add Q, QuadraticMap.map_add Q, map_smul_eq_sq, map_smul_eq_sq,
    map_smul_eq_sq, polar_add_left]
  simp only [polar_smul_left_eq, polar_smul_right_eq, T.Qp, T.Qq, T.pq, T.pa, T.qa]
  ring

theorem polar_comb (α β γ α' β' γ' : K) :
    polar Q (α • T.p + β • T.q + γ • T.a) (α' • T.p + β' • T.q + γ' • T.a) =
      α * β' + β * α' + 2 * γ * γ' * Q T.a := by
  simp only [polar_add_left, polar_add_right, polar_smul_left_eq, polar_smul_right_eq,
    T.pp, T.qq, T.pq, T.qp, T.pa, T.ap, T.qa, T.aq, T.aa]
  ring

theorem exists_sing_aniso (h2 : (2 : K) ≠ 0) {w : V} (hw : w ∈ T.span) (hw0 : w ≠ 0) :
    ∃ v ∈ T.span, ∃ a' ∈ T.span, Q v = 0 ∧ polar Q v a' = 0 ∧ Q a' ≠ 0 ∧ polar Q w v ≠ 0 := by
  obtain ⟨α, β, γ, rfl⟩ := T.mem_span_iff.mp hw
  have e1 : polar Q (α • T.p + β • T.q + γ • T.a) T.p = β := by
    simp only [polar_add_left, polar_smul_left_eq, T.pp, T.qp, T.ap]
    ring
  have e2 : polar Q (α • T.p + β • T.q + γ • T.a) T.q = α := by
    simp only [polar_add_left, polar_smul_left_eq, T.pq, T.qq, T.aq]
    ring
  by_cases hβ : β = 0
  · by_cases hα : α = 0
    · have hγ : γ ≠ 0 := by
        rintro rfl
        apply hw0
        rw [hα, hβ]
        simp
      set c := Q T.a with hc
      refine ⟨(1 : K) • T.p + (-c) • T.q + (1 : K) • T.a, T.mem_span_iff.mpr ⟨_, _, _, rfl⟩,
        (1 : K) • T.p + c • T.q + (0 : K) • T.a, T.mem_span_iff.mpr ⟨_, _, _, rfl⟩, ?_, ?_, ?_, ?_⟩
      · rw [T.Q_comb]
        ring
      · rw [T.polar_comb]
        ring
      · rw [T.Q_comb]
        simpa using T.Qa
      · rw [T.polar_comb, hα, hβ]
        have : (0 : K) * -c + 0 * 1 + 2 * γ * 1 * Q T.a = 2 * γ * Q T.a := by ring
        rw [this]
        exact mul_ne_zero (mul_ne_zero h2 hγ) T.Qa
    · exact ⟨T.q, T.q_mem, T.a, T.a_mem, T.Qq, T.qa, T.Qa, by rw [e2]; exact hα⟩
  · exact ⟨T.p, T.p_mem, T.a, T.a_mem, T.Qp, T.pa, T.Qa, by rw [e1]; exact hβ⟩

end Trip

end CFSG.ClassicalInvolution.Q3.TL4

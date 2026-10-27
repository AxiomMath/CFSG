module

public import Mathlib.GroupTheory.Nilpotent

public section

namespace CFSG.EvenSporadicStandard.TwoHS

open Subgroup

variable {X : Type*} [Group X]

theorem comm_of_conj_eq {n a : X} (h : n * a * n⁻¹ = a) : n * a = a * n := by
  calc n * a = (n * a * n⁻¹) * n := by group
    _ = a * n := by rw [h]

theorem mem_Q_or_of_normalizes (Q : Subgroup X) {τ v x n : X}
    (hQ : ∀ y : X, (y * τ = τ * y ∧ y * v = v * y) ↔ y ∈ Q) (hτvc : τ * v = v * τ)
    (hxτ : x * τ * x⁻¹ = v) (hxv : x * v * x⁻¹ = τ)
    (hτ1 : τ ≠ 1) (hτv : τ ≠ v) (hv1 : v ≠ 1)
    (hnc : ¬ ∃ g : X, τ * v = g * τ * g⁻¹)
    (hτ' : n * τ * n⁻¹ = 1 ∨ n * τ * n⁻¹ = τ ∨ n * τ * n⁻¹ = v ∨ n * τ * n⁻¹ = τ * v)
    (hv' : n * v * n⁻¹ = 1 ∨ n * v * n⁻¹ = τ ∨ n * v * n⁻¹ = v ∨ n * v * n⁻¹ = τ * v) :
    n ∈ Q ∨ x⁻¹ * n ∈ Q := by
  have hne1 : ∀ {a : X} (m : X), a ≠ 1 → m * a * m⁻¹ ≠ 1 := by
    intro a m ha h
    apply ha
    calc a = m⁻¹ * (m * a * m⁻¹) * m := by group
      _ = 1 := by rw [h]; group
  have hneq : n * τ * n⁻¹ ≠ n * v * n⁻¹ := by
    intro h
    apply hτv
    calc τ = n⁻¹ * (n * τ * n⁻¹) * n := by group
      _ = n⁻¹ * (n * v * n⁻¹) * n := by rw [h]
      _ = v := by group
  have hxτ' : τ = x⁻¹ * v * x := by rw [← hxτ]; group
  have hxv' : v = x⁻¹ * τ * x := by rw [← hxv]; group
  rcases hτ' with h1 | h1 | h1 | h1
  · exact absurd h1 (hne1 n hτ1)
  · rcases hv' with h2 | h2 | h2 | h2
    · exact absurd h2 (hne1 n hv1)
    · exact absurd (h1.trans h2.symm) hneq
    · exact Or.inl ((hQ n).1 ⟨comm_of_conj_eq h1, comm_of_conj_eq h2⟩)
    · exfalso
      apply hnc
      refine ⟨n * x, ?_⟩
      calc τ * v = n * v * n⁻¹ := h2.symm
        _ = n * (x * τ * x⁻¹) * n⁻¹ := by rw [hxτ]
        _ = n * x * τ * (n * x)⁻¹ := by group
  · rcases hv' with h2 | h2 | h2 | h2
    · exact absurd h2 (hne1 n hv1)
    · right
      refine (hQ _).1 ⟨?_, ?_⟩
      · apply comm_of_conj_eq
        calc x⁻¹ * n * τ * (x⁻¹ * n)⁻¹ = x⁻¹ * (n * τ * n⁻¹) * x := by group
          _ = τ := by rw [h1, ← hxτ']
      · apply comm_of_conj_eq
        calc x⁻¹ * n * v * (x⁻¹ * n)⁻¹ = x⁻¹ * (n * v * n⁻¹) * x := by group
          _ = v := by rw [h2, ← hxv']
    · exact absurd (h1.trans h2.symm) hneq
    · exfalso
      apply hnc
      refine ⟨x⁻¹ * n * x, ?_⟩
      have h3 : x⁻¹ * (n * v * n⁻¹) * x = τ * v := by
        rw [h2]
        calc x⁻¹ * (τ * v) * x = (x⁻¹ * τ * x) * (x⁻¹ * v * x) := by group
          _ = v * τ := by rw [← hxv', ← hxτ']
          _ = τ * v := hτvc.symm
      calc τ * v = x⁻¹ * (n * v * n⁻¹) * x := h3.symm
        _ = x⁻¹ * (n * (x * τ * x⁻¹) * n⁻¹) * x := by rw [hxτ]
        _ = (x⁻¹ * n * x) * τ * (x⁻¹ * n * x)⁻¹ := by group
  · exfalso
    apply hnc
    exact ⟨n, h1.symm⟩

variable [Finite X]

theorem le_of_isPGroup (P Q : Subgroup X) (hQP : Q ≤ P) {τ v x : X}
    (hQ : ∀ y : X, (y * τ = τ * y ∧ y * v = v * y) ↔ y ∈ Q) (hτvc : τ * v = v * τ)
    (hxP : x ∈ P) (hxτ : x * τ * x⁻¹ = v) (hxv : x * v * x⁻¹ = τ)
    (hτ1 : τ ≠ 1) (hτv : τ ≠ v) (hv1 : v ≠ 1)
    (hnc : ¬ ∃ g : X, τ * v = g * τ * g⁻¹)
    (hV : ∀ z ∈ P, (∃ a ∈ P, ∀ p ∈ P, p * z * p⁻¹ = z ∨ p * z * p⁻¹ = a) ↔
        (z = 1 ∨ z = τ ∨ z = v ∨ z = τ * v))
    (R : Subgroup X) (hR : IsPGroup 2 R) (hPR : P ≤ R) : R ≤ P := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  by_contra hRP
  obtain ⟨g, hgR, hgP⟩ := IsConcreteLE.not_le_iff_exists.1 hRP
  have hnil : Group.IsNilpotent ↥R := hR.isNilpotent
  have hnc' := Group.normalizerCondition_of_isNilpotent (G := ↥R)
  set P' : Subgroup ↥R := P.subgroupOf R with hP'
  have hlt : P' < ⊤ := by
    rw [lt_top_iff_ne_top]
    intro h
    apply hgP
    have : (⟨g, hgR⟩ : ↥R) ∈ P' := by rw [h]; exact Subgroup.mem_top _
    exact this
  obtain ⟨n', hn'N, hn'P⟩ := (IsConcreteLE.lt_iff_le_and_exists.1 (hnc' P' hlt)).2
  set n : X := n'.1 with hn
  have hnorm : ∀ p ∈ P, n * p * n⁻¹ ∈ P ∧ n⁻¹ * p * n ∈ P := by
    intro p hp
    have hpR : p ∈ R := hPR hp
    have key := mem_normalizer_iff.1 hn'N
    constructor
    · have := (key ⟨p, hpR⟩).1 (by exact hp)
      exact this
    · have hq : n⁻¹ * p * n ∈ R := R.mul_mem (R.mul_mem (R.inv_mem n'.2) hpR) n'.2
      have := (key ⟨n⁻¹ * p * n, hq⟩).2
      have h2 : (n' * ⟨n⁻¹ * p * n, hq⟩ * n'⁻¹ : ↥R) ∈ P' := by
        show n * (n⁻¹ * p * n) * n⁻¹ ∈ P
        have : n * (n⁻¹ * p * n) * n⁻¹ = p := by group
        rw [this]; exact hp
      exact this h2
  have hτQ : τ ∈ Q := (hQ τ).1 ⟨rfl, hτvc⟩
  have hvQ : v ∈ Q := (hQ v).1 ⟨hτvc.symm, rfl⟩
  have hVP : ∀ z : X, (z = 1 ∨ z = τ ∨ z = v ∨ z = τ * v) → z ∈ P := by
    rintro z (rfl | rfl | rfl | rfl)
    · exact P.one_mem
    · exact hQP hτQ
    · exact hQP hvQ
    · exact P.mul_mem (hQP hτQ) (hQP hvQ)
  have hVmem : ∀ z : X, (z = 1 ∨ z = τ ∨ z = v ∨ z = τ * v) →
      (n * z * n⁻¹ = 1 ∨ n * z * n⁻¹ = τ ∨ n * z * n⁻¹ = v ∨ n * z * n⁻¹ = τ * v) := by
    intro z hz
    have hzP : z ∈ P := hVP z hz
    obtain ⟨a, haP, ha⟩ := (hV z hzP).2 hz
    refine (hV _ (hnorm z hzP).1).1 ⟨n * a * n⁻¹, (hnorm a haP).1, ?_⟩
    intro p hp
    have hp' : n⁻¹ * p * n ∈ P := (hnorm p hp).2
    have e : ∀ w : X, p * (n * w * n⁻¹) * p⁻¹ =
        n * ((n⁻¹ * p * n) * w * (n⁻¹ * p * n)⁻¹) * n⁻¹ := by
      intro w; group
    rcases ha _ hp' with h | h
    · left; rw [e, h]
    · right; rw [e, h]
  have hnP : n ∈ P := by
    rcases mem_Q_or_of_normalizes Q hQ hτvc hxτ hxv hτ1 hτv hv1 hnc
      (hVmem τ (Or.inr (Or.inl rfl))) (hVmem v (Or.inr (Or.inr (Or.inl rfl)))) with h | h
    · exact hQP h
    · have : n = x * (x⁻¹ * n) := by group
      rw [this]
      exact P.mul_mem hxP (hQP h)
  exact hn'P hnP

end CFSG.EvenSporadicStandard.TwoHS

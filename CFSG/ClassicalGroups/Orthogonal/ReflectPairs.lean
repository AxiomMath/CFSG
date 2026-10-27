module

public import CFSG.ClassicalGroups.Orthogonal.CharTwoTransvection
public import CFSG.Quasithin.Recognition.CertDerived
public import Mathlib.GroupTheory.Nilpotent

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.ClassicalGroups.Orthogonal

open QuadraticMap Module
open scoped commutatorElement

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] {Q : QuadraticForm (ZMod 2) V}

theorem commutator_orthogonalGroup_le_closure_reflect_mul [FiniteDimensional (ZMod 2) V]
    (hQ : (polarBilin Q).Nondegenerate) (h5 : 5 ≤ finrank (ZMod 2) V) {v₀ : V} (hv₀ : Q v₀ ≠ 0) :
    ⁅TauCeti.QuadraticMap.orthogonalGroup Q, TauCeti.QuadraticMap.orthogonalGroup Q⁆ ≤
      Subgroup.closure {g | ∃ v, Q v ≠ 0 ∧ g = reflect Q v * reflect Q v₀} := by
  rw [orthogonalGroup_eq_closure_reflect hQ (by omega) (Or.inl h5)]
  have hpair : ∀ {x y : V}, Q x ≠ 0 → Q y ≠ 0 →
      reflect Q x * reflect Q y ∈
        Subgroup.closure {g | ∃ v, Q v ≠ 0 ∧ g = reflect Q v * reflect Q v₀} := by
    intro x y hx hy
    have hxT : reflect Q x * reflect Q v₀ ∈
        Subgroup.closure {g | ∃ v, Q v ≠ 0 ∧ g = reflect Q v * reflect Q v₀} :=
      Subgroup.subset_closure ⟨x, hx, rfl⟩
    have hyT : reflect Q y * reflect Q v₀ ∈
        Subgroup.closure {g | ∃ v, Q v ≠ 0 ∧ g = reflect Q v * reflect Q v₀} :=
      Subgroup.subset_closure ⟨y, hy, rfl⟩
    have e : reflect Q x * reflect Q y =
        (reflect Q x * reflect Q v₀) * (reflect Q y * reflect Q v₀)⁻¹ := by
      rw [mul_inv_rev, reflect_inv, reflect_inv]
      calc
        reflect Q x * reflect Q y
            = reflect Q x * (reflect Q v₀ * reflect Q v₀) * reflect Q y := by
              rw [reflect_mul_self, mul_one]
        _ = (reflect Q x * reflect Q v₀) * (reflect Q v₀ * reflect Q y) := by group
    rw [e]
    exact Subgroup.mul_mem _ hxT (Subgroup.inv_mem _ hyT)
  refine CFSG.Quasithin.commutator_closure_le_of_involutions
    (S := Set.range (reflect Q))
    (T := {g | ∃ v, Q v ≠ 0 ∧ g = reflect Q v * reflect Q v₀}) ?_ ?_ ?_
  · rintro s ⟨v, rfl⟩
    exact reflect_mul_self Q v
  · rintro s ⟨a, rfl⟩ t ⟨v, hv, rfl⟩
    have hsO := reflect_mem_orthogonalGroup Q a
    have hsv : Q (reflect Q a v) ≠ 0 := by rwa [map_of_mem hsO]
    have hsv₀ : Q (reflect Q a v₀) ≠ 0 := by rwa [map_of_mem hsO]
    have e : reflect Q a * (reflect Q v * reflect Q v₀) * (reflect Q a)⁻¹ =
        reflect Q (reflect Q a v) * reflect Q (reflect Q a v₀) := by
      rw [← reflect_conj hsO v, ← reflect_conj hsO v₀]
      group
    rw [e]
    exact hpair hsv hsv₀
  · rintro s ⟨a, rfl⟩ s' ⟨b, rfl⟩
    by_cases ha : Q a = 0
    · rw [reflect_of_map_eq_zero ha, commutatorElement_one_left]
      exact Subgroup.one_mem _
    · by_cases hb : Q b = 0
      · rw [reflect_of_map_eq_zero hb, commutatorElement_one_right]
        exact Subgroup.one_mem _
      · have hmem := hpair ha hb
        have e : ⁅reflect Q a, reflect Q b⁆ =
            (reflect Q a * reflect Q b) * (reflect Q a * reflect Q b) := by
          simp only [commutatorElement_def]
          rw [reflect_inv, reflect_inv]
          group
        rw [e]
        exact Subgroup.mul_mem _ hmem hmem

end CFSG.ClassicalGroups.Orthogonal

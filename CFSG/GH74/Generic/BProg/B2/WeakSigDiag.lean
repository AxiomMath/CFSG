module

public import CFSG.RankThree.PartOne.CTP.SeitzToral
public import Mathlib.Algebra.Order.Ring.Star

public section

namespace CFSG.GH74.Generic.BProg.B2

open Matrix CFSG.RankThree.PartOne.CTP.SeitzToral

variable {F : Type*} [Field F] {n : ℕ}

theorem card_range_le_two_of_sq_eq_one {D : Type*} [Group D] (χ : D →* Fˣ) (hsq : ∀ x : D, x * x = 1) :
    Nat.card χ.range ≤ 2 := by
  have hle : χ.range ≤ Subgroup.zpowers (-1 : Fˣ) := by
    rintro _ ⟨x, rfl⟩
    have h1 : χ x * χ x = 1 := by rw [← map_mul, hsq x, map_one]
    have h2 : ((χ x : Fˣ) : F) * ((χ x : Fˣ) : F) = 1 := by
      have := congrArg (fun u : Fˣ => (u : F)) h1
      simpa using this
    rcases mul_self_eq_one_iff.mp h2 with h | h
    · have : χ x = 1 := Units.ext h
      rw [this]
      exact Subgroup.one_mem _
    · have : χ x = -1 := Units.ext (by simpa using h)
      rw [this]
      exact Subgroup.mem_zpowers _
  have hord : orderOf (-1 : Fˣ) ∣ 2 := orderOf_dvd_of_pow_eq_one (by simp)
  have hfin : Finite (Subgroup.zpowers (-1 : Fˣ)) :=
    Nat.finite_of_card_ne_zero (by
      rw [Nat.card_zpowers]
      exact (Nat.pos_of_dvd_of_pos hord (by norm_num)).ne')
  have hcard : Nat.card (Subgroup.zpowers (-1 : Fˣ)) ≤ 2 := by
    rw [Nat.card_zpowers]
    exact Nat.le_of_dvd (by norm_num) hord
  exact (Subgroup.card_le_of_le hle).trans hcard

theorem closure_centralizer_hyperplane_diag_eq_top (D : Subgroup (GL (Fin n) F)) [Finite D]
    (hD : ∀ x ∈ D, ∀ i j, i ≠ j → (x : Matrix (Fin n) (Fin n) F) i j = 0)
    (hsq : ∀ x ∈ D, x * x = 1) :
    Subgroup.closure {g : Matrix.SpecialLinearGroup (Fin n) F | ∃ E : Subgroup (GL (Fin n) F), E ≤ D ∧
      Nat.card D ≤ 2 * Nat.card E ∧ ∀ x ∈ E,
        (g : Matrix (Fin n) (Fin n) F) * (x : Matrix (Fin n) (Fin n) F) =
          (x : Matrix (Fin n) (Fin n) F) * g} = ⊤ := by
  rw [eq_top_iff, ← Matrix.SpecialLinearGroup.closure_range_toSpecialLinearGroup_eq_top_of_field
    (ι := Fin n) (K := F), Subgroup.closure_le]
  rintro _ ⟨t, rfl⟩
  apply Subgroup.subset_closure
  let χ : D →* Fˣ := diagRatio D hD t.i t.j
  have hχsq : ∀ x : D, x * x = 1 := fun x => Subtype.ext (hsq x.1 x.2)
  have hrange : Nat.card χ.range ≤ 2 := card_range_le_two_of_sq_eq_one χ hχsq
  refine ⟨χ.ker.map D.subtype, Subgroup.map_subtype_le _, ?_, ?_⟩
  · have h1 : Nat.card χ.ker * Nat.card χ.range = Nat.card D := by
      rw [← Subgroup.index_ker, Subgroup.card_mul_index]
    have h2 : Nat.card (χ.ker.map D.subtype) = Nat.card χ.ker :=
      Subgroup.card_map_of_injective D.subtype_injective
    rw [h2, ← h1, mul_comm]
    exact Nat.mul_le_mul_right _ hrange
  · intro x hx
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hx
    have hy1 : χ y = 1 := hy
    have hii : (y.1 : Matrix (Fin n) (Fin n) F) t.i t.i = (y.1 : Matrix (Fin n) (Fin n) F) t.j t.j := by
      have h1 : (y.1 : Matrix (Fin n) (Fin n) F) t.i t.i *
          ((y.1 : Matrix (Fin n) (Fin n) F) t.j t.j)⁻¹ = 1 := by
        have h := congrArg (fun u : Fˣ => (u : F)) hy1
        simpa [χ, diagRatio] using h
      have hj := diag_entry_ne_zero (hD y.1 y.2) t.j
      field_simp at h1
      exact h1
    exact transvection_commute_of_diag_eq (hD y.1 y.2) t.hij hii t.c

end CFSG.GH74.Generic.BProg.B2

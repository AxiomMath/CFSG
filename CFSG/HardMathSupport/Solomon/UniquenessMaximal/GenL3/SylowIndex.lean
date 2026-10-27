module

public import Mathlib.GroupTheory.Sylow

public section

namespace CFSG.HardMathSupport.Solomon.UniquenessMaximal.GenL3

open scoped Pointwise

theorem exists_conj_le_of_not_dvd_index {X : Type*} [Group X] [Finite X] {p : ℕ} (hp : p.Prime)
    (N : Subgroup X) (hidx : ¬ p ∣ N.index) (E : Subgroup X) (hE : IsPGroup p E) :
    ∃ x : X, ∀ e ∈ E, x * e * x⁻¹ ∈ N := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  haveI : Finite N := inferInstance
  obtain ⟨Q⟩ := (inferInstance : Nonempty (Sylow p N))
  set P : Subgroup X := (Q : Subgroup N).map N.subtype with hPdef
  have hPcard : Nat.card P = p ^ (Nat.card X).factorization p := by
    have h1 : Nat.card P = Nat.card (Q : Subgroup N) :=
      Subgroup.card_map_of_injective N.subtype_injective
    rw [h1, Sylow.card_eq_multiplicity]
    have h2 : Nat.card X = N.index * Nat.card N := by
      rw [mul_comm]; exact (Subgroup.card_mul_index N).symm
    have hX0 : N.index ≠ 0 := Subgroup.index_ne_zero_of_finite
    have hN0 : Nat.card N ≠ 0 := Nat.card_pos.ne'
    rw [h2, Nat.factorization_mul hX0 hN0]
    simp [Nat.factorization_eq_zero_of_not_dvd hidx]
  let S : Sylow p X := Sylow.ofCard P hPcard
  obtain ⟨R, hER⟩ := hE.exists_le_sylow
  obtain ⟨x, hx⟩ := MulAction.exists_smul_eq X S R
  refine ⟨x⁻¹, fun e he => ?_⟩
  have heR : e ∈ ((x • S : Sylow p X) : Set X) := by
    rw [hx]
    exact hER he
  rw [Sylow.coe_smul] at heR
  obtain ⟨s, hs, rfl⟩ := Set.mem_smul_set.1 heR
  have hsP : s ∈ P := by
    have : (S : Subgroup X) = P := Sylow.coe_ofCard P hPcard
    rw [← this]
    exact hs
  obtain ⟨n, -, rfl⟩ := Subgroup.mem_map.1 hsP
  rw [MulAut.smul_def, MulAut.conj_apply]
  have h : x⁻¹ * (x * (N.subtype n) * x⁻¹) * x⁻¹⁻¹ = N.subtype n := by group
  rw [h]
  exact n.2

end CFSG.HardMathSupport.Solomon.UniquenessMaximal.GenL3

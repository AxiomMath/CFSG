module

public import CFSG.LinearAlgebra.IrreducibleBinaryCentralizerField

public section

namespace CFSG.LinearAlgebra

open Module

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]

theorem centralizer_cube_eq_one_of_irreducible_binary_eight
    [FiniteDimensional (ZMod 2) V]
    (hV : Module.finrank (ZMod 2) V = 8)
    (H : Subgroup (LinearMap.GeneralLinearGroup (ZMod 2) V))
    (hirr : ∀ U : Submodule (ZMod 2) V,
      (∀ h ∈ H, ∀ u ∈ U, (h : V →ₗ[ZMod 2] V) u ∈ U) → U = ⊥ ∨ U = ⊤)
    (h2 : 5 ≤ (Nat.card H).factorization 2)
    (a : LinearMap.GeneralLinearGroup (ZMod 2) V)
    (ha : a ∈ Subgroup.centralizer (H : Set (LinearMap.GeneralLinearGroup (ZMod 2) V))) :
    a ^ 3 = 1 := by
  obtain ⟨-, d, hdpos, hdvd, -, hord, -, h2dvd⟩ :=
    irreducible_binary_linear_centralizer_field_degree_bound (n := 8) (by norm_num) hV H hirr a ha
  have hcases : d = 1 ∨ d = 2 ∨ d = 4 ∨ d = 8 := by
    have hle : d ≤ 8 := Nat.le_of_dvd (by norm_num) hdvd
    interval_cases d <;> simp_all
  have h3 : orderOf a ∣ 3 := by
    rcases hcases with rfl | rfl | rfl | rfl
    · have ha1 : a = 1 := by simpa using hord
      rw [ha1]
      simp
    · simpa using hord
    ·
      exfalso
      have hle4 : (Nat.card H).factorization 2 ≤ 4 := by
        have hdiv : 2 ^ (Nat.card H).factorization 2 ∣ 2 ^ 4 := by
          simpa using h2dvd
        exact (Nat.pow_dvd_pow_iff_le_right (by norm_num : 1 < 2)).mp hdiv
      omega
    ·
      exfalso
      have hle0 : (Nat.card H).factorization 2 ≤ 0 := by
        have hdiv : 2 ^ (Nat.card H).factorization 2 ∣ 2 ^ 0 := by
          simpa using h2dvd
        exact (Nat.pow_dvd_pow_iff_le_right (by norm_num : 1 < 2)).mp hdiv
      omega
  exact orderOf_dvd_iff_pow_eq_one.mp h3

end CFSG.LinearAlgebra

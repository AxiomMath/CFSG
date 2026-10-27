module

public import CFSG.LinearAlgebra.LinearGroups.UnitaryOrderSupport

public section

namespace CFSG.LinearGroups

open CFSG.LocalAnalysis.ComponentInitial

variable {p f : ℕ} {K : Type*} [Field K]

theorem unitary_full_group_order (h : UnitaryFieldData p f K) {V : Type*} [AddCommGroup V]
    [Module K V] [FiniteDimensional K V] {B : V →ₛₗ[h.bar] V →ₗ[K] K} (hB : B.IsSymm)
    (hBl : B.SeparatingLeft) {n : ℕ} (hn : Module.finrank K V = n) (hn1 : 1 ≤ n) :
    (Nat.card (sesqUnitaryGroup B) : ℤ) = ((p ^ f : ℕ) : ℤ) ^ (n * (n - 1) / 2) *
        ∏ i ∈ Finset.Icc 1 n, (((p ^ f : ℕ) : ℤ) ^ i - (-1) ^ i) ∧
      (Nat.card (sesqSpecialUnitaryGroup B) : ℤ) = ((p ^ f : ℕ) : ℤ) ^ (n * (n - 1) / 2) *
        ∏ i ∈ Finset.Icc 2 n, (((p ^ f : ℕ) : ℤ) ^ i - (-1) ^ i) ∧
      (∀ c : Kˣ, c ∈ (unitaryDet B).range ↔ h.norm (c : K) = 1) ∧
      Nat.card (unitaryDet B).range = p ^ f + 1 ∧
      (unitaryDet B).ker = (sesqSpecialUnitaryGroup B).subgroupOf (sesqUnitaryGroup B) ∧
      p ^ (Nat.card (sesqUnitaryGroup B)).factorization p = (p ^ f) ^ (n * (n - 1) / 2) ∧
      p ^ (Nat.card (sesqSpecialUnitaryGroup B)).factorization p =
        (p ^ f) ^ (n * (n - 1) / 2) := by
  classical
  obtain ⟨e₀, he₀⟩ := h.exists_orthonormal_basis hB hBl
  let e : Module.Basis (Fin n) K V := e₀.reindex (finCongr hn)
  have he : ⇑e ∈ orthonormalFrames B n := mem_orthonormalFrames.mpr fun i j => by
    simp only [e, Module.Basis.reindex_apply, he₀, (finCongr hn).symm.injective.eq_iff]
  have hU : (Nat.card (sesqUnitaryGroup B) : ℤ) = ((p ^ f : ℕ) : ℤ) ^ (n * (n - 1) / 2) *
      ∏ i ∈ Finset.Icc 1 n, (((p ^ f : ℕ) : ℤ) ^ i - (-1) ^ i) := by
    rw [card_sesqUnitaryGroup_eq hBl e he, card_orthonormalFrames h n hB hBl hn,
      prod_range_eq_pow_mul_prod_Icc]
  have hrange : ∀ c : Kˣ, c ∈ (unitaryDet B).range ↔ h.norm (c : K) = 1 := by
    intro c
    constructor
    · rintro ⟨g, rfl⟩
      rw [unitaryDet_apply]
      exact norm_det_of_isometry h e he (mem_sesqUnitaryGroup.mp g.2)
    · intro hc
      obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
      obtain ⟨φ, hφ, hdet⟩ := exists_isometry_det_eq h e he hc
      exact ⟨isometryUnit hBl hφ, Units.ext (by rw [unitaryDet_apply, coe_isometryUnit, hdet])⟩
  have hrange' : (unitaryDet B).range = (Units.map h.normHom).ker := by
    ext c
    rw [hrange, UnitaryFieldData.mem_ker_normUnits]
  have hcard : Nat.card (unitaryDet B).range = p ^ f + 1 := by
    rw [hrange']
    exact h.card_ker_normUnits_and_surjective.1
  have hker : (unitaryDet B).ker = (sesqSpecialUnitaryGroup B).subgroupOf (sesqUnitaryGroup B) := by
    ext g
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, mem_sesqSpecialUnitaryGroup, Units.ext_iff,
      unitaryDet_apply, Units.val_one]
    exact ⟨fun hg => ⟨g.2, hg⟩, fun hg => hg.2⟩
  have hSUmul : (Nat.card (sesqSpecialUnitaryGroup B) : ℤ) * (((p ^ f : ℕ) : ℤ) + 1) =
      Nat.card (sesqUnitaryGroup B) := by
    have h1 := Subgroup.card_mul_index (unitaryDet B).ker
    rw [Subgroup.index_ker, hcard, hker,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe (sesqSpecialUnitaryGroup_le B)).toEquiv] at h1
    exact_mod_cast h1
  have hSU : (Nat.card (sesqSpecialUnitaryGroup B) : ℤ) = ((p ^ f : ℕ) : ℤ) ^ (n * (n - 1) / 2) *
      ∏ i ∈ Finset.Icc 2 n, (((p ^ f : ℕ) : ℤ) ^ i - (-1) ^ i) := by
    have hq1 : ((p ^ f : ℕ) : ℤ) + 1 ≠ 0 := by positivity
    apply mul_right_cancel₀ hq1
    rw [hSUmul, hU, prod_Icc_one_eq_mul _ hn1]
    ring
  refine ⟨hU, hSU, hrange, hcard, hker, ?_, ?_⟩
  · exact pow_factorization_eq_of_eq_mul h.prime hU
      (not_dvd_prod_pow_sub_neg_one_pow h.prime h.one_le _ fun i hi => (Finset.mem_Icc.mp hi).1)
  · exact pow_factorization_eq_of_eq_mul h.prime hSU
      (not_dvd_prod_pow_sub_neg_one_pow h.prime h.one_le _ fun i hi => by
        have := (Finset.mem_Icc.mp hi).1
        omega)

end CFSG.LinearGroups

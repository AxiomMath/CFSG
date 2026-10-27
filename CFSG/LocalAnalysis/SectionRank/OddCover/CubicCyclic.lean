module

public import Mathlib.FieldTheory.Finite.Extension
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Card
public import Mathlib.GroupTheory.Sylow

public section

namespace CFSG.SectionRank.OddCover

section Sylow

variable {G : Type*} [Group G] [Finite G]

theorem isCyclic_of_isPGroup_of_card_eq_mul {r : ℕ} [hr : Fact r.Prime] {Z : Subgroup G}
    [IsCyclic Z] {m : ℕ} (hG : Nat.card G = Nat.card Z * m) (hrm : ¬ r ∣ m) {R : Subgroup G}
    (hR : IsPGroup r R) : IsCyclic R := by
  have hm : m ≠ 0 := by
    rintro rfl
    exact hrm (dvd_zero r)
  obtain ⟨S₀⟩ := (inferInstance : Nonempty (Sylow r Z))
  have hS₀ := Sylow.card_eq_multiplicity S₀
  have hfact : (Nat.card G).factorization r = (Nat.card Z).factorization r := by
    rw [hG, Nat.factorization_mul Nat.card_pos.ne' hm, Finsupp.add_apply,
      Nat.factorization_eq_zero_of_not_dvd hrm, add_zero]
  let S : Sylow r G := Sylow.ofCard ((S₀ : Subgroup Z).map Z.subtype) (by
    rw [Subgroup.card_map_of_injective Z.subtype_injective, hS₀, hfact])
  have hScyc : IsCyclic (S : Subgroup G) := by
    have : IsCyclic ((S₀ : Subgroup Z).map Z.subtype) :=
      isCyclic_of_surjective ((Z.subtype).subgroupMap (S₀ : Subgroup Z))
        (MonoidHom.subgroupMap_surjective _ _)
    exact this
  obtain ⟨S', hRS'⟩ := hR.exists_le_sylow
  have hS'cyc : IsCyclic (S' : Subgroup G) :=
    isCyclic_of_surjective (S.equiv S').toMonoidHom (S.equiv S').surjective
  have e : R ≃* (R.subgroupOf (S' : Subgroup G)) := (Subgroup.subgroupOfEquivOfLe hRS').symm
  exact isCyclic_of_surjective e.symm.toMonoidHom e.symm.surjective

end Sylow

section Field

variable {k : Type} [Field k]

@[expose] noncomputable def unitsGL {A : Type*} [Ring A] [Algebra k A] {d : ℕ}
    (b : Module.Basis (Fin d) k A) : Aˣ →* GL (Fin d) k :=
  Units.map (Algebra.leftMulMatrix b : A →* Matrix (Fin d) (Fin d) k)

theorem unitsGL_injective {A : Type*} [Ring A] [Algebra k A] {d : ℕ}
    (b : Module.Basis (Fin d) k A) : Function.Injective (unitsGL b) :=
  Units.map_injective (Algebra.leftMulMatrix_injective b)

variable [Finite k]

variable (k) in
theorem exists_isCyclic_card_GL (d : ℕ) [NeZero d] :
    ∃ Z : Subgroup (GL (Fin d) k), IsCyclic Z ∧ Nat.card Z = Nat.card k ^ d - 1 := by
  obtain ⟨p, _⟩ := CharP.exists k
  have : Fact p.Prime := ⟨CharP.char_is_prime k p⟩
  let L := FiniteField.Extension k p d
  let b : Module.Basis (Fin d) k L :=
    Module.finBasisOfFinrankEq k L (FiniteField.finrank_extension k p d)
  refine ⟨(unitsGL b).range, isCyclic_of_surjective _ (unitsGL b).rangeRestrict_surjective, ?_⟩
  rw [← Nat.card_congr (MonoidHom.ofInjective (unitsGL_injective b)).toEquiv, Nat.card_units,
    FiniteField.natCard_extension]

variable (k) in
theorem exists_isCyclic_card_sq_GL_three :
    ∃ Z : Subgroup (GL (Fin 3) k), IsCyclic Z ∧ Nat.card Z = Nat.card k ^ 2 - 1 := by
  obtain ⟨p, _⟩ := CharP.exists k
  have : Fact p.Prime := ⟨CharP.char_is_prime k p⟩
  let L := FiniteField.Extension k p 2
  let b : Module.Basis (Fin 3) k (L × k) := Module.finBasisOfFinrankEq k (L × k) (by
    rw [Module.finrank_prod, FiniteField.finrank_extension, Module.finrank_self])
  let ψ : Lˣ →* (L × k)ˣ := Units.map (MonoidHom.inl L k)
  have hψ : Function.Injective ψ :=
    Units.map_injective fun a a' h => congrArg Prod.fst h
  let φ : Lˣ →* GL (Fin 3) k := (unitsGL b).comp ψ
  have hφ : Function.Injective φ := (unitsGL_injective b).comp hψ
  refine ⟨φ.range, isCyclic_of_surjective _ φ.rangeRestrict_surjective, ?_⟩
  rw [← Nat.card_congr (MonoidHom.ofInjective hφ).toEquiv, Nat.card_units,
    FiniteField.natCard_extension]

variable (k) in
theorem card_GL_three :
    Nat.card (GL (Fin 3) k) =
      (Nat.card k ^ 3 - 1) * (Nat.card k ^ 3 - Nat.card k) * (Nat.card k ^ 3 - Nat.card k ^ 2) := by
  have := Fintype.ofFinite k
  rw [Matrix.card_GL_field, Fin.prod_univ_three, ← Nat.card_eq_fintype_card]
  simp only [Fin.val_zero, Fin.val_one, Fin.val_two, pow_zero, pow_one]

theorem isCyclic_of_isPGroup_GL_three {r : ℕ} [hr : Fact r.Prime] (hrQ : ¬ r ∣ Nat.card k)
    (hr1 : ¬ r ∣ Nat.card k - 1) {R : Subgroup (GL (Fin 3) k)} (hR : IsPGroup r R) :
    IsCyclic R := by
  have hr' := hr.out
  set Q := Nat.card k with hQ
  have hQ1 : 1 ≤ Q := Nat.card_pos
  have e3 : Q ^ 3 - 1 = (Q - 1) * (Q ^ 2 + Q + 1) := by
    zify [hQ1, Nat.one_le_pow 3 Q hQ1]
    ring
  have e2 : Q ^ 2 - 1 = (Q - 1) * (Q + 1) := by
    zify [hQ1, Nat.one_le_pow 2 Q hQ1]
    ring
  have eQ : Q ^ 3 - Q = Q * ((Q - 1) * (Q + 1)) := by
    zify [hQ1, Nat.le_self_pow (by norm_num : 3 ≠ 0) Q]
    ring
  have eQ2 : Q ^ 3 - Q ^ 2 = Q ^ 2 * (Q - 1) := by
    zify [hQ1, Nat.pow_le_pow_right hQ1 (by norm_num : 2 ≤ 3)]
    ring
  have hrQ2 : ¬ r ∣ Q ^ 2 := fun h => hrQ (hr'.dvd_of_dvd_pow h)
  have hrQ3 : ¬ r ∣ Q ^ 3 := fun h => hrQ (hr'.dvd_of_dvd_pow h)
  by_cases hrQp : r ∣ Q + 1
  · obtain ⟨Z, hZ, hZcard⟩ := exists_isCyclic_card_sq_GL_three k
    have hm : ¬ r ∣ (Q ^ 2 + Q + 1) * Q ^ 3 * (Q - 1) * (Q - 1) := by
      have hq : ¬ r ∣ Q ^ 2 + Q + 1 := by
        intro h
        have : r ∣ Q * (Q + 1) + 1 := by rwa [show Q * (Q + 1) + 1 = Q ^ 2 + Q + 1 by ring]
        exact hr'.one_lt.ne' (Nat.dvd_one.1 ((Nat.dvd_add_right (dvd_mul_of_dvd_right hrQp Q)).1
          this))
      exact hr'.not_dvd_mul (hr'.not_dvd_mul (hr'.not_dvd_mul hq hrQ3) hr1) hr1
    refine isCyclic_of_isPGroup_of_card_eq_mul (Z := Z) (m := _) ?_ hm hR
    rw [card_GL_three, hZcard, e3, eQ, eQ2, e2]
    ring
  · obtain ⟨Z, hZ, hZcard⟩ := exists_isCyclic_card_GL k 3
    have hm : ¬ r ∣ (Q * ((Q - 1) * (Q + 1))) * (Q ^ 2 * (Q - 1)) :=
      hr'.not_dvd_mul (hr'.not_dvd_mul hrQ (hr'.not_dvd_mul hr1 hrQp))
        (hr'.not_dvd_mul hrQ2 hr1)
    refine isCyclic_of_isPGroup_of_card_eq_mul (Z := Z) (m := _) ?_ hm hR
    rw [card_GL_three, hZcard, eQ, eQ2]
    ring

theorem finite_field_cubic_cyclic_linear_subgroup (k : Type) [Field k] [Finite k] :
    (∃ Z : Subgroup (GL (Fin 3) k), IsCyclic Z ∧ Nat.card Z = Nat.card k ^ 3 - 1) ∧
      ∀ (r : ℕ) [Fact r.Prime], ¬ r ∣ Nat.card k * (Nat.card k ^ 2 - 1) →
        ∀ R : Subgroup (GL (Fin 3) k), IsPGroup r R → IsCyclic R := by
  refine ⟨exists_isCyclic_card_GL k 3, fun r hr hrQ R hR => ?_⟩
  have hQ1 : 1 ≤ Nat.card k := Nat.card_pos
  have e2 : Nat.card k ^ 2 - 1 = (Nat.card k - 1) * (Nat.card k + 1) := by
    zify [hQ1, Nat.one_le_pow 2 (Nat.card k) hQ1]
    ring
  exact isCyclic_of_isPGroup_GL_three (fun h => hrQ (Dvd.dvd.mul_right h _))
    (fun h => hrQ (Dvd.dvd.mul_left (by rw [e2]; exact Dvd.dvd.mul_right h _) _)) hR

end Field

end CFSG.SectionRank.OddCover

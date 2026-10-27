module

public import CFSG.LocalAnalysis.ComponentClassification.OutcomeLocalCTIUnitarySocle
public import CFSG.LocalAnalysis.ComponentInitial.SmallLinearIsomorphisms

public section

namespace CFSG.LocalAnalysis.ComponentInitial.SteinbergCE

open Subgroup Matrix CFSG.Assembly.LowTwoRank CFSG.ClassicalGroups.UnitaryFlag
  CFSG.LocalAnalysis.ComponentInitial CFSG.ComponentClassification.OutcomeLocal

theorem center_GL_three_zmod_two_eq_bot : center (GL (Fin 3) (ZMod 2)) = ⊥ := by
  rw [Matrix.GeneralLinearGroup.center_eq_range_scalar, eq_bot_iff]
  rintro _ ⟨c, rfl⟩
  rw [mem_bot, Subsingleton.elim c 1, map_one]

theorem statedClassicalModel_PSL_two_seven_of_GL_three_two {J : Type} [Group J]
    (e : J ≃* GL (Fin 3) (ZMod 2)) : StatedClassicalModel (J ⧸ center J) .PSL 2 7 1 := by
  have : Fact (Nat.Prime 7) := ⟨Nat.prime_seven⟩
  have hZ : center J = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    have h1 : e x ∈ center (GL (Fin 3) (ZMod 2)) := by
      rw [mem_center_iff]
      intro y
      obtain ⟨y', rfl⟩ := e.surjective y
      rw [← map_mul, ← map_mul, (mem_center_iff.mp hx) y']
    rw [center_GL_three_zmod_two_eq_bot, mem_bot] at h1
    rw [mem_bot, ← map_eq_one_iff e e.injective, h1]
  obtain ⟨e₇⟩ := nonempty_GL_three_two_equiv_PSL_two_seven
  refine ⟨⟨Nat.prime_seven, le_rfl, le_rfl, by decide, by decide⟩, ZMod 7, inferInstance,
    inferInstance, by rw [Nat.card_zmod, pow_one], ⟨?_⟩⟩
  exact ((((QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot).trans e).trans
    e₇).trans (projectiveSpecialLinearGroupEquivStatedProj 2 (ZMod 7))

theorem not_statedClassicalModel_PSU_of_GL_three_two_component {Y : Type} [Group Y] [Finite Y]
    {D : Subgroup Y} [D.Normal] (hDs : IsSimpleGroup D) (hDnab : ∃ x y : D, x * y ≠ y * x)
    (hCD : centralizer (D : Set Y) = ⊥) {a : Y} (ha : orderOf a = 2) {J : Subgroup Y}
    (hJD : J ≤ D) (hJ : CFSG.Assembly.IsComponentOf J (centralizer ({a} : Set Y)))
    (hJGL : Nonempty (J ≃* GL (Fin 3) (ZMod 2))) (n e : ℕ) :
    ¬ StatedClassicalModel D .PSU n 2 e := by
  rintro ⟨⟨-, he, hn, h32⟩, K, _, _, hK, ⟨φ⟩⟩
  have h : UnitaryFieldData 2 e K := ⟨Nat.prime_two, he, by rw [hK, ← pow_mul, mul_comm]⟩
  obtain ⟨eJ⟩ := hJGL
  have hq : ¬(n = 3 ∧ 2 ^ e = 2) := fun ⟨h3, h2⟩ => h32 (by rw [h3, h2])
  obtain ⟨ρ, -, -, -, -, H₀, C, hC, -, θ, -, ρC, -, -, σ, -, -, Cl, hCl, hrest⟩ :=
    faithful_even_unitary_socle_small_source_involution_selector
      hDs hDnab hCD ha hJD hJ Nat.prime_seven (by norm_num) le_rfl
      (Or.inl (statedClassicalModel_PSL_two_seven_of_GL_three_two eJ)) h hn hq
      (φ.trans (unitaryPSUEquiv h (by omega)).symm)
  obtain ⟨-, -, -, -, -, -, -, -, hrows, -⟩ := hrest
  rcases hrows with ⟨-, -, h75, -⟩ | ⟨-, -, h73, -⟩ | ⟨-, -, h73, -⟩ <;> omega

end CFSG.LocalAnalysis.ComponentInitial.SteinbergCE

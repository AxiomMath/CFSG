module

public import CFSG.CharacterTheory.BlockBasics.LocalRing
public import CFSG.CharacterTheory.BrauerLinearThree.LocalCounting
public import CFSG.CharacterTheory.Semidihedral.Principal.FullPrimePartBlock

public section

namespace CFSG.BrauerLinearThree.QOne

open Matrix CFSG.DesarguesianPlanes CFSG.TwoRankLowerBound.Helpers
open CFSG.Semidihedral.Principal
  (full_prime_part_character_degree_singleton_block_singular_vanishing)

theorem false_of_two_mul_eq_neg_one {x : ℂ} (hx : IsIntegral ℤ x) (h : 2 * x = -1) : False := by
  have hx' : x = algebraMap ℚ ℂ (-1 / 2 : ℚ) := by
    rw [eq_ratCast]
    push_cast
    linear_combination h / 2
  rw [hx'] at hx
  have hq : IsIntegral ℤ (-1 / 2 : ℚ) := isIntegral_algebraMap_iff.mp hx
  obtain ⟨y, hy⟩ := IsIntegrallyClosed.isIntegral_iff.mp hq
  have h2 : ((2 * y : ℤ) : ℚ) = -1 := by
    push_cast
    rw [show (y : ℚ) = algebraMap ℤ ℚ y from rfl, hy]
    norm_num
  have h3 : 2 * y = -1 := by exact_mod_cast h2
  omega

theorem finrank_eq_of_character_one {G : Type} [Group G] [Fintype G]
    (basis : FiniteIrreducibleCharacterBasis G) (χ : basis.index) {d : ℕ}
    (h : (basis.representation χ).character 1 = (d : ℂ)) :
    Module.finrank ℂ (basis.representation χ).vector = d := by
  rw [FiniteComplexRepresentation.character, Representation.char_one] at h
  exact_mod_cast h

theorem cube_mul_eq_split {q : ℕ} (hq : 1 ≤ q) :
    q ^ 3 * (q ^ 3 - 1) * (q ^ 2 - 1) = q ^ 3 * (q - 1) ^ 2 * ((q + 1) * (q ^ 2 + q + 1)) := by
  have h2 : 1 ≤ q ^ 2 := Nat.one_le_pow _ _ hq
  have h3 : 1 ≤ q ^ 3 := Nat.one_le_pow _ _ hq
  zify [hq, h2, h3]
  ring

variable {G : Type} [Group G] {F : Type} [Field F] [Finite F] {Z : Subgroup (GL (Fin 2) F)}
  (hZ : Z ≤ CFSG.Assembly.LowTwoRank.StatedScalars (Fin 2) F)
  (hcard : Nat.card G * Nat.card Z =
    Nat.card F ^ 3 * (Nat.card F ^ 3 - 1) * (Nat.card F ^ 2 - 1))

omit [Group G] in
include hZ hcard in
theorem ringChar_pow_factorization_dvd_cube :
    ringChar F ^ (Nat.card G).factorization (ringChar F) ∣ Nat.card F ^ 3 := by
  have hdvd : ringChar F ^ (Nat.card G).factorization (ringChar F) ∣
      Nat.card F ^ 3 * ((Nat.card F ^ 3 - 1) * (Nat.card F ^ 2 - 1)) := by
    rw [← mul_assoc, ← hcard]
    exact (Nat.ordProj_dvd _ _).mul_right _
  exact (Nat.Coprime.pow_left _ (coprime_facts hZ).2.2).dvd_of_dvd_mul_right hdvd

omit [Group G] in
include hcard in
theorem pow_factorization_dvd_of_dvd_add_one {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hpq : p ∣ Nat.card F + 1) :
    p ^ (Nat.card G).factorization p ∣
      (Nat.card F + 1) * (Nat.card F ^ 2 + Nat.card F + 1) := by
  have hq1 : 1 ≤ Nat.card F := Nat.card_pos
  have hdvd : p ^ (Nat.card G).factorization p ∣ Nat.card F ^ 3 * (Nat.card F - 1) ^ 2 *
      ((Nat.card F + 1) * (Nat.card F ^ 2 + Nat.card F + 1)) := by
    rw [← cube_mul_eq_split hq1, ← hcard]
    exact (Nat.ordProj_dvd _ _).mul_right _
  have hcop : Nat.Coprime p (Nat.card F ^ 3 * (Nat.card F - 1) ^ 2) := by
    apply Nat.Coprime.mul_right
    · apply Nat.Coprime.pow_right
      rw [Nat.Prime.coprime_iff_not_dvd hp]
      intro h
      have : p ∣ Nat.card F + 1 - Nat.card F := Nat.dvd_sub hpq h
      rw [Nat.add_sub_cancel_left] at this
      exact hp.one_lt.ne' (Nat.dvd_one.mp this)
    · apply Nat.Coprime.pow_right
      rw [Nat.Prime.coprime_iff_not_dvd hp]
      intro h
      have : p ∣ Nat.card F + 1 - (Nat.card F - 1) := Nat.dvd_sub hpq h
      rw [show Nat.card F + 1 - (Nat.card F - 1) = 2 by omega] at this
      exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp this)
  exact (Nat.Coprime.pow_left _ hcop).dvd_of_dvd_mul_left hdvd

variable [Fintype G] (basis : FiniteIrreducibleCharacterBasis G) {χ₁ χ₂ χ₃ χ₅ : basis.index}
  (hχ₁ : (basis.representation χ₁).character 1 = (Nat.card F : ℂ) ^ 3)
  (hχ₅ : (basis.representation χ₅).character 1 =
    ((Nat.card F : ℂ) + 1) * ((Nat.card F : ℂ) ^ 2 + Nat.card F + 1))
  (hrel₁ : ∀ g : G, Odd (orderOf g) →
    -1 + (basis.representation χ₁).character g =
      (basis.representation χ₂).character g - (basis.representation χ₃).character g)
  (hrel₃ : ∀ g : G, Odd (orderOf g) →
    (basis.representation χ₂).character g + (basis.representation χ₃).character g =
      (basis.representation χ₅).character g)

include hZ hcard hχ₁ in
theorem character_eq_zero_of_ringChar_dvd {g : G} (hg : ringChar F ∣ orderOf g) :
    (basis.representation χ₁).character g = 0 := by
  have hp : (ringChar F).Prime := CharP.char_is_prime F _
  have : Fact (ringChar F).Prime := ⟨hp⟩
  obtain ⟨ideal, hmax, hmem⟩ := (CFSG.BlockBasics.residue_prime_existence _ hp).1
  have : CharP (ComplexAlgebraicIntegers ⧸ ideal) (ringChar F) :=
    (CFSG.BlockBasics.residue_prime_existence _ hp).2 ideal hmax hmem
  have hdeg : ringChar F ^ (Nat.card G).factorization (ringChar F) ∣
      Module.finrank ℂ (basis.representation χ₁).vector := by
    rw [finrank_eq_of_character_one basis χ₁ (d := Nat.card F ^ 3) (by rw [hχ₁]; push_cast; rfl)]
    exact ringChar_pow_factorization_dvd_cube hZ hcard
  exact (full_prime_part_character_degree_singleton_block_singular_vanishing basis ideal
    (ringChar F) χ₁ hdeg).2 g hg

include hcard hχ₅ in
theorem character_eq_zero_of_dvd_add_one {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hpq : p ∣ Nat.card F + 1) {g : G} (hg : p ∣ orderOf g) :
    (basis.representation χ₅).character g = 0 := by
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨ideal, hmax, hmem⟩ := (CFSG.BlockBasics.residue_prime_existence _ hp).1
  have : CharP (ComplexAlgebraicIntegers ⧸ ideal) p :=
    (CFSG.BlockBasics.residue_prime_existence _ hp).2 ideal hmax hmem
  have hdeg : p ^ (Nat.card G).factorization p ∣
      Module.finrank ℂ (basis.representation χ₅).vector := by
    rw [finrank_eq_of_character_one basis χ₅
      (d := (Nat.card F + 1) * (Nat.card F ^ 2 + Nat.card F + 1)) (by rw [hχ₅]; push_cast; rfl)]
    exact pow_factorization_dvd_of_dvd_add_one hcard hp hp2 hpq
  exact (full_prime_part_character_degree_singleton_block_singular_vanishing basis ideal p χ₅
    hdeg).2 g hg

include hZ hcard hχ₁ hχ₅ hrel₁ hrel₃ in
theorem orderOf_ne_mul_ringChar (h2 : (2 : F) ≠ 0) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hpq : p ∣ Nat.card F + 1) (g : G) : orderOf g ≠ p * ringChar F := by
  intro hg
  have hp₀ : (ringChar F).Prime := CharP.char_is_prime F _
  have hp₀2 : ringChar F ≠ 2 := by
    intro h
    apply h2
    have := ringChar.Nat.cast_ringChar (R := F)
    rw [h] at this
    exact_mod_cast this
  have hodd : Odd (orderOf g) := by
    rw [hg]
    exact (hp.odd_of_ne_two hp2).mul (hp₀.odd_of_ne_two hp₀2)
  have h1 := character_eq_zero_of_ringChar_dvd hZ hcard basis hχ₁ (g := g)
    (by rw [hg]; exact dvd_mul_left _ _)
  have h5 := character_eq_zero_of_dvd_add_one hcard basis hχ₅ hp hp2 hpq (g := g)
    (by rw [hg]; exact dvd_mul_right _ _)
  have e1 := hrel₁ g hodd
  have e3 := hrel₃ g hodd
  rw [h1] at e1
  rw [h5] at e3
  exact false_of_two_mul_eq_neg_one (finite_character_value_isIntegral _ g)
    (by linear_combination -e1 + e3)

end CFSG.BrauerLinearThree.QOne

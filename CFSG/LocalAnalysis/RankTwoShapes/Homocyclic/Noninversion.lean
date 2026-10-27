module

public import CFSG.CharacterTheory.TwoRankLowerBound.BlockSectionOrthogonality
public import CFSG.CharacterTheory.TwoRankLowerBound.PrimePrimaryFactorization
public import CFSG.CharacterTheory.TwoRankLowerBound.VirtualPairingIntegral
public import CFSG.CharacterTheory.TwoRankLowerBound.CharacterInflation
public import CFSG.CharacterTheory.TwoRankLowerBound.ClassSum

public section

namespace CFSG.RankTwoShapes

open CFSG.TwoRankLowerBound.Helpers
open scoped BigOperators Classical

universe u

theorem characterPairing_restrict_eq {G : Type*} [Group G] [Fintype G] (Q : Subgroup G)
    (χ : G → ℂ) (θ : Q → ℂ) :
    characterPairing (fun x : Q => χ x.val) θ =
      (Nat.card Q : ℂ)⁻¹ * ∑ y : Q, χ (y : G)⁻¹ * θ y := by
  unfold characterPairing
  congr 1
  rw [← Equiv.sum_comp (Equiv.inv Q)]
  apply Finset.sum_congr rfl
  intro y _
  simp

theorem restriction_pairing_sum_eq_zero {G : Type*} [Group G] [Fintype G]
    (basis : FiniteIrreducibleCharacterBasis G) (support : Finset basis.index) (Q : Subgroup G)
    (U : Set G) (θ : Q → ℂ) (hθU : ∀ x : Q, (x : G) ∉ U → θ x = 0) (F : basis.index → ℂ)
    (hF : ∀ y : G, y ∈ U →
      ∑ label ∈ support, (basis.representation label).character y⁻¹ * F label = 0) :
    ∑ label ∈ support,
        characterPairing (fun x : Q => (basis.representation label).character x.val) θ *
          F label = 0 := by
  simp_rw [characterPairing_restrict_eq]
  have hswap : ∑ label ∈ support, (Nat.card Q : ℂ)⁻¹ *
      (∑ y : Q, (basis.representation label).character (y : G)⁻¹ * θ y) * F label =
      (Nat.card Q : ℂ)⁻¹ * ∑ y : Q, θ y *
        ∑ label ∈ support, (basis.representation label).character (y : G)⁻¹ * F label := by
    rw [Finset.mul_sum]
    simp_rw [Finset.mul_sum, Finset.sum_mul]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro y _
    apply Finset.sum_congr rfl
    intro label _
    ring
  rw [hswap]
  apply mul_eq_zero_of_right
  apply Finset.sum_eq_zero
  intro y _
  by_cases hy : (y : G) ∈ U
  · rw [hF (y : G) hy, mul_zero]
  · rw [hθU y hy, zero_mul]

theorem orderOf_dvd_prime_pow_of_mem {G : Type*} [Group G] {p : ℕ} (Q : Subgroup G)
    (hQ : IsPGroup p Q) (y : G) (hy : y ∈ Q) : ∃ k : ℕ, orderOf y ∣ p ^ k := by
  obtain ⟨k, hk⟩ := hQ ⟨y, hy⟩
  refine ⟨k, orderOf_dvd_of_pow_eq_one ?_⟩
  have := congrArg Subtype.val hk
  simpa using this

theorem principal_noninversion_restriction_identities {G : Type u} [Group G] [Fintype G]
    (basis : FiniteIrreducibleCharacterBasis G) (ideal : Ideal ComplexAlgebraicIntegers)
    [ideal.IsMaximal] (prime : ℕ) [Fact prime.Prime]
    [CharP (ComplexAlgebraicIntegers ⧸ ideal) prime]
    (principal : basis.index)
    (Q : Subgroup G) (hQ : IsPGroup prime Q) (J : G) (hJ : orderOf J = 2)
    (U : Set G) (hUQ : U ⊆ Q) (hU : ∀ x ∈ U, ∀ t : G, IsConj J t → t * x * t⁻¹ ≠ x⁻¹)
    (θ : Q → ℂ) (hθ : θ ∈ virtualCharacters Q) (hθU : ∀ x : Q, (x : G) ∉ U → θ x = 0) :
    (∀ label, ∃ integer : ℤ,
      characterPairing (fun x : Q => (basis.representation label).character x.val) θ = integer) ∧
    (∑ label ∈ coefficientBlock basis (localizedComplexIntegerRing ideal) principal,
      characterPairing (fun x : Q => (basis.representation label).character x.val) θ *
        (basis.representation label).character 1 = 0) ∧
    (∑ label ∈ coefficientBlock basis (localizedComplexIntegerRing ideal) principal,
      characterPairing (fun x : Q => (basis.representation label).character x.val) θ *
        (basis.representation label).character J = 0) ∧
    (∑ label ∈ coefficientBlock basis (localizedComplexIntegerRing ideal) principal,
      characterPairing (fun x : Q => (basis.representation label).character x.val) θ *
        ((basis.representation label).character J ^ 2 /
          (basis.representation label).character 1) = 0) := by
  set B := coefficientBlock basis (localizedComplexIntegerRing ideal) principal
  have hJsq : J * J = 1 := by
    rw [← pow_two, ← hJ, pow_orderOf_eq_one]
  have hJinv : J⁻¹ = J := inv_eq_of_mul_eq_one_left hJsq
  have hUne : ∀ y ∈ U, y ≠ 1 := by
    rintro y hy rfl
    exact hU 1 hy J (IsConj.refl J) (by simp)
  have hUorder : ∀ y ∈ U, ∃ k : ℕ, orderOf y ∣ prime ^ k := fun y hy =>
    orderOf_dvd_prime_pow_of_mem Q hQ y (hUQ hy)
  have horth : ∀ (z : G) (y : G), y ∈ U →
      (∀ primary ∈ Subgroup.zpowers z, IsConj primary y → False) →
      ∑ label ∈ B, (basis.representation label).character y⁻¹ *
        (basis.representation label).character z = 0 := by
    intro z y hy hnot
    obtain ⟨primary, regular, exponent, hprimaryMem, _, hcommute, hproduct, hprimary, hregular⟩ :=
      finite_prime_primary_factorization z prime Fact.out
    obtain ⟨k, hk⟩ := hUorder y hy
    have hsum := coefficientBlock_section_column_orthogonality basis ideal prime principal
      primary y regular 1 exponent k hprimary hk hregular (by simp) hcommute (Commute.one_right y)
      (fun hconj => hnot primary hprimaryMem hconj)
    rw [hproduct, mul_one] at hsum
    rw [← hsum]
    apply Finset.sum_congr rfl
    intro label _
    ring
  refine ⟨?_, ?_, ?_, ?_⟩
  ·
    intro label
    apply characterPairing_virtual_integer _ θ _ hθ
    exact character_mem_virtualCharacters
      (inflatedFiniteComplexRepresentation Q.subtype (basis.representation label))
  ·
    apply restriction_pairing_sum_eq_zero basis B Q U θ hθU
    intro y hy
    apply horth 1 y hy
    intro primary hprimary hconj
    rw [Subgroup.zpowers_one_eq_bot, Subgroup.mem_bot] at hprimary
    subst hprimary
    exact hUne y hy (isConj_one_right.mp hconj)
  ·
    apply restriction_pairing_sum_eq_zero basis B Q U θ hθU
    intro y hy
    apply horth J y hy
    intro primary hprimary hconj
    obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp hprimary
    have hcases : J ^ m = 1 ∨ J ^ m = J := by
      have hm := Int.emod_two_eq_zero_or_one m
      have hpow : J ^ m = J ^ (m % 2) := by
        rw [← zpow_mod_orderOf, hJ]
        norm_cast
      rcases hm with hm | hm
      · left
        rw [hpow, hm, zpow_zero]
      · right
        rw [hpow, hm, zpow_one]
    rcases hcases with h1 | hJm
    · rw [h1] at hconj
      exact hUne y hy (isConj_one_right.mp hconj)
    · rw [hJm] at hconj
      apply hU y hy y hconj
      have hy2 : y * y = 1 := by
        obtain ⟨c, hc⟩ := isConj_iff.mp hconj
        rw [← hc]
        calc c * J * c⁻¹ * (c * J * c⁻¹) = c * (J * J) * c⁻¹ := by group
          _ = 1 := by rw [hJsq]; group
      rw [mul_inv_cancel_right]
      exact (inv_eq_of_mul_eq_one_left hy2).symm
  ·
    apply restriction_pairing_sum_eq_zero basis B Q U θ hθU
    intro y hy
    let C : Finset G := Finset.univ.filter (IsConj J)
    have hCinv : ∀ conjugator element : G,
        element ∈ C ↔ conjugator * element * conjugator⁻¹ ∈ C := by
      intro conjugator element
      simp only [C, Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · intro h
        exact h.trans (isConj_iff.mpr ⟨conjugator, rfl⟩)
      · intro h
        exact h.trans (isConj_iff.mpr ⟨conjugator, rfl⟩).symm
    have hCconj : ∀ element ∈ C, IsConj J element := by
      intro element helement
      simpa [C] using helement
    have hCcard : (C.card : ℂ) ≠ 0 := by
      have : J ∈ C := Finset.mem_filter.mpr ⟨Finset.mem_univ _, IsConj.refl J⟩
      exact Nat.cast_ne_zero.mpr (Finset.card_ne_zero_of_mem this)
    have hclass : ∀ label, (basis.representation label).character J ^ 2 /
        (basis.representation label).character 1 =
        ((C.card : ℂ) ^ 2)⁻¹ *
          ∑ a ∈ C, ∑ b ∈ C, (basis.representation label).character (a * b) := by
      intro label
      let : (basis.representation label).representation.IsIrreducible := basis.irreducible label
      have hdegree := irreducible_character_degree_ne_zero (basis.representation label)
        (basis.irreducible label)
      have h := irreducible_conjugacy_class_quadratic_evaluation
        (basis.representation label).representation J C hCinv hCconj hdegree
      change ∑ a ∈ C, ∑ b ∈ C, (basis.representation label).character (a * b) =
        (C.card : ℂ) ^ 2 * (basis.representation label).character J ^ 2 /
          (basis.representation label).character 1 at h
      rw [h]
      field_simp
    have hpair : ∀ a ∈ C, ∀ b ∈ C, ∑ label ∈ B, (basis.representation label).character y⁻¹ *
        (basis.representation label).character (a * b) = 0 := by
      intro a ha b hb
      apply horth (a * b) y hy
      intro primary hprimary hconj
      have haJ := hCconj a ha
      have hbJ := hCconj b hb
      have ha2 : a * a = 1 := by
        obtain ⟨c, hc⟩ := isConj_iff.mp haJ
        rw [← hc]
        calc c * J * c⁻¹ * (c * J * c⁻¹) = c * (J * J) * c⁻¹ := by group
          _ = 1 := by rw [hJsq]; group
      have hb2 : b * b = 1 := by
        obtain ⟨c, hc⟩ := isConj_iff.mp hbJ
        rw [← hc]
        calc c * J * c⁻¹ * (c * J * c⁻¹) = c * (J * J) * c⁻¹ := by group
          _ = 1 := by rw [hJsq]; group
      have hainv : a⁻¹ = a := inv_eq_of_mul_eq_one_left ha2
      have hbinv : b⁻¹ = b := inv_eq_of_mul_eq_one_left hb2
      have hinvert : a * (a * b) * a⁻¹ = (a * b)⁻¹ := by
        rw [mul_inv_rev, hainv, hbinv, ← mul_assoc, ha2, one_mul]
      obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp hprimary
      have hinvertPow : a * (a * b) ^ m * a⁻¹ = ((a * b) ^ m)⁻¹ := by
        have := congrArg (· ^ m) hinvert
        rw [← inv_zpow, ← this]
        exact conj_zpow.symm
      obtain ⟨g, hg⟩ := isConj_iff.mp hconj
      apply hU y hy (g * a * g⁻¹) (haJ.trans (isConj_iff.mpr ⟨g, rfl⟩))
      rw [← hg]
      calc g * a * g⁻¹ * (g * (a * b) ^ m * g⁻¹) * (g * a * g⁻¹)⁻¹ =
          g * (a * (a * b) ^ m * a⁻¹) * g⁻¹ := by group
        _ = (g * (a * b) ^ m * g⁻¹)⁻¹ := by rw [hinvertPow]; group
    calc ∑ label ∈ B, (basis.representation label).character y⁻¹ *
          ((basis.representation label).character J ^ 2 /
            (basis.representation label).character 1) =
        ((C.card : ℂ) ^ 2)⁻¹ * ∑ a ∈ C, ∑ b ∈ C, ∑ label ∈ B,
          (basis.representation label).character y⁻¹ *
            (basis.representation label).character (a * b) := by
          simp_rw [hclass, Finset.mul_sum]
          rw [Finset.sum_comm]
          apply Finset.sum_congr rfl
          intro a _
          rw [Finset.sum_comm]
          apply Finset.sum_congr rfl
          intro b _
          apply Finset.sum_congr rfl
          intro label _
          ring
      _ = 0 := by
          apply mul_eq_zero_of_right
          apply Finset.sum_eq_zero
          intro a ha
          apply Finset.sum_eq_zero
          intro b hb
          exact hpair a ha b hb

end CFSG.RankTwoShapes

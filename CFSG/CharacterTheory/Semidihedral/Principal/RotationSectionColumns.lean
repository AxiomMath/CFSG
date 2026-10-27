module

public import CFSG.CharacterTheory.Semidihedral.Principal.RotationFusion
public import CFSG.CharacterTheory.Semidihedral.Principal.SectionConstancy

public section

open scoped BigOperators Classical

namespace CFSG.Semidihedral.Principal

open CFSG.TwoRankLowerBound.Helpers CFSG.RankTwoShapes CFSG.Open

variable {G : Type*} [Group G] [Fintype G] {n : ℕ} {S : Sylow 2 G}

omit [Fintype G] in
theorem suppliedRotation_zpow_orderOf_dvd (hn : 3 ≤ n)
    (e : SemidihedralGroup n ≃* (S : Subgroup G)) (i : ℤ) :
    orderOf ((e (r n) : G) ^ i) ∣ 2 ^ (n - 1) := by
  apply orderOf_dvd_of_pow_eq_one
  rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast,
    show 2 ^ (n - 1) = modulus n from rfl, ← suppliedRotation_orderOf hn e, pow_orderOf_eq_one,
    one_zpow]

theorem noncentralRotation_section_data (hn : 4 ≤ n)
    (e : SemidihedralGroup n ≃* (S : Subgroup G)) (i : ℤ) (hi0 : ¬ i ≡ 0 [ZMOD modulus n])
    (hi1 : ¬ i ≡ (modulus n / 2 : ℕ) [ZMOD modulus n]) :
    ∃ (R : Subgroup (Subgroup.centralizer (Subgroup.zpowers ((e (r n) : G) ^ i) : Set G)))
      (_ : R.Normal), Nat.Coprime 2 (Nat.card R) ∧
      IsPGroup 2 (Subgroup.centralizer (Subgroup.zpowers ((e (r n) : G) ^ i) : Set G) ⧸ R) ∧
      (∀ x, x ∈ R ↔ Odd (orderOf x)) ∧
      Nat.card (Subgroup.centralizer (Subgroup.zpowers ((e (r n) : G) ^ i) : Set G) ⧸ R) =
        modulus n := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨R, hRn, ⟨hRodd, k, hk⟩, -, -, hmem, -, -, hbij⟩ :=
    noncentralRotation_normal_odd_complement_zpowers hn e i hi0 hi1
  refine ⟨R, hRn, Nat.coprime_two_left.mpr hRodd, IsPGroup.of_card hk, hmem, ?_⟩
  rw [← Nat.card_congr (Equiv.ofBijective _ hbij)]
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (show Subgroup.zpowers (e (r n) : G) ≤
      Subgroup.centralizer (Subgroup.zpowers ((e (r n) : G) ^ i) : Set G) by
    rw [suppliedRotation_centralizer_zpowers]; exact suppliedRotation_le_centralizer e i)).toEquiv,
    Nat.card_zpowers, suppliedRotation_orderOf (by omega) e]

theorem noncentral_rotation_principal_section_columns (hn : 4 ≤ n)
    (e : SemidihedralGroup n ≃* (S : Subgroup G)) (basis : FiniteIrreducibleCharacterBasis G)
    (ideal : Ideal ComplexAlgebraicIntegers) [ideal.IsMaximal]
    [CharP (ComplexAlgebraicIntegers ⧸ ideal) 2] (principal : basis.index)
    (hprincipal : (basis.representation principal).character = 1) :
    (∀ i : ℤ, ¬ i ≡ 0 [ZMOD modulus n] → ¬ i ≡ (modulus n / 2 : ℕ) [ZMOD modulus n] →
      ∀ χ ∈ coefficientBlock basis (localizedComplexIntegerRing ideal) principal,
      ∀ y ∈ Subgroup.centralizer {(e (r n) : G) ^ i}, Odd (orderOf y) →
        (basis.representation χ).character ((e (r n) : G) ^ i * y) =
          (basis.representation χ).character ((e (r n) : G) ^ i)) ∧
    (∀ i j : ℤ, ¬ i ≡ 0 [ZMOD modulus n] → ¬ i ≡ (modulus n / 2 : ℕ) [ZMOD modulus n] →
      ¬ j ≡ 0 [ZMOD modulus n] → ¬ j ≡ (modulus n / 2 : ℕ) [ZMOD modulus n] →
      ∑ χ ∈ coefficientBlock basis (localizedComplexIntegerRing ideal) principal,
          (basis.representation χ).character ((e (r n) : G) ^ i) *
            starRingEnd ℂ ((basis.representation χ).character ((e (r n) : G) ^ j)) =
        if j ≡ i [ZMOD modulus n] ∨ j ≡ (((modulus n / 2 : ℕ) : ℤ) - 1) * i [ZMOD modulus n]
        then (modulus n : ℂ) else 0) ∧
    (∀ i : ℤ, ¬ i ≡ 0 [ZMOD modulus n] → ¬ i ≡ (modulus n / 2 : ℕ) [ZMOD modulus n] →
      ∀ x : G, (∀ a c : G, a * c = x → Commute a c → (∃ k : ℕ, orderOf a = 2 ^ k) →
          Odd (orderOf c) → ¬ IsConj a ((e (r n) : G) ^ i)) →
        ∑ χ ∈ coefficientBlock basis (localizedComplexIntegerRing ideal) principal,
          (basis.representation χ).character ((e (r n) : G) ^ i) *
            starRingEnd ℂ ((basis.representation χ).character x) = 0) ∧
    (∀ i : ℤ, ¬ i ≡ 0 [ZMOD modulus n] → ¬ i ≡ (modulus n / 2 : ℕ) [ZMOD modulus n] →
      ∀ x : G, Odd (orderOf x) →
        ∑ χ ∈ coefficientBlock basis (localizedComplexIntegerRing ideal) principal,
          (basis.representation χ).character ((e (r n) : G) ^ i) *
            starRingEnd ℂ ((basis.representation χ).character x) = 0) ∧
    (∀ i : ℤ, ¬ i ≡ 0 [ZMOD modulus n] → ¬ i ≡ (modulus n / 2 : ℕ) [ZMOD modulus n] →
      ∀ x a c : G, a * c = x → Commute a c → orderOf a = 2 → Odd (orderOf c) →
        ∑ χ ∈ coefficientBlock basis (localizedComplexIntegerRing ideal) principal,
          (basis.representation χ).character ((e (r n) : G) ^ i) *
            starRingEnd ℂ ((basis.representation χ).character x) = 0) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hu : ∀ i : ℤ, orderOf ((e (r n) : G) ^ i) ∣ 2 ^ (n - 1) := fun i =>
    suppliedRotation_zpow_orderOf_dvd (by omega) e i
  have horth : ∀ (i : ℤ) (a c : G) (k : ℕ), orderOf a ∣ 2 ^ k → Nat.Coprime 2 (orderOf c) →
      Commute a c → ¬ IsConj ((e (r n) : G) ^ i) a →
      ∑ χ ∈ coefficientBlock basis (localizedComplexIntegerRing ideal) principal,
          (basis.representation χ).character ((e (r n) : G) ^ i) *
            starRingEnd ℂ ((basis.representation χ).character (a * c)) = 0 := by
    intro i a c k ha hc hac hnot
    have h1 : Nat.Coprime 2 (orderOf (1 : G)) := by
      rw [orderOf_one]; exact Nat.coprime_one_right 2
    have h := coefficientBlock_section_column_orthogonality basis ideal 2 principal
      ((e (r n) : G) ^ i) a 1 c (n - 1) k (hu i) ha h1 hc (Commute.one_right _) hac hnot
    rw [mul_one] at h
    rw [← h]
    refine Finset.sum_congr rfl fun χ _ => ?_
    rw [finite_character_conjugate_inverse]
  have hnot2 : ∀ (i : ℤ), ¬ i ≡ 0 [ZMOD modulus n] →
      ¬ i ≡ (modulus n / 2 : ℕ) [ZMOD modulus n] → ∀ a : G, a ^ 2 = 1 →
        ¬ IsConj ((e (r n) : G) ^ i) a := by
    intro i hi0 hi1 a ha hconj
    obtain ⟨g, hg⟩ := isConj_iff.mp hconj
    apply noncentralRotation_sq_ne_one (by omega) e i hi0 hi1
    have : (g * (e (r n) : G) ^ i * g⁻¹) ^ 2 = 1 := by rw [hg]; exact ha
    rw [conj_pow] at this
    have h2 := congrArg (fun x => g⁻¹ * x * g) this
    simpa [mul_assoc] using h2
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  ·
    intro i hi0 hi1 χ hχ y hy hyodd
    obtain ⟨R, hRn, hR, hquot, hmem, -⟩ := noncentralRotation_section_data hn e i hi0 hi1
    have hyC : y ∈ Subgroup.centralizer (Subgroup.zpowers ((e (r n) : G) ^ i) : Set G) := by
      rw [suppliedRotation_centralizer_zpowers]; exact hy
    have hyR : (⟨y, hyC⟩ : Subgroup.centralizer
        (Subgroup.zpowers ((e (r n) : G) ^ i) : Set G)) ∈ R := by
      rw [hmem, Subgroup.orderOf_mk]; exact hyodd
    exact principal_character_section_constant_of_normal_complement basis ideal 2 principal
      hprincipal (hu i) R hR hquot hχ hyR
  ·
    intro i j hi0 hi1 hj0 hj1
    split_ifs with hij
    ·
      have hconj : IsConj ((e (r n) : G) ^ i) ((e (r n) : G) ^ j) :=
        (noncentralRotation_isConj_iff hn e i j hj0 hj1).mpr hij
      have hval : ∀ χ : basis.index, (basis.representation χ).character ((e (r n) : G) ^ j) =
          (basis.representation χ).character ((e (r n) : G) ^ i) := by
        intro χ
        obtain ⟨g, hg⟩ := isConj_iff.mp hconj
        rw [← hg]
        exact Representation.char_conj _ _ _
      simp only [hval]
      obtain ⟨R, hRn, hR, hquot, -, hcard⟩ := noncentralRotation_section_data hn e i hi0 hi1
      obtain ⟨localBasis⟩ := finiteIrreducibleCharacterBasis_exists
        (G := Subgroup.centralizer (Subgroup.zpowers ((e (r n) : G) ^ i) : Set G))
      obtain ⟨localPrincipal, hlocalPrincipal⟩ :=
        finiteIrreducibleCharacterBasis_contains_irreducible localBasis
          (principalFiniteComplexRepresentation _)
          (principalFiniteComplexRepresentation_isIrreducible _)
      rw [principalFiniteComplexRepresentation_character] at hlocalPrincipal
      obtain ⟨h1, h2, -⟩ := principal_primary_column_centralizer_norm_of_normal_complement basis
        ideal 2 principal hprincipal ((e (r n) : G) ^ i) (n - 1) (hu i) localBasis
        localPrincipal hlocalPrincipal R hR hquot
      rw [h1, h2, hcard]
    ·
      have hnot : ¬ IsConj ((e (r n) : G) ^ i) ((e (r n) : G) ^ j) := fun h =>
        hij ((noncentralRotation_isConj_iff hn e i j hj0 hj1).mp h)
      have h := horth i ((e (r n) : G) ^ j) 1 (n - 1) (hu j)
        (by rw [orderOf_one]; exact Nat.coprime_one_right 2) (Commute.one_right _) hnot
      simpa only [mul_one] using h
  ·
    intro i hi0 hi1 x hx
    obtain ⟨a, c, k, -, -, hac, hacx, ha, hc⟩ := finite_prime_primary_factorization x 2
      Nat.prime_two
    have hnot : ¬ IsConj ((e (r n) : G) ^ i) a := fun h => hx a c hacx hac (by
      obtain ⟨m, -, hm⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp ha
      exact ⟨m, hm⟩) (Nat.coprime_two_left.mp hc) h.symm
    rw [← hacx]
    exact horth i a c k ha hc hac hnot
  ·
    intro i hi0 hi1 x hx
    have h := horth i 1 x 0 (by rw [orderOf_one]; exact one_dvd _)
      (Nat.coprime_two_left.mpr hx) (Commute.one_left _)
      (hnot2 i hi0 hi1 1 (one_pow 2))
    simpa only [one_mul] using h
  ·
    intro i hi0 hi1 x a c hacx hac ha hc
    rw [← hacx]
    exact horth i a c 1 (by rw [ha, pow_one]) (Nat.coprime_two_left.mpr hc) hac
      (hnot2 i hi0 hi1 a (by rw [← ha]; exact pow_orderOf_eq_one a))

end CFSG.Semidihedral.Principal

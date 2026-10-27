module

public import CFSG.CharacterTheory.Semidihedral.FieldFactorOneLocalBlocks
public import CFSG.CharacterTheory.Semidihedral.Principal.RotationSectionColumns

public section

open scoped BigOperators Classical

namespace CFSG.Semidihedral.FieldFactorOne

open CFSG.Open CFSG.Semidihedral CFSG.Semidihedral.ActualSimpleLayerLocalPackage
open CFSG.TwoRankLowerBound.Helpers CFSG.Wreathed CFSG.Wreathed.CompatibleFamily
open CFSG.Wreathed.LinearLocalTwistMoment CFSG.RankTwoShapes CFSG.Semidihedral.Principal

variable {G : Type} [Group G] [Fintype G] {n : ℕ} {S : Sylow 2 G}
  (fS : SemidihedralGroup n ≃* (S : Subgroup G)) {t : G}

omit [Fintype G] in
theorem t_mem_zpowers_rotation [Finite G] (hn : 4 ≤ n) (ht : t = (fS (r n) : G) ^ 2 ^ (n - 2))
    (i : ℤ) (hi0 : ¬ i ≡ 0 [ZMOD modulus n]) :
    t ∈ Subgroup.zpowers ((fS (r n) : G) ^ i) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set u : G := (fS (r n) : G) ^ i with hu
  have hu2 : IsPGroup 2 (Subgroup.zpowers u) := by
    obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp
      (suppliedRotation_zpow_orderOf_dvd (by omega) fS i)
    exact IsPGroup.of_card (n := k) (by rw [Nat.card_zpowers, hk])
  have hu1 : u ≠ 1 := by
    intro h
    apply hi0
    rw [← suppliedRotation_zpow_eq_iff (by omega) fS, zpow_zero]
    exact h
  have hne : Subgroup.zpowers u ≠ ⊥ := by
    intro h
    apply hu1
    have : u ∈ Subgroup.zpowers u := Subgroup.mem_zpowers u
    rwa [h, Subgroup.mem_bot] at this
  have : Nontrivial (Subgroup.zpowers u) := (Subgroup.nontrivial_iff_ne_bot _).mpr hne
  have hdvd : 2 ∣ Nat.card (Subgroup.zpowers u) := by
    rcases hu2.card_eq_or_dvd with h | h
    · exact absurd h (Finite.one_lt_card).ne'
    · exact h
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := Subgroup.zpowers u) 2 hdvd
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp x.2
  have hxG : (x : G) = (fS (r n) : G) ^ (i * k) := by
    rw [← hk, hu, ← zpow_mul]
  have hord : orderOf (r n ^ (i * k)) = 2 := by
    have h1 : orderOf (x : G) = 2 := by rw [Subgroup.orderOf_coe, hx]
    rw [hxG, ← Subgroup.coe_zpow, ← map_zpow, Subgroup.orderOf_coe, MulEquiv.orderOf_eq] at h1
    exact h1
  rw [r_zpow_eq_element n (by omega), rotation_involution_iff n (by omega)] at hord
  have hmod : i * k ≡ ((2 ^ (n - 2) : ℕ) : ℤ) [ZMOD modulus n] := by
    rw [← ZMod.intCast_eq_intCast_iff, hord, half]
    push_cast
    rfl
  have hxt : (x : G) = t := by
    rw [hxG, ht, (suppliedRotation_zpow_eq_iff (by omega) fS _ _).mpr hmod]
    norm_cast
  rw [← hxt]
  exact x.2

theorem central_character_mul_conj {H : Type*} [Group H] [Fintype H]
    (basis : FiniteIrreducibleCharacterBasis H) (ψ : basis.index) {c : H}
    (hc : c ∈ Subgroup.center H) :
    (basis.representation ψ).character c * starRingEnd ℂ ((basis.representation ψ).character c) =
      (basis.representation ψ).character 1 ^ 2 := by
  obtain ⟨ζ, hζ, hrep⟩ := irreducible_central_scalar_root (basis.representation ψ)
    (basis.irreducible ψ) c hc (orderOf c) (orderOf_pos c) (pow_orderOf_eq_one c)
  have hval : (basis.representation ψ).character c =
      (ζ : ℂ) * (basis.representation ψ).character 1 := by
    rw [FiniteComplexRepresentation.character, Representation.character, hrep, map_smul,
      smul_eq_mul, Representation.char_one]
    simp
  have hnorm : (ζ : ℂ) * starRingEnd ℂ (ζ : ℂ) = 1 := by
    have hpow : (ζ : ℂ) ^ orderOf c = 1 := by
      have := congrArg (fun z : ComplexAlgebraicIntegers => (z : ℂ)) hζ
      simpa using this
    have hn : ‖(ζ : ℂ)‖ = 1 :=
      Complex.norm_eq_one_of_pow_eq_one hpow (orderOf_pos c).ne'
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, hn]
    norm_num
  have hdeg : starRingEnd ℂ ((basis.representation ψ).character 1) =
      (basis.representation ψ).character 1 := by
    rw [FiniteComplexRepresentation.character, Representation.char_one, map_natCast]
  rw [hval, map_mul, hdeg]
  linear_combination (basis.representation ψ).character 1 ^ 2 * hnorm

theorem typeStar_rotation_columns (hn : 4 ≤ n) (ht : t = (fS (r n) : G) ^ 2 ^ (n - 2))
    (hindex : ∀ V : Subgroup G, V.index ≠ 2) (θ : C t →* ℂˣ)
    (hθS : ∀ c : C t, (c : G) ∈ (S : Subgroup G) → θ c = 1)
    (hθT : ∀ g ∈ Subgroup.normalizer
        ((Subgroup.closure {t, (fS (s n) : G)} : Subgroup G) : Set G),
      ∀ c c' : C t,
        (c : G) ∈ Subgroup.centralizer
          ((Subgroup.closure {t, (fS (s n) : G)} : Subgroup G) : Set G) →
        (c' : G) = g * c * g⁻¹ → θ c' = θ c)
    (basis : FiniteIrreducibleCharacterBasis G) (ideal : Ideal ComplexAlgebraicIntegers)
    [ideal.IsMaximal] [CharP (ComplexAlgebraicIntegers ⧸ ideal) 2]
    (normalizerBasis :
      FiniteIrreducibleCharacterBasis (Subgroup.normalizer ((S : Subgroup G) : Set G)))
    (lambdaLabel : normalizerBasis.index)
    (hlambda : ∀ (x : Subgroup.normalizer ((S : Subgroup G) : Set G)) (q : G)
      (c : Subgroup.centralizer ((S : Subgroup G) : Set G)), q ∈ (S : Subgroup G) →
        (x : G) = q * c → (normalizerBasis.representation lambdaLabel).character x =
          thetaG t θ (c : G))
    (B : basis.index)
    (hB : brauerNormalizerCharacterResidueHom ideal 2 (S : Subgroup G) S.isPGroup'
      (Subgroup.normalizer ((S : Subgroup G) : Set G)) (Subgroup.centralizer_le_normalizer _) le_rfl
        normalizerBasis lambdaLabel = centralCharacterResidueHom basis ideal B) :
    (∀ i j : ℤ, ¬ i ≡ 0 [ZMOD modulus n] → ¬ i ≡ (modulus n / 2 : ℕ) [ZMOD modulus n] →
      ¬ j ≡ 0 [ZMOD modulus n] → ¬ j ≡ (modulus n / 2 : ℕ) [ZMOD modulus n] →
      ∑ χ ∈ coefficientBlock basis (localizedComplexIntegerRing ideal) B,
          (basis.representation χ).character ((fS (r n) : G) ^ i) *
            starRingEnd ℂ ((basis.representation χ).character ((fS (r n) : G) ^ j)) =
        if j ≡ i [ZMOD modulus n] ∨ j ≡ (((modulus n / 2 : ℕ) : ℤ) - 1) * i [ZMOD modulus n]
        then (modulus n : ℂ) else 0) ∧
    (∀ i : ℤ, ¬ i ≡ 0 [ZMOD modulus n] → ¬ i ≡ (modulus n / 2 : ℕ) [ZMOD modulus n] →
      ∀ x : G, (∀ a c : G, a * c = x → Commute a c → (∃ k : ℕ, orderOf a = 2 ^ k) →
          Odd (orderOf c) → ¬ IsConj a ((fS (r n) : G) ^ i)) →
        ∑ χ ∈ coefficientBlock basis (localizedComplexIntegerRing ideal) B,
          (basis.representation χ).character ((fS (r n) : G) ^ i) *
            starRingEnd ℂ ((basis.representation χ).character x) = 0) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hu : ∀ i : ℤ, orderOf ((fS (r n) : G) ^ i) ∣ 2 ^ (n - 1) := fun i =>
    suppliedRotation_zpow_orderOf_dvd (by omega) fS i
  have horth : ∀ (i : ℤ) (a c : G) (k : ℕ), orderOf a ∣ 2 ^ k → Nat.Coprime 2 (orderOf c) →
      Commute a c → ¬ IsConj ((fS (r n) : G) ^ i) a →
      ∑ χ ∈ coefficientBlock basis (localizedComplexIntegerRing ideal) B,
          (basis.representation χ).character ((fS (r n) : G) ^ i) *
            starRingEnd ℂ ((basis.representation χ).character (a * c)) = 0 := by
    intro i a c k ha hc hac hnot
    have h1 : Nat.Coprime 2 (orderOf (1 : G)) := by
      rw [orderOf_one]; exact Nat.coprime_one_right 2
    have h := coefficientBlock_section_column_orthogonality basis ideal 2 B
      ((fS (r n) : G) ^ i) a 1 c (n - 1) k (hu i) ha h1 hc (Commute.one_right _) hac hnot
    rw [mul_one] at h
    rw [← h]
    refine Finset.sum_congr rfl fun χ _ => ?_
    rw [finite_character_conjugate_inverse]
  have hnorm : ∀ i : ℤ, ¬ i ≡ 0 [ZMOD modulus n] → ¬ i ≡ (modulus n / 2 : ℕ) [ZMOD modulus n] →
      ∑ χ ∈ coefficientBlock basis (localizedComplexIntegerRing ideal) B,
          (basis.representation χ).character ((fS (r n) : G) ^ i) *
            starRingEnd ℂ ((basis.representation χ).character ((fS (r n) : G) ^ i)) =
        (modulus n : ℂ) := by
    intro i hi0 hi1
    set u : G := (fS (r n) : G) ^ i with hudef
    have hu2 : IsPGroup 2 (Subgroup.zpowers u) := by
      obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp (hu i)
      exact IsPGroup.of_card (n := k) (by rw [Nat.card_zpowers, hk])
    have htu := t_mem_zpowers_rotation fS hn ht i hi0
    have huC : u ∈ C t := by
      apply sylow_le_C fS hn ht
      rw [hudef]
      exact Subgroup.zpow_mem _ (fS (r n)).2 i
    obtain ⟨localBasis⟩ := finiteIrreducibleCharacterBasis_exists
      (G := Subgroup.centralizer (Subgroup.zpowers u : Set G))
    obtain ⟨ψLabel, -, hbr, huniq, hβ⟩ := typeStar_local_block fS hn ht hindex θ hθS hθT basis
      ideal normalizerBasis lambdaLabel hlambda B hB hu2 htu huC localBasis
    obtain ⟨e₀, he₀⟩ : ∃ e₀ : ℕ, orderOf u ∣ 2 ^ e₀ := ⟨n - 1, hu i⟩
    have hkernel := unique_local_block_section_kernel basis ideal 2 u e₀ he₀ hu2 localBasis B
      ψLabel hbr huniq (centralizerSelf u) (centralizerSelf u)
      ⟨1, by rw [mul_one], by rw [orderOf_one]; exact Nat.coprime_one_right 2⟩
      ⟨1, by rw [mul_one], by rw [orderOf_one]; exact Nat.coprime_one_right 2⟩
    change ∑ χ ∈ coefficientBlock basis (localizedComplexIntegerRing ideal) B,
        (basis.representation χ).character ((centralizerSelf u : _) : G) *
          starRingEnd ℂ ((basis.representation χ).character ((centralizerSelf u : _) : G)) = _
    rw [hkernel, hβ, linearTwistedBlock,
      Finset.sum_image (fun x _ y _ hxy => (linearTwistLabelEquiv localBasis _).injective hxy)]
    have hlam1 : (family t θ (Subgroup.zpowers u) (centralizerSelf u) : ℂ) = 1 := by
      rw [family_apply_special fS hn ht θ hθT (special_zpowers htu huC)]
      change ((thetaG t θ u : ℂˣ) : ℂ) = 1
      rw [thetaG_eq_one_of_isPGroup fS hn ht θ hθS huC hu2, Units.val_one]
    have hterm : ∀ ψ₀, (localBasis.representation (linearTwistLabelEquiv localBasis
        (family t θ (Subgroup.zpowers u)) ψ₀)).character (centralizerSelf u) *
        starRingEnd ℂ ((localBasis.representation (linearTwistLabelEquiv localBasis
          (family t θ (Subgroup.zpowers u)) ψ₀)).character (centralizerSelf u)) =
        (localBasis.representation ψ₀).character 1 ^ 2 := by
      intro ψ₀
      rw [linearTwistLabelEquiv_character, hlam1, one_mul]
      exact central_character_mul_conj localBasis ψ₀ (centralizerSelf_mem_center u)
    rw [Finset.sum_congr rfl fun ψ₀ _ => hterm ψ₀]
    obtain ⟨R, hRn, hR, hquot, -, hcard⟩ := noncentralRotation_section_data hn fS i hi0 hi1
    rw [principal_block_degree_square_sum_of_normal_complement localBasis ideal 2
      (principalCharacterLabel localBasis) (principalCharacterLabel_character localBasis) R hR
      hquot, hcard]
  have hnot2 : ∀ (i : ℤ), ¬ i ≡ 0 [ZMOD modulus n] →
      ¬ i ≡ (modulus n / 2 : ℕ) [ZMOD modulus n] → ∀ a : G, a ^ 2 = 1 →
        ¬ IsConj ((fS (r n) : G) ^ i) a := by
    intro i hi0 hi1 a ha hconj
    obtain ⟨g, hg⟩ := isConj_iff.mp hconj
    apply noncentralRotation_sq_ne_one (by omega) fS i hi0 hi1
    have : (g * (fS (r n) : G) ^ i * g⁻¹) ^ 2 = 1 := by rw [hg]; exact ha
    rw [conj_pow] at this
    have h2 := congrArg (fun x => g⁻¹ * x * g) this
    simpa [mul_assoc] using h2
  refine ⟨?_, ?_⟩
  ·
    intro i j hi0 hi1 hj0 hj1
    split_ifs with hij
    · have hconj : IsConj ((fS (r n) : G) ^ i) ((fS (r n) : G) ^ j) :=
        (noncentralRotation_isConj_iff hn fS i j hj0 hj1).mpr hij
      have hval : ∀ χ : basis.index, (basis.representation χ).character ((fS (r n) : G) ^ j) =
          (basis.representation χ).character ((fS (r n) : G) ^ i) := by
        intro χ
        obtain ⟨g, hg⟩ := isConj_iff.mp hconj
        rw [← hg]
        exact Representation.char_conj _ _ _
      simp only [hval]
      exact hnorm i hi0 hi1
    · have hnot : ¬ IsConj ((fS (r n) : G) ^ i) ((fS (r n) : G) ^ j) := fun h =>
        hij ((noncentralRotation_isConj_iff hn fS i j hj0 hj1).mp h)
      have h := horth i ((fS (r n) : G) ^ j) 1 (n - 1) (hu j)
        (by rw [orderOf_one]; exact Nat.coprime_one_right 2) (Commute.one_right _) hnot
      simpa only [mul_one] using h
  ·
    intro i hi0 hi1 x hx
    obtain ⟨a, c, k, -, -, hac, hacx, ha, hc⟩ := finite_prime_primary_factorization x 2
      Nat.prime_two
    have hnot : ¬ IsConj ((fS (r n) : G) ^ i) a := fun h => hx a c hacx hac (by
      obtain ⟨m, -, hm⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp ha
      exact ⟨m, hm⟩) (Nat.coprime_two_left.mp hc) h.symm
    rw [← hacx]
    exact horth i a c k ha hc hac hnot

end CFSG.Semidihedral.FieldFactorOne

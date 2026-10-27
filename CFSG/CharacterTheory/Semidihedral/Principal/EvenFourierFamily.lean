module

public import CFSG.CharacterTheory.Semidihedral.Principal.FourierSupport
public import CFSG.CharacterTheory.Semidihedral.Principal.DegreeZeroGram

public section

open scoped BigOperators Classical

namespace CFSG.Semidihedral.Principal

open CFSG.TwoRankLowerBound.Helpers CFSG.RankTwoShapes CFSG.Open

variable {G : Type*} [Group G] [Fintype G] {n : ℕ} {S : Sylow 2 G}

theorem characterPairing_finset_expansion_left {H : Type*} [Group H] [Fintype H] {ι : Type*}
    (B : Finset ι) (k : ι → ℂ) (χ : ι → H → ℂ) (f : H → ℂ) :
    characterPairing (fun x => ∑ i ∈ B, k i * χ i x) f =
      ∑ i ∈ B, k i * characterPairing (χ i) f := by
  unfold characterPairing
  simp only [Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun x _ => ?_
  ring

theorem principalCyclicProjection_coefficient_gram (basis : FiniteIrreducibleCharacterBasis G)
    (B : Finset basis.index) (ρ : G) (h h' : Subgroup.zpowers ρ → ℂ) :
    ∑ χ ∈ B, characterPairing
        (fun x : Subgroup.zpowers ρ => (basis.representation χ).character x) h *
      characterPairing (fun x : Subgroup.zpowers ρ => (basis.representation χ).character x) h' =
    characterPairing (fun x : Subgroup.zpowers ρ => principalCyclicProjection basis B ρ h x)
      h' := by
  unfold principalCyclicProjection
  rw [characterPairing_finset_expansion_left]

theorem characterPairing_zpowers_eq_sum_range {H : Type*} [Group H] [Fintype H] {g : H} {M : ℕ}
    (hg : orderOf g = M) (F F' : Subgroup.zpowers g → ℂ) :
    characterPairing F F' = (M : ℂ)⁻¹ * ∑ v ∈ Finset.range M,
      F ⟨g ^ (v : ℤ), Subgroup.zpow_mem_zpowers g _⟩ *
        F' ⟨g ^ (-(v : ℤ)), Subgroup.zpow_mem_zpowers g _⟩ := by
  have hfin : IsOfFinOrder g := isOfFinOrder_of_finite g
  unfold characterPairing
  rw [Nat.card_zpowers, hg]
  congr 1
  rw [← Equiv.sum_comp (finEquivZPowers hfin)]
  subst hg
  rw [← Fin.sum_univ_eq_sum_range (fun v => F ⟨g ^ (v : ℤ), Subgroup.zpow_mem_zpowers g _⟩ *
        F' ⟨g ^ (-(v : ℤ)), Subgroup.zpow_mem_zpowers g _⟩)]
  refine Fintype.sum_congr _ _ fun i => ?_
  rw [finEquivZPowers_apply]
  have h1 : (⟨g ^ (i : ℕ), Subgroup.npow_mem_zpowers g i⟩ : Subgroup.zpowers g) =
      ⟨g ^ ((i : ℕ) : ℤ), Subgroup.zpow_mem_zpowers g _⟩ := Subtype.ext (by simp)
  have h2 : (⟨g ^ (i : ℕ), Subgroup.npow_mem_zpowers g i⟩ : Subgroup.zpowers g)⁻¹ =
      ⟨g ^ (-((i : ℕ) : ℤ)), Subgroup.zpow_mem_zpowers g _⟩ := Subtype.ext (by simp [zpow_neg])
  rw [h2, h1]

omit [Fintype G] in
theorem suppliedRotation_half_orderOf (hn : 4 ≤ n) (e : SemidihedralGroup n ≃* (S : Subgroup G)) :
    orderOf ((e (r n) : G) ^ (modulus n / 2)) = 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hord := suppliedRotation_orderOf (by omega) e
  have h2 : 2 * (modulus n / 2) = modulus n := by
    unfold modulus; rw [show n - 1 = (n - 2) + 1 by omega, pow_succ]; omega
  obtain ⟨hM, -, hK2, -⟩ := modulus_eq_four_mul hn
  apply orderOf_eq_prime
  · rw [← pow_mul, mul_comm, h2, ← hord, pow_orderOf_eq_one]
  · apply pow_ne_one_of_lt_orderOf
    · omega
    · rw [hord]; omega

theorem principalCyclicProjection_rotation_value (hn : 4 ≤ n)
    (e : SemidihedralGroup n ≃* (S : Subgroup G)) (basis : FiniteIrreducibleCharacterBasis G)
    (ideal : Ideal ComplexAlgebraicIntegers) [ideal.IsMaximal]
    [CharP (ComplexAlgebraicIntegers ⧸ ideal) 2] (principal : basis.index)
    (hprincipal : (basis.representation principal).character = 1)
    {f : Subgroup.zpowers (e (r n) : G) → ℂ} (h1 : f 1 = 0)
    (ht : f ⟨(e (r n) : G) ^ (modulus n / 2), Subgroup.npow_mem_zpowers _ _⟩ = 0) (v : ℤ) :
    principalCyclicProjection basis (coefficientBlock basis (localizedComplexIntegerRing ideal)
        principal) (e (r n) : G) f ((e (r n) : G) ^ v) =
      f ⟨(e (r n) : G) ^ v, Subgroup.zpow_mem_zpowers _ _⟩ +
        f ⟨(e (r n) : G) ^ ((((modulus n / 2 : ℕ) : ℤ) - 1) * v),
          Subgroup.zpow_mem_zpowers _ _⟩ := by
  have hcols := noncentral_rotation_principal_section_columns hn e basis ideal principal hprincipal
  by_cases hv0 : v ≡ 0 [ZMOD modulus n]
  · have hav : (((modulus n / 2 : ℕ) : ℤ) - 1) * v ≡ 0 [ZMOD modulus n] := by
      simpa using hv0.mul_left ((((modulus n / 2 : ℕ) : ℤ) - 1))
    have hx : ∀ w : ℤ, w ≡ 0 [ZMOD modulus n] →
        (⟨(e (r n) : G) ^ w, Subgroup.zpow_mem_zpowers _ _⟩ : Subgroup.zpowers (e (r n) : G)) =
          1 := fun w hw => Subtype.ext (by
      show (e (r n) : G) ^ w = 1
      rw [← zpow_zero (e (r n) : G), suppliedRotation_zpow_eq_iff (by omega) e]
      exact hw)
    rw [hx v hv0, hx _ hav, h1, add_zero]
    have hg : (e (r n) : G) ^ v = 1 := congrArg Subtype.val (hx v hv0)
    rw [hg]
    refine principalCyclicProjection_eq_zero_of_inv_columns hn e basis _ h1 ht fun w hw0 hw1 => ?_
    exact hcols.2.2.2.1 w hw0 hw1 _ (by rw [inv_one, orderOf_one]; exact odd_one)
  by_cases hv1 : v ≡ (modulus n / 2 : ℕ) [ZMOD modulus n]
  · have hav : (((modulus n / 2 : ℕ) : ℤ) - 1) * v ≡ (modulus n / 2 : ℕ) [ZMOD modulus n] := by
      have h := hv1.mul_left ((((modulus n / 2 : ℕ) : ℤ) - 1))
      refine h.trans ?_
      have hsq := twist_sq_modEq hn
      have h2 : (modulus n : ℤ) = 2 * ((modulus n / 2 : ℕ) : ℤ) := by
        have : 2 ∣ modulus n := by unfold modulus; exact dvd_pow_self 2 (by omega)
        omega
      rw [Int.modEq_iff_dvd]
      obtain ⟨K, -, hK2, -⟩ := modulus_eq_four_mul hn
      refine ⟨1 - ((modulus n / 4 : ℕ) : ℤ), ?_⟩
      have h4 : (modulus n : ℤ) = 4 * ((modulus n / 4 : ℕ) : ℤ) := by
        have : 4 ∣ modulus n := ⟨2 ^ (n - 3), K⟩
        omega
      have h2' : ((modulus n / 2 : ℕ) : ℤ) = 2 * ((modulus n / 4 : ℕ) : ℤ) := by omega
      rw [h2', h4]
      ring
    have hx : ∀ w : ℤ, w ≡ (modulus n / 2 : ℕ) [ZMOD modulus n] →
        (⟨(e (r n) : G) ^ w, Subgroup.zpow_mem_zpowers _ _⟩ : Subgroup.zpowers (e (r n) : G)) =
          ⟨(e (r n) : G) ^ (modulus n / 2), Subgroup.npow_mem_zpowers _ _⟩ :=
      fun w hw => Subtype.ext (by
        show (e (r n) : G) ^ w = (e (r n) : G) ^ (modulus n / 2)
        rw [← zpow_natCast, suppliedRotation_zpow_eq_iff (by omega) e]
        exact hw)
    rw [hx v hv1, hx _ hav, ht, add_zero]
    have hg : (e (r n) : G) ^ v = (e (r n) : G) ^ (modulus n / 2) := congrArg Subtype.val (hx v hv1)
    rw [hg]
    have hord := suppliedRotation_half_orderOf hn e
    refine principalCyclicProjection_eq_zero_of_inv_columns hn e basis _ h1 ht fun w hw0 hw1 => ?_
    exact hcols.2.2.2.2 w hw0 hw1 _ _ 1 (mul_one _) (Commute.one_right _)
      (by rw [orderOf_inv, hord]) (by rw [orderOf_one]; exact odd_one)
  · exact principalCyclicProjection_section_value hn e basis ideal principal hprincipal h1 ht hv0
      hv1 (mul_one _) (Commute.one_right _) (by rw [orderOf_one]; exact odd_one) (IsConj.refl _)


theorem characterPairing_sub_right' {H : Type*} [Group H] [Fintype H] (F f g : H → ℂ) :
    characterPairing F (fun x => f x - g x) = characterPairing F f - characterPairing F g := by
  unfold characterPairing
  simp only [mul_sub, Finset.sum_sub_distrib]

omit [Fintype G] in
theorem cyclicLinearCharacter_half (hn : 4 ≤ n) (e : SemidihedralGroup n ≃* (S : Subgroup G))
    (j : ℤ) : cyclicLinearCharacter (e (r n) : G) (modulus n) j
      ⟨(e (r n) : G) ^ (modulus n / 2), Subgroup.npow_mem_zpowers _ _⟩ = (-1 : ℂ) ^ j := by
  have hord := suppliedRotation_orderOf (by omega) e
  have h := cyclicLinearCharacter_zpow hord j ((modulus n / 2 : ℕ) : ℤ)
  rw [show (⟨(e (r n) : G) ^ (((modulus n / 2 : ℕ) : ℤ)), Subgroup.zpow_mem_zpowers _ _⟩ :
      Subgroup.zpowers (e (r n) : G)) =
      ⟨(e (r n) : G) ^ (modulus n / 2), Subgroup.npow_mem_zpowers _ _⟩ from
      Subtype.ext (zpow_natCast _ _)] at h
  rw [h, mul_comm, zpow_mul, cyclicRoot_zpow_half hn]

theorem principalCyclicProjection_gram_sum (hn : 4 ≤ n)
    (e : SemidihedralGroup n ≃* (S : Subgroup G)) (basis : FiniteIrreducibleCharacterBasis G)
    (ideal : Ideal ComplexAlgebraicIntegers) [ideal.IsMaximal]
    [CharP (ComplexAlgebraicIntegers ⧸ ideal) 2] (principal : basis.index)
    (hprincipal : (basis.representation principal).character = 1)
    {f : Subgroup.zpowers (e (r n) : G) → ℂ} (h1 : f 1 = 0)
    (ht : f ⟨(e (r n) : G) ^ (modulus n / 2), Subgroup.npow_mem_zpowers _ _⟩ = 0)
    (f' : Subgroup.zpowers (e (r n) : G) → ℂ) :
    ∑ χ ∈ coefficientBlock basis (localizedComplexIntegerRing ideal) principal,
        characterPairing (fun x : Subgroup.zpowers (e (r n) : G) =>
          (basis.representation χ).character x) f *
        characterPairing (fun x : Subgroup.zpowers (e (r n) : G) =>
          (basis.representation χ).character x) f' =
      (modulus n : ℂ)⁻¹ * ∑ v ∈ Finset.range (modulus n),
        (f ⟨(e (r n) : G) ^ (v : ℤ), Subgroup.zpow_mem_zpowers _ _⟩ +
          f ⟨(e (r n) : G) ^ ((((modulus n / 2 : ℕ) : ℤ) - 1) * (v : ℤ)),
            Subgroup.zpow_mem_zpowers _ _⟩) *
        f' ⟨(e (r n) : G) ^ (-(v : ℤ)), Subgroup.zpow_mem_zpowers _ _⟩ := by
  rw [principalCyclicProjection_coefficient_gram,
    characterPairing_zpowers_eq_sum_range (suppliedRotation_orderOf (by omega) e)]
  congr 1
  refine Finset.sum_congr rfl fun v _ => ?_
  rw [principalCyclicProjection_rotation_value hn e basis ideal principal hprincipal h1 ht]

theorem cyclicRoot_zpow_mul_neg (M : ℕ) (x y v : ℤ) :
    cyclicRoot M ^ (x * v) * cyclicRoot M ^ (y * -v) = cyclicRoot M ^ ((x - y) * v) := by
  rw [← zpow_add₀ (cyclicRoot_ne_zero M)]
  congr 1
  ring

theorem cyclicRoot_average (M : ℕ) (hM : 0 < M) (x y : ℤ) :
    (M : ℂ)⁻¹ * ∑ v ∈ Finset.range M, cyclicRoot M ^ ((x - y) * (v : ℤ)) =
      if (M : ℤ) ∣ x - y then 1 else 0 := by
  rw [sum_range_cyclicRoot_zpow hM]
  have hM0 : (M : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hM.ne'
  split_ifs
  · field_simp
  · rw [mul_zero]

@[expose] def residueIndicator (M : ℕ) (x y : ℤ) : ℤ := if (M : ℤ) ∣ x - y then 1 else 0

theorem residueIndicator_congr_left {M : ℕ} {x x' : ℤ} (y : ℤ) (h : x ≡ x' [ZMOD M]) :
    residueIndicator M x y = residueIndicator M x' y := by
  unfold residueIndicator
  have : (M : ℤ) ∣ x - y ↔ (M : ℤ) ∣ x' - y := by
    have hd := (Int.modEq_iff_dvd.mp h)
    constructor
    · intro hxy
      have := dvd_add hxy hd
      rwa [show x - y + (x' - x) = x' - y by ring] at this
    · intro hxy
      have := dvd_sub hxy hd
      rwa [show x' - y - (x' - x) = x - y by ring] at this
  simp only [this]

theorem characterPairing_linear_difference (hn : 4 ≤ n)
    (e : SemidihedralGroup n ≃* (S : Subgroup G)) (basis : FiniteIrreducibleCharacterBasis G)
    (p q : ℤ) (χ : basis.index) :
    characterPairing
        (fun x : Subgroup.zpowers (e (r n) : G) => (basis.representation χ).character x)
        (fun x => cyclicLinearCharacter (e (r n) : G) (modulus n) p x -
          cyclicLinearCharacter (e (r n) : G) (modulus n) q x) =
      ((multiplicityColumn basis (e (r n) : G) (modulus n) p χ -
        multiplicityColumn basis (e (r n) : G) (modulus n) q χ : ℤ) : ℂ) := by
  have hord := suppliedRotation_orderOf (by omega) e
  have hM : 0 < modulus n := by unfold modulus; positivity
  have hr : (e (r n) : G) ^ modulus n = 1 := by rw [← hord]; exact pow_orderOf_eq_one _
  rw [characterPairing_sub_right', characterPairing_zpowers_cyclicLinearCharacter _ hord,
    characterPairing_zpowers_cyclicLinearCharacter _ hord, Int.cast_sub,
    multiplicityColumn_cast basis hM hr, multiplicityColumn_cast basis hM hr]

theorem multiplicityColumn_difference_gram (hn : 4 ≤ n)
    (e : SemidihedralGroup n ≃* (S : Subgroup G)) (basis : FiniteIrreducibleCharacterBasis G)
    (ideal : Ideal ComplexAlgebraicIntegers) [ideal.IsMaximal]
    [CharP (ComplexAlgebraicIntegers ⧸ ideal) 2] (principal : basis.index)
    (hprincipal : (basis.representation principal).character = 1) (p q p' q' : ℤ)
    (hpq : Even (p - q)) :
    ∑ χ ∈ coefficientBlock basis (localizedComplexIntegerRing ideal) principal,
        (multiplicityColumn basis (e (r n) : G) (modulus n) p χ -
          multiplicityColumn basis (e (r n) : G) (modulus n) q χ) *
        (multiplicityColumn basis (e (r n) : G) (modulus n) p' χ -
          multiplicityColumn basis (e (r n) : G) (modulus n) q' χ) =
      residueIndicator (modulus n) p p' - residueIndicator (modulus n) p q' -
        residueIndicator (modulus n) q p' + residueIndicator (modulus n) q q' +
        residueIndicator (modulus n) ((((modulus n / 2 : ℕ) : ℤ) - 1) * p) p' -
        residueIndicator (modulus n) ((((modulus n / 2 : ℕ) : ℤ) - 1) * p) q' -
        residueIndicator (modulus n) ((((modulus n / 2 : ℕ) : ℤ) - 1) * q) p' +
        residueIndicator (modulus n) ((((modulus n / 2 : ℕ) : ℤ) - 1) * q) q' := by
  have hord := suppliedRotation_orderOf (by omega) e
  have hM : 0 < modulus n := by unfold modulus; positivity
  set a : ℤ := ((modulus n / 2 : ℕ) : ℤ) - 1 with ha
  set ζ := cyclicRoot (modulus n) with hζ
  have hlam : ∀ j k : ℤ, cyclicLinearCharacter (e (r n) : G) (modulus n) j
      ⟨(e (r n) : G) ^ k, Subgroup.zpow_mem_zpowers _ _⟩ = ζ ^ (j * k) := fun j k =>
    cyclicLinearCharacter_zpow hord j k
  have h1 : (fun x => cyclicLinearCharacter (e (r n) : G) (modulus n) p x -
      cyclicLinearCharacter (e (r n) : G) (modulus n) q x) (1 : Subgroup.zpowers (e (r n) : G)) =
      0 := by
    simp only [cyclicLinearCharacter_one hord, sub_self]
  have ht : (fun x => cyclicLinearCharacter (e (r n) : G) (modulus n) p x -
      cyclicLinearCharacter (e (r n) : G) (modulus n) q x)
      ⟨(e (r n) : G) ^ (modulus n / 2), Subgroup.npow_mem_zpowers _ _⟩ = 0 := by
    simp only [cyclicLinearCharacter_half hn e]
    obtain ⟨k, hk⟩ := hpq
    rw [show p = q + (k + k) by omega, zpow_add₀ (by norm_num), ← two_mul, zpow_mul]
    norm_num
  apply Int.cast_injective (α := ℂ)
  simp only [Int.cast_sum, Int.cast_mul, Int.cast_sub, Int.cast_add]
  have hgram := principalCyclicProjection_gram_sum hn e basis ideal principal hprincipal
    (f := fun x => cyclicLinearCharacter (e (r n) : G) (modulus n) p x -
      cyclicLinearCharacter (e (r n) : G) (modulus n) q x) h1 ht
    (fun x => cyclicLinearCharacter (e (r n) : G) (modulus n) p' x -
      cyclicLinearCharacter (e (r n) : G) (modulus n) q' x)
  simp only [characterPairing_linear_difference hn e basis, Int.cast_sub] at hgram
  rw [hgram]
  simp only [hlam]
  have hexp : ∀ v : ℕ, (ζ ^ (p * (v : ℤ)) - ζ ^ (q * (v : ℤ)) +
      (ζ ^ (p * (a * (v : ℤ))) - ζ ^ (q * (a * (v : ℤ))))) *
      (ζ ^ (p' * -(v : ℤ)) - ζ ^ (q' * -(v : ℤ))) =
      ζ ^ ((p - p') * (v : ℤ)) - ζ ^ ((p - q') * (v : ℤ)) - ζ ^ ((q - p') * (v : ℤ)) +
        ζ ^ ((q - q') * (v : ℤ)) + ζ ^ ((a * p - p') * (v : ℤ)) -
        ζ ^ ((a * p - q') * (v : ℤ)) - ζ ^ ((a * q - p') * (v : ℤ)) +
        ζ ^ ((a * q - q') * (v : ℤ)) := by
    intro v
    rw [show p * (a * (v : ℤ)) = (a * p) * v by ring, show q * (a * (v : ℤ)) = (a * q) * v by ring]
    simp only [add_mul, sub_mul, mul_sub, hζ, cyclicRoot_zpow_mul_neg]
    ring
  rw [Finset.sum_congr rfl fun v _ => hexp v]
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, mul_add, mul_sub, hζ,
    cyclicRoot_average _ hM, residueIndicator]
  simp only [apply_ite (Int.cast : ℤ → ℂ), Int.cast_one, Int.cast_zero]

theorem residueIndicator_self (M : ℕ) (x : ℤ) : residueIndicator M x x = 1 := by
  simp [residueIndicator]

theorem residueIndicator_eq_zero_of_abs_lt {M : ℕ} {x y : ℤ} (hne : x ≠ y)
    (hlt : |x - y| < M) : residueIndicator M x y = 0 := by
  unfold residueIndicator
  refine ite_eq_right fun hd => hne (sub_eq_zero.mp (Int.eq_zero_of_abs_lt_dvd hd hlt))

theorem residueIndicator_eq_zmod (M : ℕ) (x y : ℤ) :
    residueIndicator M x y = if (x : ZMod M) = (y : ZMod M) then 1 else 0 := by
  unfold residueIndicator
  have h : (M : ℤ) ∣ x - y ↔ (x : ZMod M) = (y : ZMod M) := by
    rw [eq_comm, ZMod.intCast_eq_intCast_iff_dvd_sub]
  simp only [h]

theorem residueIndicator_eq_zero_of_odd_sub {M : ℕ} (hM : Even M) {x y : ℤ} (hxy : Odd (x - y)) :
    residueIndicator M x y = 0 := by
  unfold residueIndicator
  refine ite_eq_right fun hd => ?_
  obtain ⟨m, hm⟩ := hM
  have h2 : (2 : ℤ) ∣ x - y := (Dvd.intro (m : ℤ) (by omega)).trans hd
  exact (Int.not_even_iff_odd.mpr hxy) (even_iff_two_dvd.mpr h2)

theorem multiplicityColumn_principal (hn : 4 ≤ n) (e : SemidihedralGroup n ≃* (S : Subgroup G))
    (basis : FiniteIrreducibleCharacterBasis G) {principal : basis.index}
    (hprincipal : (basis.representation principal).character = 1) (j : ℤ) :
    multiplicityColumn basis (e (r n) : G) (modulus n) j principal =
      if (modulus n : ℤ) ∣ j then 1 else 0 := by
  have hord := suppliedRotation_orderOf (by omega) e
  have hM : 0 < modulus n := by unfold modulus; positivity
  have hr : (e (r n) : G) ^ modulus n = 1 := by rw [← hord]; exact pow_orderOf_eq_one _
  apply Int.cast_injective (α := ℂ)
  rw [multiplicityColumn_cast basis hM hr, cyclicMultiplicity, hprincipal]
  have hsum : ∑ v ∈ Finset.range (modulus n), (1 : G → ℂ) ((e (r n) : G) ^ v) *
      cyclicRoot (modulus n) ^ (-(j * (v : ℤ))) =
      ∑ v ∈ Finset.range (modulus n), cyclicRoot (modulus n) ^ ((-j) * (v : ℤ)) :=
    Finset.sum_congr rfl fun v _ => by rw [Pi.one_apply, one_mul, neg_mul]
  rw [hsum, sum_range_cyclicRoot_zpow hM]
  have hM0 : (modulus n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hM.ne'
  by_cases hj : (modulus n : ℤ) ∣ j
  · rw [ite_eq_left (dvd_neg.mpr hj), ite_eq_left hj, Int.cast_one]
    field_simp
  · rw [ite_eq_right (fun h => hj (dvd_neg.mp h)), ite_eq_right hj, Int.cast_zero, mul_zero]

theorem characterPairing_finset_expansion_right {H : Type*} [Group H] [Fintype H] {ι : Type*}
    (B : Finset ι) (k : ι → ℂ) (χ : ι → H → ℂ) (f : H → ℂ) :
    characterPairing f (fun x => ∑ i ∈ B, k i * χ i x) =
      ∑ i ∈ B, k i * characterPairing f (χ i) := by
  unfold characterPairing
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun x _ => ?_
  ring

theorem characterPairing_basis (basis : FiniteIrreducibleCharacterBasis G) (c d : basis.index) :
    characterPairing (basis.representation c).character (basis.representation d).character =
      if c = d then 1 else 0 := by
  rw [characterPairing_irreducible _ _ (basis.irreducible c) (basis.irreducible d)]
  simp only [basis.distinct.eq_iff]

theorem characterPairing_basis_combination (basis : FiniteIrreducibleCharacterBasis G)
    (B : Finset basis.index) (k k' : basis.index → ℂ) :
    characterPairing (fun g => ∑ c ∈ B, k c * (basis.representation c).character g)
        (fun g => ∑ c ∈ B, k' c * (basis.representation c).character g) =
      ∑ c ∈ B, k c * k' c := by
  rw [characterPairing_finset_expansion_left]
  refine Finset.sum_congr rfl fun c hc => ?_
  rw [characterPairing_finset_expansion_right]
  simp only [characterPairing_basis, mul_ite, mul_one, mul_zero]
  rw [Finset.sum_ite_eq B c, ite_eq_left hc]

theorem characterPairing_basis_combination_one (basis : FiniteIrreducibleCharacterBasis G)
    {B : Finset basis.index} {principal : basis.index}
    (hprincipal : (basis.representation principal).character = 1) (hB : principal ∈ B)
    (k : basis.index → ℂ) :
    characterPairing (fun g => ∑ c ∈ B, k c * (basis.representation c).character g) 1 =
      k principal := by
  rw [characterPairing_finset_expansion_left, ← hprincipal]
  simp only [characterPairing_basis, mul_ite, mul_one, mul_zero]
  rw [Finset.sum_ite_eq' B principal, ite_eq_left hB]

theorem basis_combination_coefficient (basis : FiniteIrreducibleCharacterBasis G)
    {B : Finset basis.index} {c : basis.index} (hc : c ∈ B) (k : basis.index → ℂ) :
    characterPairing (fun g => ∑ d ∈ B, k d * (basis.representation d).character g)
      (basis.representation c).character = k c := by
  rw [characterPairing_finset_expansion_left]
  simp only [characterPairing_basis, mul_ite, mul_one, mul_zero]
  rw [Finset.sum_ite_eq' B c, ite_eq_left hc]

theorem basis_character_one (basis : FiniteIrreducibleCharacterBasis G) (c : basis.index) :
    (basis.representation c).character 1 =
        (Module.finrank ℂ (basis.representation c).vector : ℂ) ∧
      0 < Module.finrank ℂ (basis.representation c).vector := by
  have h1 : (basis.representation c).character 1 =
      (Module.finrank ℂ (basis.representation c).vector : ℂ) := by
    rw [FiniteComplexRepresentation.character, Representation.char_one]
  refine ⟨h1, Nat.pos_of_ne_zero fun h0 => ?_⟩
  apply irreducible_character_degree_ne_zero _ (basis.irreducible c)
  rw [h1, h0, Nat.cast_zero]

theorem even_family_coefficient_gram (hn : 4 ≤ n)
    (e : SemidihedralGroup n ≃* (S : Subgroup G)) (basis : FiniteIrreducibleCharacterBasis G)
    (ideal : Ideal ComplexAlgebraicIntegers) [ideal.IsMaximal]
    [CharP (ComplexAlgebraicIntegers ⧸ ideal) 2] (principal : basis.index)
    (hprincipal : (basis.representation principal).character = 1) :
    let B := coefficientBlock basis (localizedComplexIntegerRing ideal) principal
    let L := multiplicityColumn basis (e (r n) : G) (modulus n)
    let θ : basis.index → ℤ := fun c => L 0 c - L ((modulus n / 2 : ℕ) : ℤ) c
    let η : ℕ → basis.index → ℤ := fun l c => L 0 c - L (2 * l) c
    ∑ c ∈ B, θ c * θ c = 4 ∧
    (∀ l : ℕ, 1 ≤ l → l ≤ modulus n / 4 - 1 → ∑ c ∈ B, θ c * η l c = 2) ∧
    (∀ j l : ℕ, 1 ≤ j → j ≤ modulus n / 4 - 1 → 1 ≤ l → l ≤ modulus n / 4 - 1 →
      ∑ c ∈ B, η j c * η l c = 2 + if j = l then 1 else 0) := by
  intro B L θ η
  obtain ⟨hM, -, hK2, -⟩ := modulus_eq_four_mul hn
  set K : ℕ := 2 ^ (n - 3) with hK
  set h : ℤ := ((modulus n / 2 : ℕ) : ℤ) with hh
  have hhK : h = 2 * (K : ℤ) := by rw [hh]; omega
  have hMK : (modulus n : ℤ) = 4 * (K : ℤ) := by rw [hM]; push_cast; ring
  have hquarter : modulus n / 4 = K := by omega
  have hgram := multiplicityColumn_difference_gram hn e basis ideal principal hprincipal
  have e00 : residueIndicator (modulus n) 0 0 = 1 := residueIndicator_self _ _
  have e0h : residueIndicator (modulus n) 0 h = 0 :=
    residueIndicator_eq_zero_of_abs_lt (by omega) (by rw [abs_lt]; constructor <;> omega)
  have eh0 : residueIndicator (modulus n) h 0 = 0 :=
    residueIndicator_eq_zero_of_abs_lt (by omega) (by rw [abs_lt]; constructor <;> omega)
  have ehh : residueIndicator (modulus n) h h = 1 := residueIndicator_self _ _
  have eah : ∀ y, residueIndicator (modulus n) ((h - 1) * h) y = residueIndicator (modulus n) h y :=
    fun y => residueIndicator_congr_left y (by
      rw [Int.modEq_iff_dvd, hMK, hhK]
      exact ⟨1 - (K : ℤ), by ring⟩)
  have e2l : ∀ l : ℕ, 1 ≤ l → l ≤ modulus n / 4 - 1 →
      residueIndicator (modulus n) 0 (2 * l) = 0 ∧ residueIndicator (modulus n) (2 * l) 0 = 0 ∧
      residueIndicator (modulus n) h (2 * l) = 0 ∧
      (∀ y, residueIndicator (modulus n) ((h - 1) * (2 * l)) y =
        residueIndicator (modulus n) (-(2 * l)) y) ∧
      residueIndicator (modulus n) (-(2 * l)) 0 = 0 := by
    intro l hl1 hl2
    refine ⟨residueIndicator_eq_zero_of_abs_lt (by omega) (by rw [abs_lt]; constructor <;> omega),
      residueIndicator_eq_zero_of_abs_lt (by omega) (by rw [abs_lt]; constructor <;> omega),
      residueIndicator_eq_zero_of_abs_lt (by omega) (by rw [abs_lt]; constructor <;> omega),
      fun y => residueIndicator_congr_left y ?_,
      residueIndicator_eq_zero_of_abs_lt (by omega) (by rw [abs_lt]; constructor <;> omega)⟩
    rw [Int.modEq_iff_dvd, hMK, hhK]
    exact ⟨-(l : ℤ), by ring⟩
  have ejl : ∀ j l : ℕ, 1 ≤ j → j ≤ modulus n / 4 - 1 → 1 ≤ l → l ≤ modulus n / 4 - 1 →
      residueIndicator (modulus n) (2 * j) (2 * l) = (if j = l then 1 else 0) ∧
      residueIndicator (modulus n) (-(2 * j)) (2 * l) = 0 := by
    intro j l hj1 hj2 hl1 hl2
    refine ⟨?_, residueIndicator_eq_zero_of_abs_lt (by omega)
      (by rw [abs_lt]; constructor <;> omega)⟩
    by_cases hjl : j = l
    · rw [ite_eq_left hjl, hjl]
      exact residueIndicator_self _ _
    · rw [ite_eq_right hjl]
      exact residueIndicator_eq_zero_of_abs_lt (by omega) (by rw [abs_lt]; constructor <;> omega)
  refine ⟨?_, fun l hl1 hl2 => ?_, fun j l hj1 hj2 hl1 hl2 => ?_⟩
  · rw [hgram 0 h 0 h ⟨-(K : ℤ), by omega⟩, mul_zero, e00, e0h, eh0, ehh, eah, eah, eh0, ehh]
    norm_num
  · obtain ⟨a0l, al0, ahl, -, -⟩ := e2l l hl1 hl2
    rw [hgram 0 h 0 (2 * l) ⟨-(K : ℤ), by omega⟩, mul_zero, e00, a0l, eh0, ahl, eah, eah, eh0,
      ahl]
    norm_num
  · obtain ⟨a0l, -, -, -, -⟩ := e2l l hl1 hl2
    obtain ⟨-, aj0, -, ajt, ajn0⟩ := e2l j hj1 hj2
    obtain ⟨hjl, hnjl⟩ := ejl j l hj1 hj2 hl1 hl2
    rw [hgram 0 (2 * j) 0 (2 * l) ⟨-(j : ℤ), by omega⟩, mul_zero, e00, a0l, aj0, hjl, ajt, ajt,
      ajn0, hnjl]
    split_ifs <;> norm_num

omit [Fintype G] in
theorem cyclicLinearCharacter_zero (ρ : G) (M : ℕ) (x : Subgroup.zpowers ρ) :
    cyclicLinearCharacter ρ M 0 x = 1 := by
  simp [cyclicLinearCharacter]

theorem principalCyclicProjection_apply (basis : FiniteIrreducibleCharacterBasis G)
    (B : Finset basis.index) (ρ : G) (h : Subgroup.zpowers ρ → ℂ) (k : basis.index → ℤ)
    (hk : ∀ c, characterPairing (fun x : Subgroup.zpowers ρ => (basis.representation c).character x)
      h = k c) (g : G) :
    principalCyclicProjection basis B ρ h g =
      ∑ c ∈ B, (k c : ℂ) * (basis.representation c).character g := by
  unfold principalCyclicProjection
  exact Finset.sum_congr rfl fun c _ => by rw [hk c]

theorem basis_combination_one (basis : FiniteIrreducibleCharacterBasis G) (B : Finset basis.index)
    (k : basis.index → ℤ) :
    ∑ c ∈ B, (k c : ℂ) * (basis.representation c).character 1 =
      ((∑ c ∈ B, k c * (Module.finrank ℂ (basis.representation c).vector : ℤ) : ℤ) : ℂ) := by
  push_cast
  exact Finset.sum_congr rfl fun c _ => by rw [(basis_character_one basis c).1]

theorem basis_combination_three (basis : FiniteIrreducibleCharacterBasis G) {B : Finset basis.index}
    {p y s : basis.index} (hp : p ∈ B) (hy : y ∈ B) (hs : s ∈ B) (b c : ℤ) (g : G) :
    ∑ d ∈ B, ((((if d = p then 1 else 0) + b * (if d = y then 1 else 0) +
        c * (if d = s then 1 else 0) : ℤ)) : ℂ) * (basis.representation d).character g =
      (basis.representation p).character g + b * (basis.representation y).character g +
        c * (basis.representation s).character g := by
  push_cast
  simp only [add_mul, Finset.sum_add_distrib, mul_ite, mul_one, mul_zero, ite_mul, zero_mul,
    one_mul, Finset.sum_ite_eq', hp, hy, hs, ite_true]


theorem basis_combination_four (basis : FiniteIrreducibleCharacterBasis G) {B : Finset basis.index}
    {p y s w : basis.index} (hp : p ∈ B) (hy : y ∈ B) (hs : s ∈ B) (hw : w ∈ B) (b c d : ℤ)
    (g : G) :
    ∑ x ∈ B, ((((if x = p then 1 else 0) + b * (if x = y then 1 else 0) +
        c * (if x = s then 1 else 0) + d * (if x = w then 1 else 0) : ℤ)) : ℂ) *
          (basis.representation x).character g =
      (basis.representation p).character g + b * (basis.representation y).character g +
        c * (basis.representation s).character g + d * (basis.representation w).character g := by
  push_cast
  simp only [add_mul, Finset.sum_add_distrib, mul_ite, mul_one, mul_zero, ite_mul, zero_mul,
    one_mul, Finset.sum_ite_eq', hp, hy, hs, hw, ite_true]

theorem even_cyclic_principal_Fourier_family (hn : 4 ≤ n)
    (e : SemidihedralGroup n ≃* (S : Subgroup G)) (basis : FiniteIrreducibleCharacterBasis G)
    (ideal : Ideal ComplexAlgebraicIntegers) [ideal.IsMaximal]
    [CharP (ComplexAlgebraicIntegers ⧸ ideal) 2] (principal : basis.index)
    (hprincipal : (basis.representation principal).character = 1) :
    let B := coefficientBlock basis (localizedComplexIntegerRing ideal) principal
    let ρ : G := (e (r n) : G)
    let M : ℕ := modulus n
    let χ : basis.index → G → ℂ := fun c => (basis.representation c).character
    let L := multiplicityColumn basis ρ M
    let θ : basis.index → ℤ := fun c => L 0 c - L ((M / 2 : ℕ) : ℤ) c
    let η : ℕ → basis.index → ℤ := fun l c => L 0 c - L (2 * l) c
    let Θ := principalCyclicProjection basis B ρ
      (fun x => 1 - cyclicLinearCharacter ρ M ((M / 2 : ℕ) : ℤ) x)
    let E := fun l : ℕ => principalCyclicProjection basis B ρ
      (fun x => 1 - cyclicLinearCharacter ρ M (2 * l) x)
    (∀ c, characterPairing (fun x : Subgroup.zpowers ρ => χ c x)
        (fun x => 1 - cyclicLinearCharacter ρ M ((M / 2 : ℕ) : ℤ) x) = θ c) ∧
    (∀ (l : ℕ) c, characterPairing (fun x : Subgroup.zpowers ρ => χ c x)
        (fun x => 1 - cyclicLinearCharacter ρ M (2 * l) x) = η l c) ∧
    (∀ g, Θ g = ∑ c ∈ B, (θ c : ℂ) * χ c g) ∧ (∀ (l : ℕ) g, E l g = ∑ c ∈ B, (η l c : ℂ) * χ c g) ∧
    Θ 1 = 0 ∧ (∀ l : ℕ, 1 ≤ l → l ≤ M / 4 - 1 → E l 1 = 0) ∧
    θ principal = 1 ∧ (∀ l : ℕ, 1 ≤ l → l ≤ M / 4 - 1 → η l principal = 1) ∧
    characterPairing Θ 1 = 1 ∧ (∀ l : ℕ, 1 ≤ l → l ≤ M / 4 - 1 → characterPairing (E l) 1 = 1) ∧
    ∑ c ∈ B, θ c * θ c = 4 ∧ (∀ l : ℕ, 1 ≤ l → l ≤ M / 4 - 1 → ∑ c ∈ B, θ c * η l c = 2) ∧
    (∀ j l : ℕ, 1 ≤ j → j ≤ M / 4 - 1 → 1 ≤ l → l ≤ M / 4 - 1 →
      ∑ c ∈ B, η j c * η l c = 2 + if j = l then 1 else 0) ∧
    characterPairing Θ Θ = 4 ∧ (∀ l : ℕ, 1 ≤ l → l ≤ M / 4 - 1 → characterPairing Θ (E l) = 2) ∧
    (∀ j l : ℕ, 1 ≤ j → j ≤ M / 4 - 1 → 1 ≤ l → l ≤ M / 4 - 1 →
      characterPairing (E j) (E l) = 2 + if j = l then 1 else 0) ∧
    ∃ (c₁ c₂ c₃ : basis.index) (δ₁ δ₂ δ₃ ε : ℤ) (ψ : ℕ → basis.index),
      c₁ ∈ B ∧ c₂ ∈ B ∧ c₃ ∈ B ∧ c₁ ≠ c₂ ∧ c₁ ≠ c₃ ∧ c₂ ≠ c₃ ∧
      c₁ ≠ principal ∧ c₂ ≠ principal ∧ c₃ ≠ principal ∧
      (δ₁ = 1 ∨ δ₁ = -1) ∧ (δ₂ = 1 ∨ δ₂ = -1) ∧ (δ₃ = 1 ∨ δ₃ = -1) ∧ (ε = 1 ∨ ε = -1) ∧
      (∀ j l : ℕ, 1 ≤ j → j ≤ M / 4 - 1 → 1 ≤ l → l ≤ M / 4 - 1 → ψ j = ψ l → j = l) ∧
      (∀ l : ℕ, 1 ≤ l → l ≤ M / 4 - 1 →
        ψ l ∈ B ∧ ψ l ≠ principal ∧ ψ l ≠ c₁ ∧ ψ l ≠ c₂ ∧ ψ l ≠ c₃) ∧
      Θ = 1 + (δ₁ : ℂ) • χ c₁ + (δ₂ : ℂ) • χ c₂ + (δ₃ : ℂ) • χ c₃ ∧
      (∀ l : ℕ, 1 ≤ l → l ≤ M / 4 - 1 → E l = 1 + (δ₁ : ℂ) • χ c₁ + (ε : ℂ) • χ (ψ l)) ∧
      (∀ c ∈ B, θ c = (if c = principal then 1 else 0) + δ₁ * (if c = c₁ then 1 else 0) +
        δ₂ * (if c = c₂ then 1 else 0) + δ₃ * (if c = c₃ then 1 else 0)) ∧
      (∀ l : ℕ, 1 ≤ l → l ≤ M / 4 - 1 → ∀ c ∈ B, η l c = (if c = principal then 1 else 0) +
        δ₁ * (if c = c₁ then 1 else 0) + ε * (if c = ψ l then 1 else 0)) ∧
      M / 4 + 3 ≤ B.card ∧
      1 + (δ₁ : ℂ) * χ c₁ 1 + (δ₂ : ℂ) * χ c₂ 1 + (δ₃ : ℂ) * χ c₃ 1 = 0 ∧
      1 + (δ₁ : ℂ) * χ c₁ 1 ≠ 0 ∧
      (∀ l : ℕ, 1 ≤ l → l ≤ M / 4 - 1 → χ (ψ l) 1 = ‖1 + (δ₁ : ℂ) * χ c₁ 1‖) ∧
      ε = -SignType.sign (1 + (δ₁ : ℂ) * χ c₁ 1).re := by
  intro B ρ M χ L θ η Θ E
  obtain ⟨hM4, hKeven, hK2, -⟩ := modulus_eq_four_mul hn
  have hpB : principal ∈ B := coefficientBlock_self_mem _ _ _
  have hcoefΘ : ∀ c, characterPairing (fun x : Subgroup.zpowers ρ => χ c x)
      (fun x => 1 - cyclicLinearCharacter ρ M ((M / 2 : ℕ) : ℤ) x) = θ c := by
    intro c
    have hfun : (fun x => 1 - cyclicLinearCharacter ρ M ((M / 2 : ℕ) : ℤ) x) =
        fun x => cyclicLinearCharacter ρ M 0 x - cyclicLinearCharacter ρ M ((M / 2 : ℕ) : ℤ) x :=
      funext fun x => by rw [cyclicLinearCharacter_zero]
    rw [hfun, characterPairing_linear_difference hn e basis]
  have hcoefE : ∀ (l : ℕ) c, characterPairing (fun x : Subgroup.zpowers ρ => χ c x)
      (fun x => 1 - cyclicLinearCharacter ρ M (2 * l) x) = η l c := by
    intro l c
    have hfun : (fun x => 1 - cyclicLinearCharacter ρ M (2 * l) x) =
        fun x => cyclicLinearCharacter ρ M 0 x - cyclicLinearCharacter ρ M (2 * l) x :=
      funext fun x => by rw [cyclicLinearCharacter_zero]
    rw [hfun, characterPairing_linear_difference hn e basis]
  have hΘapply : ∀ g, Θ g = ∑ c ∈ B, (θ c : ℂ) * χ c g :=
    principalCyclicProjection_apply basis B ρ _ θ hcoefΘ
  have hEapply : ∀ (l : ℕ) g, E l g = ∑ c ∈ B, (η l c : ℂ) * χ c g := fun l =>
    principalCyclicProjection_apply basis B ρ _ (η l) (hcoefE l)
  have hΘfun : Θ = fun g => ∑ c ∈ B, (θ c : ℂ) * χ c g := funext hΘapply
  have hEfun : ∀ l : ℕ, E l = fun g => ∑ c ∈ B, (η l c : ℂ) * χ c g := fun l => funext (hEapply l)
  have hvals := (cyclic_principal_Fourier_projection_values hn e basis ideal principal
    hprincipal).2.1 1 (by rw [orderOf_one]; exact odd_one)
  have hΘ1 : Θ 1 = 0 := hvals.1
  have hE1 : ∀ l : ℕ, 1 ≤ l → l ≤ M / 4 - 1 → E l 1 = 0 := hvals.2.1
  have hLp := multiplicityColumn_principal hn e basis hprincipal
  have hθp : θ principal = 1 := by
    show multiplicityColumn basis (e (r n) : G) (modulus n) 0 principal -
      multiplicityColumn basis (e (r n) : G) (modulus n) ((modulus n / 2 : ℕ) : ℤ) principal = 1
    rw [hLp, hLp, ite_eq_left (dvd_zero _), ite_eq_right]
    · norm_num
    · intro hd
      have := Int.le_of_dvd (by omega) hd
      omega
  have hηp : ∀ l : ℕ, 1 ≤ l → l ≤ M / 4 - 1 → η l principal = 1 := by
    intro l hl1 hl2
    show multiplicityColumn basis (e (r n) : G) (modulus n) 0 principal -
      multiplicityColumn basis (e (r n) : G) (modulus n) (2 * l) principal = 1
    rw [hLp, hLp, ite_eq_left (dvd_zero _), ite_eq_right]
    · norm_num
    · intro hd
      have := Int.le_of_dvd (by omega) hd
      omega
  obtain ⟨hθθ, hθη, hηη⟩ := even_family_coefficient_gram hn e basis ideal principal hprincipal
  have hpairΘΘ : characterPairing Θ Θ = 4 := by
    rw [hΘfun, characterPairing_basis_combination basis B (fun c => (θ c : ℂ))]
    exact_mod_cast hθθ
  have hpairΘE : ∀ l : ℕ, 1 ≤ l → l ≤ M / 4 - 1 → characterPairing Θ (E l) = 2 := by
    intro l hl1 hl2
    rw [hΘfun, hEfun, characterPairing_basis_combination basis B (fun c => (θ c : ℂ))]
    exact_mod_cast hθη l hl1 hl2
  have hpairEE : ∀ j l : ℕ, 1 ≤ j → j ≤ M / 4 - 1 → 1 ≤ l → l ≤ M / 4 - 1 →
      characterPairing (E j) (E l) = 2 + if j = l then 1 else 0 := by
    intro j l hj1 hj2 hl1 hl2
    rw [hEfun, hEfun, characterPairing_basis_combination basis B (fun c => (η j c : ℂ))]
    have h := hηη j l hj1 hj2 hl1 hl2
    split_ifs at h ⊢ <;> exact_mod_cast h
  have hpairΘ1 : characterPairing Θ 1 = 1 := by
    rw [hΘfun, characterPairing_basis_combination_one basis hprincipal hpB]
    exact_mod_cast hθp
  have hpairE1 : ∀ l : ℕ, 1 ≤ l → l ≤ M / 4 - 1 → characterPairing (E l) 1 = 1 := by
    intro l hl1 hl2
    rw [hEfun, characterPairing_basis_combination_one basis hprincipal hpB]
    exact_mod_cast hηp l hl1 hl2
  let deg : basis.index → ℤ := fun c => (Module.finrank ℂ (basis.representation c).vector : ℤ)
  have hdegpos : ∀ c ∈ B, 0 < deg c := fun c _ => by
    show (0 : ℤ) < (Module.finrank ℂ (basis.representation c).vector : ℤ)
    exact_mod_cast (basis_character_one basis c).2
  have hdegval : ∀ c, χ c 1 = (deg c : ℂ) := fun c => by
    show (basis.representation c).character 1 =
      (((Module.finrank ℂ (basis.representation c).vector : ℤ)) : ℂ)
    rw [(basis_character_one basis c).1]
    push_cast
    rfl
  have hdegp : deg principal = 1 := by
    have h := hdegval principal
    rw [show χ principal = 1 from hprincipal, Pi.one_apply] at h
    exact_mod_cast h.symm
  have hθdeg : ∑ c ∈ B, θ c * deg c = 0 := by
    have h := hΘapply 1
    rw [hΘ1, basis_combination_one basis B θ] at h
    exact_mod_cast h.symm
  have hηdeg : ∀ l : ℕ, 1 ≤ l → l ≤ M / 4 - 1 → ∑ c ∈ B, η l c * deg c = 0 := by
    intro l hl1 hl2
    have h := hEapply l 1
    rw [hE1 l hl1 hl2, basis_combination_one basis B (η l)] at h
    exact_mod_cast h.symm
  let Jset : Finset ℕ := Finset.Icc 1 (M / 4 - 1)
  have hM4' : M = 4 * 2 ^ (n - 3) := hM4
  have hmemJ : ∀ l : ℕ, l ∈ Jset ↔ 1 ≤ l ∧ l ≤ M / 4 - 1 := fun l => Finset.mem_Icc
  have hcardJ : Fintype.card {l // l ∈ Jset} = M / 4 - 1 := by
    rw [Fintype.card_coe, Nat.card_Icc]
    omega
  have hcardJ2 : Fintype.card {l // l ∈ Jset} ≠ 2 := by
    rw [hcardJ]
    obtain ⟨k, hk⟩ := hKeven
    omega
  obtain ⟨c₁, c₂, c₃, δ₁, δ₂, δ₃, ε, s, hc₁B, hc₂B, hc₃B, h12, h13, h23, hc₁p, hc₂p, hc₃p,
      hδ₁, hδ₂, hδ₃, hε, hsinj, hsavoid, hθform, hηform, hdegrees⟩ :=
    principal_degree_zero_gram_common_constituents_coordinates hcardJ2 B hpB deg hdegpos hdegp θ
      (fun l c => η l.val c) hθdeg (fun l => hηdeg l.val ((hmemJ _).mp l.2).1 ((hmemJ _).mp l.2).2)
      hθp (fun l => hηp l.val ((hmemJ _).mp l.2).1 ((hmemJ _).mp l.2).2) hθθ
      (fun l => hθη l.val ((hmemJ _).mp l.2).1 ((hmemJ _).mp l.2).2) (fun j l => by
        have h := hηη j.val l.val ((hmemJ _).mp j.2).1 ((hmemJ _).mp j.2).2
          ((hmemJ _).mp l.2).1 ((hmemJ _).mp l.2).2
        by_cases hjl : j = l
        · rw [ite_eq_left hjl]
          rw [ite_eq_left (congrArg Subtype.val hjl)] at h
          exact h
        · rw [ite_eq_right hjl]
          rw [ite_eq_right (fun h' => hjl (Subtype.ext h'))] at h
          exact h)
  let ψ : ℕ → basis.index := fun l => if h : l ∈ Jset then s ⟨l, h⟩ else principal
  have hψ : ∀ l (h : l ∈ Jset), ψ l = s ⟨l, h⟩ := fun l h => dite_eq_left h
  have hJne : Nonempty {l // l ∈ Jset} := ⟨⟨1, (hmemJ 1).mpr ⟨le_rfl, by omega⟩⟩⟩
  obtain ⟨hw, hψdeg, hεw⟩ := hdegrees hJne
  have hsJ : ∀ (l : {l // l ∈ Jset}), s l = ψ l.val := fun l => (hψ l.val l.2).symm
  have hΘdec : Θ = 1 + (δ₁ : ℂ) • χ c₁ + (δ₂ : ℂ) • χ c₂ + (δ₃ : ℂ) • χ c₃ := by
    funext g
    have hsum : ∑ c ∈ B, (θ c : ℂ) * χ c g = ∑ c ∈ B, ((((if c = principal then 1 else 0) +
        δ₁ * (if c = c₁ then 1 else 0) + δ₂ * (if c = c₂ then 1 else 0) +
        δ₃ * (if c = c₃ then 1 else 0) : ℤ)) : ℂ) * (basis.representation c).character g :=
      Finset.sum_congr rfl fun c hc => by rw [hθform c hc]
    rw [hΘapply g, hsum, basis_combination_four basis hpB hc₁B hc₂B hc₃B, hprincipal]
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.one_apply]
    rfl
  have hEdec : ∀ l : ℕ, 1 ≤ l → l ≤ M / 4 - 1 →
      E l = 1 + (δ₁ : ℂ) • χ c₁ + (ε : ℂ) • χ (ψ l) := by
    intro l hl1 hl2
    have hl : l ∈ Jset := (hmemJ l).mpr ⟨hl1, hl2⟩
    funext g
    have hsum : ∑ c ∈ B, (η l c : ℂ) * χ c g = ∑ c ∈ B, ((((if c = principal then 1 else 0) +
        δ₁ * (if c = c₁ then 1 else 0) + ε * (if c = ψ l then 1 else 0) : ℤ)) : ℂ) *
          (basis.representation c).character g :=
      Finset.sum_congr rfl fun c hc => by
        have h := hηform ⟨l, hl⟩ c hc
        rw [hsJ] at h
        rw [h]
    have hψB : ψ l ∈ B := by rw [hψ l hl]; exact (hsavoid _).1
    rw [hEapply l g, hsum, basis_combination_three basis hpB hc₁B hψB, hprincipal]
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.one_apply]
    rfl
  have hcardB : M / 4 + 3 ≤ B.card := by
    let T : Finset basis.index := {principal, c₁, c₂, c₃}
    have hT : T.card = 4 := by
      rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem, Finset.card_pair h23]
      · simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
        exact ⟨h12, h13⟩
      · simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
        exact ⟨hc₁p.symm, hc₂p.symm, hc₃p.symm⟩
    have hU : (Finset.univ.image s).card = M / 4 - 1 := by
      rw [Finset.card_image_of_injective _ hsinj, Finset.card_univ, hcardJ]
    have hdisj : Disjoint T (Finset.univ.image s) := by
      rw [Finset.disjoint_left]
      intro x hxT hxU
      obtain ⟨l, -, rfl⟩ := Finset.mem_image.mp hxU
      obtain ⟨-, hsp, hs1, hs2, hs3⟩ := hsavoid l
      simp only [T, Finset.mem_insert, Finset.mem_singleton] at hxT
      rcases hxT with h | h | h | h
      · exact hsp h
      · exact hs1 h
      · exact hs2 h
      · exact hs3 h
    have hsub : T ∪ Finset.univ.image s ⊆ B := by
      intro x hx
      rcases Finset.mem_union.mp hx with hx | hx
      · simp only [T, Finset.mem_insert, Finset.mem_singleton] at hx
        rcases hx with rfl | rfl | rfl | rfl
        · exact hpB
        · exact hc₁B
        · exact hc₂B
        · exact hc₃B
      · obtain ⟨l, -, rfl⟩ := Finset.mem_image.mp hx
        exact (hsavoid l).1
    have h := Finset.card_le_card hsub
    rw [Finset.card_union_of_disjoint hdisj, hT, hU] at h
    omega
  have hvalue : 1 + (δ₁ : ℂ) * χ c₁ 1 = ((1 + δ₁ * deg c₁ : ℤ) : ℂ) := by
    rw [hdegval c₁]
    push_cast
    ring
  refine ⟨hcoefΘ, hcoefE, hΘapply, hEapply, hΘ1, hE1, hθp, hηp, hpairΘ1, hpairE1, hθθ, hθη, hηη,
    hpairΘΘ, hpairΘE, hpairEE, c₁, c₂, c₃, δ₁, δ₂, δ₃, ε, ψ, hc₁B, hc₂B, hc₃B, h12, h13, h23,
    hc₁p, hc₂p, hc₃p, hδ₁, hδ₂, hδ₃, hε, fun j l hj1 hj2 hl1 hl2 hjl => ?_,
    fun l hl1 hl2 => ?_, hΘdec, hEdec, hθform, fun l hl1 hl2 c hc => ?_, hcardB, ?_, ?_,
    fun l hl1 hl2 => ?_, ?_⟩
  · have hj : j ∈ Jset := (hmemJ j).mpr ⟨hj1, hj2⟩
    have hl : l ∈ Jset := (hmemJ l).mpr ⟨hl1, hl2⟩
    rw [hψ j hj, hψ l hl] at hjl
    exact congrArg Subtype.val (hsinj hjl)
  · have hl : l ∈ Jset := (hmemJ l).mpr ⟨hl1, hl2⟩
    rw [hψ l hl]
    exact hsavoid _
  · have hl : l ∈ Jset := (hmemJ l).mpr ⟨hl1, hl2⟩
    have h := hηform ⟨l, hl⟩ c hc
    rw [hsJ] at h
    exact h
  · have h := congrFun hΘdec 1
    rw [hΘ1] at h
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.one_apply] at h
    exact h.symm
  · rw [hvalue]
    exact_mod_cast hw
  · have hl : l ∈ Jset := (hmemJ l).mpr ⟨hl1, hl2⟩
    rw [hvalue, Complex.norm_intCast, ← Int.cast_abs, ← hψdeg ⟨l, hl⟩, hsJ, hdegval]
    push_cast
    rfl
  · rw [hvalue, Complex.intCast_re, sign_intCast, hεw, Int.sign_eq_sign]

end CFSG.Semidihedral.Principal

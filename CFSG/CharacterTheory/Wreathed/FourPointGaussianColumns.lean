module

public import CFSG.CharacterTheory.Wreathed.FourPointGaussianColumnsSums
public import CFSG.CharacterTheory.Wreathed.FourPointOddSectionIndicator
public import CFSG.CharacterTheory.Wreathed.FourPointGaussianColumnsLocal
public import CFSG.CharacterTheory.Wreathed.FourPointOrderFour

public noncomputable section

namespace CFSG.Wreathed.FourPointGaussianColumns

open Equiv CFSG.TwoRankLowerBound.Helpers CFSG.Wreathed.CyclicCentralSL2Extension
  CFSG.Wreathed.FourPointCompleteModel CFSG.Wreathed.FourPointOrderFour
  CFSG.Wreathed.OddNormalQuotientInvolutions CFSG.Wreathed.FourPointOddSectionIndicator

open scoped BigOperators Classical

variable {G : Type} [Group G] [Fintype G] [IsSimpleGroup G]

theorem four_point_global_gaussian_columns_and_conjugate_pair_dichotomy
    (hnonab : ∃ a b : G, a * b ≠ b * a) (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G)
    (e : S ≃* Wreath (2 ^ n)) (alpha : centralizerFullQuotient n hn S e ≃* Perm (Fin 4))
    [Fintype (centralizerOddCoreQuotient n S e)] :
    let H := centralizerOddCoreQuotient n S e
    let N := involutionCentralizer n S e
    let R := centralizerOddCore n S e
    let π := centralizerOddCoreMap n S e
    let aN : N := wreathModelHom (centralizerSylow n hn S e) (centralizerCoordinates n hn S e)
      (Original.a (2 ^ n))
    let a : G := wreathModelHom S e (Original.a (2 ^ n))
    let x : G := wreathModelHom S e (Original.x (2 ^ n))
    let C := orderFourCentralizer n S e
    let R₀ : Subgroup G := R.map N.subtype ⊓ C
    let W := CentralExtension (ZMod 3) twoUnit 4 (by norm_num) (by decide)
    let u := cyclicGenerator (ZMod 3) twoUnit 4 (by norm_num) (by decide)
    let iF := specialInclusion (ZMod 3) twoUnit 4 (by norm_num) (by decide)
    let U₀ : W := iF (CentralSL2.upperSL (ZMod 3) 1)
    let y₀ : W := u ^ 2 * iF (CFSG.Wreathed.CentralSL2Abelianization.weyl (ZMod 3))
    n = 2 ∧ (∃ Φ : W ≃* H, Φ (u ^ 2) = π aN) ∧
    ∀ Φ : W ≃* H, Φ (u ^ 2) = π aN →
      (∃ y : N, orderOf y = 2 ∧ π y = Φ y₀) ∧
      (∃ z : N, (z : G) ∈ C ∧ Odd (orderOf z) ∧ π z = Φ U₀) ∧
      ∀ y : N, orderOf y = 2 → π y = Φ y₀ →
      ∀ z : N, (z : G) ∈ C → Odd (orderOf z) → π z = Φ U₀ →
        let eR : ℕ := (kernelCentralizer R y).index
        ∀ (ideal : Ideal ComplexAlgebraicIntegers) [ideal.IsMaximal]
          [CharP (ComplexAlgebraicIntegers ⧸ ideal) 2]
          (basis : FiniteIrreducibleCharacterBasis G) (principal : basis.index)
          (_ : (basis.representation principal).character = 1) (i : ℂ), i ^ 2 = -1 →
          let B := coefficientBlock basis (localizedComplexIntegerRing ideal) principal
          let X : basis.index → G → ℂ := fun χ => (basis.representation χ).character
          let d : basis.index → ℂ := fun χ => X χ 1
          let Ax : basis.index → ℂ := fun χ => X χ x
          let Bx : basis.index → ℂ := fun χ => X χ (x * z)
          let T : basis.index → ℂ := fun χ => X χ a
          let Ua : basis.index → ℂ := fun χ => X χ (a * z)
          (∀ χ ∈ B, (∃ k : ℤ, Ax χ = k) ∧ (∃ k : ℤ, Bx χ = k) ∧
            (∃ s k : ℤ, T χ = s + k * i) ∧ ∃ s k : ℤ, Ua χ = s + k * i) ∧
          ∑ χ ∈ B, Ax χ ^ 2 = 96 ∧ ∑ χ ∈ B, Bx χ ^ 2 = 12 ∧ ∑ χ ∈ B, Ax χ * Bx χ = 0 ∧
          ∑ χ ∈ B, Complex.normSq (T χ) = 96 ∧ ∑ χ ∈ B, Complex.normSq (Ua χ) = 12 ∧
          ∑ χ ∈ B, T χ * starRingEnd ℂ (Ua χ) = 0 ∧
          (∀ χ ∈ B, (∃ k : ℤ, Ax χ - Bx χ = 3 * k) ∧
            ∃ s k : ℤ, T χ - Ua χ = 3 * (s + k * i)) ∧
          ∑ χ ∈ B, d χ * Ax χ = 0 ∧ ∑ χ ∈ B, d χ * Bx χ = 0 ∧ ∑ χ ∈ B, d χ * T χ = 0 ∧
          ∑ χ ∈ B, d χ * Ua χ = 0 ∧
          Ax principal = 1 ∧ Bx principal = 1 ∧ T principal = 1 ∧ Ua principal = 1 ∧
          (∀ χ ∈ B, ∀ r : N, Odd (orderOf r) →
            X χ (x * r) = Bx χ + (Ax χ - Bx χ) * (if r ∈ R then 1 else 0)) ∧
          (∀ χ ∈ B, ∀ r : C, Odd (orderOf r) →
            X χ (a * r) = Ua χ + (T χ - Ua χ) * (if (r : G) ∈ R₀ then 1 else 0)) ∧
          ∑ χ ∈ B, T χ ^ 2 = 0 ∧ ∑ χ ∈ B, Ua χ ^ 2 = 0 ∧ ∑ χ ∈ B, T χ * Ua χ = 0 ∧
          ∑ χ ∈ B, imCoeff i (T χ) ^ 2 = 48 ∧ ∑ χ ∈ B, imCoeff i (Ua χ) ^ 2 = 6 ∧
          ∑ χ ∈ B, imCoeff i (T χ) * imCoeff i (Ua χ) = 0 ∧
          (∀ χ ∈ B, ∃ χ' ∈ B, ∀ g, X χ' g = starRingEnd ℂ (X χ g)) ∧
          GaussianPairDichotomy basis B i T Ua ∧
          ∑ χ ∈ B, Ax χ ^ 2 * Bx χ / d χ = 0 ∧
          (Nat.card G : ℂ) * ∑ χ ∈ B, Ax χ ^ 3 / d χ = 55296 * Nat.card R * eR ^ 2 ∧
          Nat.card G = 96 * Nat.card R * N.index ∧ Odd N.index := by
  intro H N R π aN a x C R₀ W u iF U₀ y₀
  have hn2 : n = 2 := FourPointResidual.four_point_parameter n hn S e alpha
  obtain ⟨Φ₀, hΦ₀, -⟩ := exists_four_point_model_equiv hnonab n hn S e alpha
  refine ⟨hn2, ⟨Φ₀, hΦ₀⟩, ?_⟩
  intro Φ hΦ
  subst hn2
  obtain ⟨-, -, hind⟩ := four_point_principal_odd_section_odd_core_indicator hnonab 2 hn S e alpha
  obtain ⟨hyex, hind⟩ := hind Φ hΦ
  refine ⟨hyex, ?_, ?_⟩
  · obtain ⟨hv3, -, -⟩ := odd_classes_of_equiv Φ
    obtain ⟨c, hc⟩ := orderFourMap_surjective 2 hn S e (Φ U₀)
    refine ⟨Subgroup.inclusion (orderFourCentralizer_le 2 S e) c, c.2, ?_, hc⟩
    rw [orderOf_injective (Subgroup.inclusion (orderFourCentralizer_le 2 S e))
      (Subgroup.inclusion_injective _) c]
    exact odd_orderOf_of_odd_orderOf_map _ (orderFourMap_ker_odd 2 hn S e) c
      (by rw [hc, hv3]; decide)
  intro y hy2 hyΦ z hzC hzodd hzΦ eR ideal _ _ basis principal hprincipal i hi B X d Ax Bx T Ua
  obtain ⟨basisH⟩ := finiteIrreducibleCharacterBasis_exists (G := H)
  obtain ⟨principalH, hprincipalH⟩ := finiteIrreducibleCharacterBasis_contains_irreducible basisH
    (principalFiniteComplexRepresentation _) (principalFiniteComplexRepresentation_isIrreducible _)
  rw [principalFiniteComplexRepresentation_character] at hprincipalH
  obtain ⟨basisN⟩ := finiteIrreducibleCharacterBasis_exists (G := N)
  obtain ⟨principalN, hprincipalN⟩ := finiteIrreducibleCharacterBasis_contains_irreducible basisN
    (principalFiniteComplexRepresentation _) (principalFiniteComplexRepresentation_isIrreducible _)
  rw [principalFiniteComplexRepresentation_character] at hprincipalN
  obtain ⟨basisC⟩ := finiteIrreducibleCharacterBasis_exists (G := C)
  obtain ⟨principalC, hprincipalC⟩ := finiteIrreducibleCharacterBasis_contains_irreducible basisC
    (principalFiniteComplexRepresentation _) (principalFiniteComplexRepresentation_isIrreducible _)
  rw [principalFiniteComplexRepresentation_character] at hprincipalC
  obtain ⟨-, -, -, -, -, haord, hapow, -, -, -, -, -, -, hcardN, -, hnotconj, hzprops, -, -, -, -,
      hbasisN, hbasisC, hval1N, hval1C, hvalz⟩ :=
    four_point_order_four_centralizer_and_odd_restriction_bases hnonab 2 hn S e alpha ideal
      basisH principalH hprincipalH basisN principalN hprincipalN basisC principalC hprincipalC
  obtain ⟨hzR, -, -, hcommN, -⟩ := (hzprops Φ).2 z hzC hzodd hzΦ
  obtain ⟨hvalzN, hvalzC⟩ := hvalz Φ z hzC hzodd hzΦ
  have hcomm : Commute a (z : G) := congrArg Subtype.val hcommN
  have ha4 : orderOf a = 2 ^ 2 := by
    rw [show a = (aN : G) from rfl, Subgroup.orderOf_coe, haord]
    norm_num
  have hx2 : orderOf x = 2 ^ 1 := by
    have h : orderOf (centralInvolution 2 S e) = 2 := by
      rw [← hapow, orderOf_pow_of_dvd (by norm_num) (by rw [haord]; norm_num), haord]
    rw [show x = (centralInvolution 2 S e : G) from rfl, Subgroup.orderOf_coe, h, pow_one]
  have hKx : Subgroup.centralizer (Subgroup.zpowers x : Set G) = N := by
    rw [Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure]
    rfl
  have hKa : Subgroup.centralizer (Subgroup.zpowers a : Set G) = C := by
    rw [Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure]
  obtain ⟨Vx, hVxint, hVxrow, hVxgram, hVxdeg⟩ := section_rows_of_oddRestrictionBasis basis ideal
    principal hprincipal le_rfl hx2 isPrimitiveRoot_neg_one_two N hKx basisN principalN
    hprincipalN _ _ hbasisN
  obtain ⟨Va, hVaint, hVarow, hVagram, hVadeg⟩ := section_rows_of_oddRestrictionBasis basis ideal
    principal hprincipal (by norm_num) ha4 (isPrimitiveRoot_of_sq_eq_neg_one hi) C hKa basisC
    principalC hprincipalC _ _ hbasisC
  set oneN : OddElements N := ⟨1, by rw [orderOf_one]; exact odd_one⟩
  set oneC : OddElements C := ⟨1, by rw [orderOf_one]; exact odd_one⟩
  set zN : OddElements N := ⟨z, hzodd⟩
  set zC : OddElements C :=
    ⟨⟨z, hzC⟩, by rw [Subgroup.orderOf_mk, Subgroup.orderOf_coe]; exact hzodd⟩
  obtain ⟨h1N0, h1N1⟩ := hval1N oneN rfl
  obtain ⟨h1C0, h1C1⟩ := hval1C oneC rfl
  obtain ⟨hzN0, hzN1⟩ := hvalzN zN rfl
  obtain ⟨hzC0, hzC1⟩ := hvalzC zC rfl
  have hAx : ∀ χ ∈ B, Ax χ = Vx χ 0 + 2 * Vx χ 1 := fun χ hχ => by
    have h := hVxrow χ hχ oneN
    rw [Fin.sum_univ_two, h1N0, h1N1] at h
    change (basis.representation χ).character x = _
    rw [show x = x * ((oneN : N) : G) by simp [oneN], h]
    ring
  have hBx : ∀ χ ∈ B, Bx χ = Vx χ 0 - Vx χ 1 := fun χ hχ => by
    have h := hVxrow χ hχ zN
    rw [Fin.sum_univ_two, hzN0, hzN1] at h
    change (basis.representation χ).character (x * z) = _
    rw [show x * (z : G) = x * ((zN : N) : G) from rfl, h]
    ring
  have hT : ∀ χ ∈ B, T χ = Va χ 0 + 2 * Va χ 1 := fun χ hχ => by
    have h := hVarow χ hχ oneC
    rw [Fin.sum_univ_two, h1C0, h1C1] at h
    change (basis.representation χ).character a = _
    rw [show a = a * ((oneC : C) : G) by simp [oneC], h]
    ring
  have hU : ∀ χ ∈ B, Ua χ = Va χ 0 - Va χ 1 := fun χ hχ => by
    have h := hVarow χ hχ zC
    rw [Fin.sum_univ_two, hzC0, hzC1] at h
    change (basis.representation χ).character (a * z) = _
    rw [show a * (z : G) = a * ((zC : C) : G) from rfl, h]
    ring
  have hVxZ : ∀ χ j, ∃ k : ℤ, Vx χ j = k := fun χ j =>
    exists_int_of_mem_adjoin_neg_one (hVxint χ j)
  have hVaZ : ∀ χ j, ∃ s k : ℤ, Va χ j = s + k * i := fun χ j =>
    exists_gaussian_of_mem_adjoin hi (hVaint χ j)
  have hconjVx : ∀ χ j, starRingEnd ℂ (Vx χ j) = Vx χ j := fun χ j => by
    obtain ⟨k, hk⟩ := hVxZ χ j
    rw [hk, map_intCast]
  have hdreal : ∀ χ ∈ B, starRingEnd ℂ (d χ) = d χ := fun χ _ => conj_character_one basis χ
  obtain ⟨gx1, gx2, gx3, gx4, gx5⟩ := gram_column_sums B Vx d hVxgram hVxdeg hdreal
  obtain ⟨ga1, ga2, ga3, ga4, ga5⟩ := gram_column_sums B Va d hVagram hVadeg hdreal
  have hTnorm : ∑ χ ∈ B, Complex.normSq (T χ) = 96 := by
    have h : ((∑ χ ∈ B, Complex.normSq (T χ) : ℝ) : ℂ) = 96 := by
      push_cast
      rw [← ga1]
      refine Finset.sum_congr rfl fun χ hχ => ?_
      rw [Complex.normSq_eq_conj_mul_self, hT χ hχ]
    exact_mod_cast h
  have hUnorm : ∑ χ ∈ B, Complex.normSq (Ua χ) = 12 := by
    have h : ((∑ χ ∈ B, Complex.normSq (Ua χ) : ℝ) : ℂ) = 12 := by
      push_cast
      rw [← ga2]
      refine Finset.sum_congr rfl fun χ hχ => ?_
      rw [Complex.normSq_eq_conj_mul_self, hU χ hχ]
    exact_mod_cast h
  have hTcU : ∑ χ ∈ B, T χ * starRingEnd ℂ (Ua χ) = 0 := by
    rw [← ga3]
    exact Finset.sum_congr rfl fun χ hχ => by rw [hT χ hχ, hU χ hχ]
  obtain ⟨hT2, hU2, hTU⟩ := section_square_sums basis ideal principal a (z : G)
    (by rw [ha4]) (by rw [Subgroup.orderOf_coe]; exact hzodd) hcomm hnotconj
  obtain ⟨him1, him2, him3⟩ := imag_column_sums B T Ua hi hTnorm hUnorm hT2 hU2 hTU hTcU
  have hTint : ∀ χ ∈ B, ∃ s k : ℤ, T χ = s + k * i := fun χ hχ => by
    obtain ⟨s₀, k₀, h₀⟩ := hVaZ χ 0
    obtain ⟨s₁, k₁, h₁⟩ := hVaZ χ 1
    refine ⟨s₀ + 2 * s₁, k₀ + 2 * k₁, ?_⟩
    rw [hT χ hχ, h₀, h₁]
    push_cast
    ring
  have hUint : ∀ χ ∈ B, ∃ s k : ℤ, Ua χ = s + k * i := fun χ hχ => by
    obtain ⟨s₀, k₀, h₀⟩ := hVaZ χ 0
    obtain ⟨s₁, k₁, h₁⟩ := hVaZ χ 1
    refine ⟨s₀ - s₁, k₀ - k₁, ?_⟩
    rw [hU χ hχ, h₀, h₁]
    push_cast
    ring
  have hTUmod : ∀ χ ∈ B, ∃ s k : ℤ, T χ - Ua χ = 3 * (s + k * i) := fun χ hχ => by
    obtain ⟨s₁, k₁, h₁⟩ := hVaZ χ 1
    refine ⟨s₁, k₁, ?_⟩
    rw [hT χ hχ, hU χ hχ, ← h₁]
    ring
  have hind' := hind y hy2 hyΦ ideal basis principal hprincipal
  have hcardG : (Nat.card G : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Nat.card_pos.ne'
  have hz' := hind' z hzodd
  rw [ite_eq_right hzR, mul_zero] at hz'
  have h1' := hind' 1 (by rw [orderOf_one]; exact odd_one)
  rw [ite_eq_left (Subgroup.one_mem _), mul_one] at h1'
  refine ⟨fun χ hχ => ⟨?_, ?_, hTint χ hχ, hUint χ hχ⟩, ?_, ?_, ?_, hTnorm, hUnorm, hTcU,
    fun χ hχ => ⟨?_, hTUmod χ hχ⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hT2, hU2, hTU, him1,
    him2, him3, fun χ hχ => ⟨conjLabel basis χ,
      conjLabel_mem_coefficientBlock basis _ principal hprincipal χ hχ, conjLabel_spec basis χ⟩,
    gaussianPairDichotomy_of_sums basis ideal principal hprincipal hi a (a * z) hTint hUint hTUmod
      him1 him2 him3, ?_, ?_, ?_, ?_⟩
  · obtain ⟨k₀, h₀⟩ := hVxZ χ 0
    obtain ⟨k₁, h₁⟩ := hVxZ χ 1
    exact ⟨k₀ + 2 * k₁, by rw [hAx χ hχ, h₀, h₁]; push_cast; ring⟩
  · obtain ⟨k₀, h₀⟩ := hVxZ χ 0
    obtain ⟨k₁, h₁⟩ := hVxZ χ 1
    exact ⟨k₀ - k₁, by rw [hBx χ hχ, h₀, h₁]; push_cast; ring⟩
  · rw [← gx1]
    refine Finset.sum_congr rfl fun χ hχ => ?_
    rw [hAx χ hχ, map_add, map_mul, hconjVx, hconjVx, map_ofNat, sq]
  · rw [← gx2]
    refine Finset.sum_congr rfl fun χ hχ => ?_
    rw [hBx χ hχ, map_sub, hconjVx, hconjVx, sq]
  · rw [← gx3]
    refine Finset.sum_congr rfl fun χ hχ => ?_
    rw [hAx χ hχ, hBx χ hχ, map_sub, hconjVx, hconjVx]
  · obtain ⟨k₁, h₁⟩ := hVxZ χ 1
    exact ⟨k₁, by rw [hAx χ hχ, hBx χ hχ, h₁]; ring⟩
  · rw [← gx4]
    exact Finset.sum_congr rfl fun χ hχ => by rw [hAx χ hχ]
  · rw [← gx5]
    exact Finset.sum_congr rfl fun χ hχ => by rw [hBx χ hχ]
  · rw [← ga4]
    exact Finset.sum_congr rfl fun χ hχ => by rw [hT χ hχ]
  · rw [← ga5]
    exact Finset.sum_congr rfl fun χ hχ => by rw [hU χ hχ]
  · change X principal x = 1
    simp only [X, hprincipal, Pi.one_apply]
  · change X principal (x * z) = 1
    simp only [X, hprincipal, Pi.one_apply]
  · change X principal a = 1
    simp only [X, hprincipal, Pi.one_apply]
  · change X principal (a * z) = 1
    simp only [X, hprincipal, Pi.one_apply]
  · intro χ hχ r hr
    have h : (basis.representation χ).character (x * r) = _ := hVxrow χ hχ ⟨r, hr⟩
    rw [Fin.sum_univ_two] at h
    change (basis.representation χ).character (x * r) = _
    rw [h, hAx χ hχ, hBx χ hχ]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one]
    split_ifs <;> ring
  · intro χ hχ r hr
    have h : (basis.representation χ).character (a * r) = _ := hVarow χ hχ ⟨r, hr⟩
    rw [Fin.sum_univ_two] at h
    change (basis.representation χ).character (a * r) = _
    rw [h, hT χ hχ, hU χ hχ]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one]
    split_ifs <;> ring
  · exact (mul_eq_zero.mp hz').resolve_left hcardG
  · rw [← h1']
    congr 1
    refine Finset.sum_congr rfl fun χ _ => ?_
    simp only [OneMemClass.coe_one, mul_one]
    ring
  · rw [← Subgroup.card_mul_index N, hcardN]
  · have hle : (S : Subgroup G) ≤ N := sylow_le_involutionCentralizer 2 hn S e
    have hdvd : N.index ∣ (S : Subgroup G).index := Subgroup.index_dvd_of_le hle
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have hS : ¬ 2 ∣ (S : Subgroup G).index := S.not_dvd_index
    exact (odd_iff_not_two_dvd _).mpr fun h => hS (h.trans hdvd)

end CFSG.Wreathed.FourPointGaussianColumns

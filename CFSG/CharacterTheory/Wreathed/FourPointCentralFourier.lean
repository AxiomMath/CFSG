module

public import CFSG.CharacterTheory.Wreathed.FourPointCentralFourierGram
public import CFSG.CharacterTheory.Wreathed.FourPointGaussianColumns

public noncomputable section

namespace CFSG.Wreathed.FourPointCentralFourier

open Equiv CFSG.TwoRankLowerBound.Helpers CFSG.Wreathed.CyclicCentralSL2Extension
  CFSG.Wreathed.FourPointCompleteModel CFSG.Wreathed.FourPointOrderFour
  CFSG.Wreathed.FourPointGaussianColumns CFSG.Wreathed.ConditionalFourier

open scoped BigOperators Classical

variable {G : Type} [Group G] [Fintype G] [IsSimpleGroup G]

theorem four_point_central_section_integral_fourier_columns
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
    n = 2 ∧ (∃ Φ : W ≃* H, Φ (u ^ 2) = π aN) ∧
    ∀ Φ : W ≃* H, Φ (u ^ 2) = π aN →
      (∃ z : N, (z : G) ∈ C ∧ Odd (orderOf z) ∧ π z = Φ U₀) ∧
      ∀ z : N, (z : G) ∈ C → Odd (orderOf z) → π z = Φ U₀ →
        ∀ (ideal : Ideal ComplexAlgebraicIntegers) [ideal.IsMaximal]
          [CharP (ComplexAlgebraicIntegers ⧸ ideal) 2]
          (basis : FiniteIrreducibleCharacterBasis G) (principal : basis.index)
          (_ : (basis.representation principal).character = 1) (i : ℂ), i ^ 2 = -1 →
          let B₀ := coefficientBlock basis (localizedComplexIntegerRing ideal) principal
          let X : basis.index → G → ℂ := fun χ => (basis.representation χ).character
          let d : basis.index → ℂ := fun χ => X χ 1
          let Ax : basis.index → ℂ := fun χ => X χ x
          let Bx : basis.index → ℂ := fun χ => X χ (x * z)
          let T : basis.index → ℂ := fun χ => X χ a
          let Ua : basis.index → ℂ := fun χ => X χ (a * z)
          let v : basis.index → ℕ → Fin 2 → ℂ := fun χ n' =>
            if n' = 1 then ![(T χ + 2 * Ua χ) / 3, (T χ - Ua χ) / 3]
            else if n' = 2 then ![(Ax χ + 2 * Bx χ) / 3, (Ax χ - Bx χ) / 3]
            else ![starRingEnd ℂ ((T χ + 2 * Ua χ) / 3), starRingEnd ℂ ((T χ - Ua χ) / 3)]
          let f : basis.index → ℕ → Fin 2 → ℂ := fun χ j ℓ =>
            (1 / 4) * ∑ n' ∈ Finset.Icc 1 3, (i ^ (j * n') - 1) * v χ n' ℓ
          let M : Matrix (Fin 2) (Fin 2) ℤ := !![16, 8; 8, 12]
          (∀ χ ∈ B₀, ∀ j ∈ Finset.Icc 1 3, ∀ ℓ, ∃ k : ℤ, f χ j ℓ = k) ∧
          (∀ j ∈ Finset.Icc 1 3, ∀ k ∈ Finset.Icc 1 3, ∀ ℓ t,
            ∑ χ ∈ B₀, f χ j ℓ * f χ k t = ((if j = k then 1 else 0) + 1) * M ℓ t / 4) ∧
          (∀ j ℓ, ∑ χ ∈ B₀, d χ * f χ j ℓ = 0) ∧
          (∀ j ∈ Finset.Icc 1 3, f principal j 0 = -1 ∧ f principal j 1 = 0) ∧
          (∀ χ ∈ B₀, ∀ n' ∈ Finset.Icc 1 3, ∀ r : C, Odd (orderOf r) →
            X χ (a ^ n' * r) = v χ n' 0 + v χ n' 1 * (3 * (if (r : G) ∈ R₀ then 1 else 0) - 1)) ∧
          (∀ χ ∈ B₀, ∀ n' ∈ Finset.Icc 1 3, ∀ ℓ,
            v χ n' ℓ = ∑ j ∈ Finset.Icc 1 3, f χ j ℓ * i ^ (-((j : ℤ) * n'))) ∧
          (∀ χ ∈ B₀, ∃ χ' ∈ B₀, ∀ g, X χ' g = starRingEnd ℂ (X χ g)) ∧
          (∀ χ ∈ B₀, ∀ χ' : basis.index, (∀ g, X χ' g = starRingEnd ℂ (X χ g)) →
            ∀ j ∈ Finset.Icc 1 3, ∀ ℓ, f χ' j ℓ = f χ (4 - j) ℓ) ∧
          (∀ j ∈ Finset.Icc 1 3, ∀ k ∈ Finset.Icc 1 3,
            ∑ χ ∈ B₀, f χ j 0 * f χ k 0 = if j = k then 8 else 4) := by
  intro H N R π aN a x C R₀ W u iF U₀
  have hn2 : n = 2 := FourPointResidual.four_point_parameter n hn S e alpha
  obtain ⟨Φ₀, hΦ₀, -⟩ := exists_four_point_model_equiv hnonab n hn S e alpha
  refine ⟨hn2, ⟨Φ₀, hΦ₀⟩, ?_⟩
  intro Φ hΦ
  subst hn2
  obtain ⟨-, -, hG⟩ :=
    four_point_global_gaussian_columns_and_conjugate_pair_dichotomy hnonab 2 hn S e alpha
  obtain ⟨⟨y, hy2, hyΦ⟩, hzex, hG⟩ := hG Φ hΦ
  refine ⟨hzex, ?_⟩
  intro z hzC hzodd hzΦ ideal _ _ basis principal hprincipal i hi B₀ X d Ax Bx T Ua v f M
  obtain ⟨hint₀, hA2₀, hB2₀, hAB₀, hTn₀, hUn₀, hTcU₀, -, hdA₀, hdB₀, hdT₀, hdU₀, hpA₀, hpB₀,
      hpT₀, hpU₀, hsecx₀, hseca₀, hT2₀, hU2₀, hTU₀, -, -, -, hstab₀, -⟩ :=
    hG y hy2 hyΦ z hzC hzodd hzΦ ideal basis principal hprincipal i hi
  have hint : ∀ χ ∈ B₀, (∃ k : ℤ, Ax χ = k) ∧ (∃ k : ℤ, Bx χ = k) ∧
      (∃ s k : ℤ, T χ = s + k * i) ∧ ∃ s k : ℤ, Ua χ = s + k * i := hint₀
  have hA2 : ∑ χ ∈ B₀, Ax χ ^ 2 = 96 := hA2₀
  have hB2 : ∑ χ ∈ B₀, Bx χ ^ 2 = 12 := hB2₀
  have hAB : ∑ χ ∈ B₀, Ax χ * Bx χ = 0 := hAB₀
  have hTn : ∑ χ ∈ B₀, Complex.normSq (T χ) = 96 := hTn₀
  have hUn : ∑ χ ∈ B₀, Complex.normSq (Ua χ) = 12 := hUn₀
  have hTcU : ∑ χ ∈ B₀, T χ * starRingEnd ℂ (Ua χ) = 0 := hTcU₀
  have hdA : ∑ χ ∈ B₀, d χ * Ax χ = 0 := hdA₀
  have hdB : ∑ χ ∈ B₀, d χ * Bx χ = 0 := hdB₀
  have hdT : ∑ χ ∈ B₀, d χ * T χ = 0 := hdT₀
  have hdU : ∑ χ ∈ B₀, d χ * Ua χ = 0 := hdU₀
  have hpA : Ax principal = 1 := hpA₀
  have hpB : Bx principal = 1 := hpB₀
  have hpT : T principal = 1 := hpT₀
  have hpU : Ua principal = 1 := hpU₀
  have hsecx : ∀ χ ∈ B₀, ∀ r : N, Odd (orderOf r) →
      X χ (x * r) = Bx χ + (Ax χ - Bx χ) * (if r ∈ R then 1 else 0) := hsecx₀
  have hseca : ∀ χ ∈ B₀, ∀ r : C, Odd (orderOf r) →
      X χ (a * r) = Ua χ + (T χ - Ua χ) * (if (r : G) ∈ R₀ then 1 else 0) := hseca₀
  have hT2 : ∑ χ ∈ B₀, T χ ^ 2 = 0 := hT2₀
  have hU2 : ∑ χ ∈ B₀, Ua χ ^ 2 = 0 := hU2₀
  have hTU : ∑ χ ∈ B₀, T χ * Ua χ = 0 := hTU₀
  have hstab : ∀ χ ∈ B₀, ∃ χ' ∈ B₀, ∀ g, X χ' g = starRingEnd ℂ (X χ g) := hstab₀
  clear hint₀ hA2₀ hB2₀ hAB₀ hTn₀ hUn₀ hTcU₀ hdA₀ hdB₀ hdT₀ hdU₀ hpA₀ hpB₀ hpT₀ hpU₀ hsecx₀ hseca₀
    hT2₀ hU2₀ hTU₀ hstab₀ hG
  have hζ : IsPrimitiveRoot i (2 ^ 2) := isPrimitiveRoot_of_sq_eq_neg_one hi
  have hi4 : i ^ 4 = 1 := by
    rw [show (4 : ℕ) = 2 * 2 by norm_num, pow_mul, hi]
    norm_num
  have ha4 : orderOf a = 2 ^ 2 := orderOf_wreathModelHom_a 2 S e
  have hxa : x = a ^ 2 := by
    change wreathModelHom S e (Original.x (2 ^ 2)) = wreathModelHom S e (Original.a (2 ^ 2)) ^ 2
    rw [wreathModelHom_x_eq]
    norm_num
  have hx2 : orderOf x = 2 ^ 1 := by
    rw [hxa, orderOf_pow_of_dvd (by norm_num) (by rw [ha4]; norm_num), ha4]
    norm_num
  have hza : (z : G) * a = a * z := Subgroup.mem_centralizer_singleton_iff.mp hzC
  have hzx : (z : G) * x = x * z := Subgroup.mem_centralizer_singleton_iff.mp z.2
  have hzodd' : Odd (orderOf (z : G)) := by rw [Subgroup.orderOf_coe]; exact hzodd
  have hAreal : ∀ χ ∈ B₀, starRingEnd ℂ (Ax χ) = Ax χ := fun χ hχ => by
    obtain ⟨k, hk⟩ := (hint χ hχ).1
    rw [hk, map_intCast]
  have hBreal : ∀ χ ∈ B₀, starRingEnd ℂ (Bx χ) = Bx χ := fun χ hχ => by
    obtain ⟨k, hk⟩ := (hint χ hχ).2.1
    rw [hk, map_intCast]
  have hdreal : ∀ χ, starRingEnd ℂ (d χ) = d χ := fun χ => conj_character_one basis χ
  have hnc : ¬ IsConj a x := fun h => by
    have := FourPointOrderFour.orderOf_eq_of_isConj h
    rw [ha4, hx2] at this
    norm_num at this
  have horth : ∀ p q : G, (p = 1 ∨ p = z) → (q = 1 ∨ q = z) →
      ∑ χ ∈ B₀, X χ (a * p) * X χ (x * q) = 0 := by
    intro p q hp hq
    have hpodd : Nat.Coprime 2 (orderOf p) := by
      rcases hp with rfl | rfl
      · rw [orderOf_one]; norm_num
      · exact Nat.coprime_two_left.mpr hzodd'
    have hqodd : Nat.Coprime 2 (orderOf q) := by
      rcases hq with rfl | rfl
      · rw [orderOf_one]; norm_num
      · exact Nat.coprime_two_left.mpr hzodd'
    have hap : Commute a p := by
      rcases hp with rfl | rfl
      · exact Commute.one_right a
      · exact hza.symm
    have hxq : Commute x q := by
      rcases hq with rfl | rfl
      · exact Commute.one_right x
      · exact hzx.symm
    have h := coefficientBlock_section_column_orthogonality basis ideal 2 principal a x p q 2 1
      (by rw [ha4]) (by rw [hx2]) hpodd hqodd hap hxq hnc
    rw [← h]
    refine Finset.sum_congr rfl fun χ hχ => ?_
    rw [← finite_character_conjugate_inverse]
    congr 1
    rcases hq with rfl | rfl
    · change X χ (x * 1) = starRingEnd ℂ (X χ (x * 1))
      rw [mul_one]
      exact (hAreal χ hχ).symm
    · exact (hBreal χ hχ).symm
  have hTA : ∑ χ ∈ B₀, T χ * Ax χ = 0 := by
    have h := horth 1 1 (Or.inl rfl) (Or.inl rfl)
    simp only [mul_one] at h
    exact h
  have hTB : ∑ χ ∈ B₀, T χ * Bx χ = 0 := by
    have h := horth 1 z (Or.inl rfl) (Or.inr rfl)
    simp only [mul_one] at h
    exact h
  have hUA : ∑ χ ∈ B₀, Ua χ * Ax χ = 0 := by
    have h := horth z 1 (Or.inr rfl) (Or.inl rfl)
    simp only [mul_one] at h
    exact h
  have hUB : ∑ χ ∈ B₀, Ua χ * Bx χ = 0 := horth z z (Or.inr rfl) (Or.inr rfl)
  have hv1 : ∀ χ, v χ 1 = evalRow (T χ) (Ua χ) := fun χ => rfl
  have hv2 : ∀ χ, v χ 2 = evalRow (Ax χ) (Bx χ) := fun χ => rfl
  have hv3 : ∀ χ, v χ 3 = evalRow (starRingEnd ℂ (T χ)) (starRingEnd ℂ (Ua χ)) := fun χ => by
    funext ℓ
    rw [← conj_evalRow]
    fin_cases ℓ <;> rfl
  have hvgram := central_rows_gram B₀ T Ua Ax Bx hAreal hBreal hTn hUn hTcU hA2 hB2 hAB hT2 hU2
    hTU hTA hTB hUA hUB (fun k χ => v χ k) hv1 hv2 hv3
  have hcases : ∀ c : ℂ, (c = 1 ∨ c = 0) → ∀ P Q : ℂ,
      Q + (P - Q) * c = (P + 2 * Q) / 3 + (P - Q) / 3 * (3 * c - 1) := by
    rintro c (rfl | rfl) P Q <;> ring
  have hc : ∀ (P : Prop) [Decidable P], ((if P then (1 : ℂ) else 0) = 1 ∨
      (if P then (1 : ℂ) else 0) = 0) := fun P _ => by
    by_cases hP : P
    · exact Or.inl (ite_eq_left hP)
    · exact Or.inr (ite_eq_right hP)
  have hsec : ∀ χ ∈ B₀, ∀ n' ∈ Finset.Icc 1 3, ∀ r : C, Odd (orderOf r) →
      X χ (a ^ n' * r) = v χ n' 0 + v χ n' 1 *
        (3 * (if (r : G) ∈ R₀ then 1 else 0) - 1) := by
    intro χ hχ n' hn' r hr
    rw [Finset.mem_Icc] at hn'
    obtain ⟨h1, h3⟩ := hn'
    interval_cases n'
    · rw [pow_one, hseca χ hχ r hr, hcases _ (hc _) (T χ) (Ua χ)]
      rfl
    · have hrN : (r : G) ∈ N := orderFourCentralizer_le 2 S e r.2
      have hrodd : Odd (orderOf (⟨r, hrN⟩ : N)) := by
        rw [Subgroup.orderOf_mk, Subgroup.orderOf_coe]
        exact hr
      have hmem : ((⟨r, hrN⟩ : N) ∈ R) ↔ (r : G) ∈ R₀ := by
        constructor
        · intro h
          exact ⟨⟨⟨r, hrN⟩, h, rfl⟩, r.2⟩
        · rintro ⟨hR, -⟩
          exact (Subgroup.mem_map_iff_mem N.subtype_injective).mp hR
      have h := hsecx χ hχ ⟨r, hrN⟩ hrodd
      rw [← hxa]
      change X χ (x * ((⟨r, hrN⟩ : N) : G)) = _
      rw [h, if_congr hmem rfl rfl, hcases _ (hc _) (Ax χ) (Bx χ)]
      rfl
    ·
      have ha3 : a ^ 3 = a⁻¹ := by
        rw [eq_inv_iff_mul_eq_one, ← pow_succ, show 3 + 1 = 2 ^ 2 by norm_num, ← ha4,
          pow_orderOf_eq_one]
      have hrinv : Odd (orderOf r⁻¹) := by rwa [orderOf_inv]
      have hra : (r : G) * a⁻¹ = a⁻¹ * r := (Commute.inv_right
        (show Commute (r : G) a from Subgroup.mem_centralizer_singleton_iff.mp r.2)).eq
      have hval : X χ (a ^ 3 * r) = starRingEnd ℂ (X χ (a * ((r⁻¹ : C) : G))) := by
        change (basis.representation χ).character (a ^ 3 * r) =
          starRingEnd ℂ ((basis.representation χ).character (a * ((r⁻¹ : C) : G)))
        rw [finite_character_conjugate_inverse, Subgroup.coe_inv, mul_inv_rev, inv_inv, ha3, hra]
      have hinv : (((r⁻¹ : C) : G) ∈ R₀) ↔ (r : G) ∈ R₀ := by
        rw [Subgroup.coe_inv, inv_mem_iff]
      rw [hval, hseca χ hχ r⁻¹ hrinv, if_congr hinv rfl rfl]
      rcases hc ((r : G) ∈ R₀) with hc' | hc'
      · rw [hc']
        simp only [v, show (3 : ℕ) ≠ 1 by decide, show (3 : ℕ) ≠ 2 by decide, ↓reduceIte,
          Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one, map_add,
          map_sub, map_mul, map_div₀, map_ofNat, map_one]
        ring
      · rw [hc']
        simp only [v, show (3 : ℕ) ≠ 1 by decide, show (3 : ℕ) ≠ 2 by decide, ↓reduceIte,
          Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one, map_add,
          map_sub, map_mul, map_div₀, map_ofNat, map_zero]
        ring
  have hfF : ∀ χ j ℓ, f χ j ℓ = fourierTransform 4 i (fun n' => v χ n' ℓ) j := by
    intro χ j ℓ
    simp only [f, fourierTransform]
    rw [show Finset.Icc 1 3 = Finset.Ico 1 4 by rfl]
    norm_num
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
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hbasisC, -⟩ :=
    four_point_order_four_centralizer_and_odd_restriction_bases hnonab 2 hn S e alpha ideal
      basisH principalH hprincipalH basisN principalN hprincipalN basisC principalC hprincipalC
  have hfint : ∀ χ ∈ B₀, ∀ j ∈ Finset.Icc 1 3, ∀ ℓ, ∃ k : ℤ, f χ j ℓ = k := by
    intro χ hχ j _ ℓ
    rw [hfF]
    refine fourierTransform_integral_of_oddRestrictionBasis basis ideal ha4 C rfl basisC
      principalC _ _ hbasisC hζ χ (v χ) (fun k hk y => ?_) j ℓ
    have hk' : k ∈ Finset.Icc 1 3 := by
      rw [Finset.mem_Ico] at hk
      rw [Finset.mem_Icc]
      norm_num at hk
      omega
    refine (hsec χ hχ k hk' y y.2).trans ?_
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one, mul_one]
    rfl
  have hfreal : ∀ χ ∈ B₀, ∀ j ∈ Finset.Icc 1 3, ∀ ℓ, starRingEnd ℂ (f χ j ℓ) = f χ j ℓ := by
    intro χ hχ j hj ℓ
    obtain ⟨k, hk⟩ := hfint χ hχ j hj ℓ
    rw [hk, map_intCast]
  have hfgram : ∀ j ∈ Finset.Icc 1 3, ∀ k ∈ Finset.Icc 1 3, ∀ ℓ t,
      ∑ χ ∈ B₀, f χ j ℓ * f χ k t = ((if j = k then 1 else 0) + 1) * M ℓ t / 4 := by
    intro j hj k hk ℓ t
    have hj' := Finset.mem_Icc.mp hj
    have hk' := Finset.mem_Icc.mp hk
    have hj4 : j < 2 ^ 2 := by norm_num; omega
    have hk4 : k < 2 ^ 2 := by norm_num; omega
    have h := fourierTransform_gram B₀ hζ (fun χ n' => v χ n' ℓ) (fun χ n' => v χ n' t)
      (M ℓ t : ℂ) (fun k hk h hh => hvgram k hk h hh ℓ t) hj'.1 hj4 hk'.1 hk4
    rw [show (2 ^ 2 : ℕ) = 4 by norm_num, Nat.cast_ofNat] at h
    rw [← h]
    refine Finset.sum_congr rfl fun χ hχ => ?_
    rw [← hfreal χ hχ j hj ℓ, hfF, hfF]
  refine ⟨hfint, hfgram, ?_, ?_, hsec, ?_, hstab, ?_, ?_⟩
  ·
    intro j ℓ
    have hlin : ∀ (P Q : basis.index → ℂ), ∑ χ ∈ B₀, d χ * P χ = 0 →
        ∑ χ ∈ B₀, d χ * Q χ = 0 → ∀ ℓ : Fin 2,
          ∑ χ ∈ B₀, d χ * evalRow (P χ) (Q χ) ℓ = 0 := by
      intro P Q hP hQ ℓ
      fin_cases ℓ
      · have h : ∑ χ ∈ B₀, d χ * evalRow (P χ) (Q χ) 0 =
            (∑ χ ∈ B₀, d χ * P χ + 2 * ∑ χ ∈ B₀, d χ * Q χ) / 3 := by
          rw [Finset.mul_sum, ← Finset.sum_add_distrib, Finset.sum_div]
          exact Finset.sum_congr rfl fun χ _ => by simp [evalRow]; ring
        show ∑ χ ∈ B₀, d χ * evalRow (P χ) (Q χ) 0 = 0
        rw [h, hP, hQ]
        norm_num
      · have h : ∑ χ ∈ B₀, d χ * evalRow (P χ) (Q χ) 1 =
            (∑ χ ∈ B₀, d χ * P χ - ∑ χ ∈ B₀, d χ * Q χ) / 3 := by
          rw [← Finset.sum_sub_distrib, Finset.sum_div]
          exact Finset.sum_congr rfl fun χ _ => by simp [evalRow]; ring
        show ∑ χ ∈ B₀, d χ * evalRow (P χ) (Q χ) 1 = 0
        rw [h, hP, hQ]
        norm_num
    have hconjd : ∀ P : basis.index → ℂ, ∑ χ ∈ B₀, d χ * P χ = 0 →
        ∑ χ ∈ B₀, d χ * starRingEnd ℂ (P χ) = 0 := fun P hP => by
      rw [← Complex.conj_conj (∑ χ ∈ B₀, d χ * starRingEnd ℂ (P χ)), map_sum]
      rw [Finset.sum_congr rfl fun χ _ => by rw [map_mul, Complex.conj_conj, hdreal]]
      rw [hP, map_zero]
    have hdv : ∀ n' ∈ Finset.Icc 1 3, ∑ χ ∈ B₀, d χ * v χ n' ℓ = 0 := by
      intro n' hn'
      rw [Finset.mem_Icc] at hn'
      obtain ⟨h1, h3⟩ := hn'
      interval_cases n'
      · exact hlin T Ua hdT hdU ℓ
      · exact hlin Ax Bx hdA hdB ℓ
      · rw [Finset.sum_congr rfl fun χ _ => by rw [hv3 χ]]
        exact hlin _ _ (hconjd T hdT) (hconjd Ua hdU) ℓ
    have h : ∑ χ ∈ B₀, d χ * f χ j ℓ = (1 / 4) * ∑ n' ∈ Finset.Icc 1 3,
        (i ^ (j * n') - 1) * ∑ χ ∈ B₀, d χ * v χ n' ℓ := by
      simp only [f, Finset.mul_sum]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun n' _ => Finset.sum_congr rfl fun χ _ => ?_
      ring
    rw [h, Finset.sum_eq_zero fun n' hn' => by rw [hdv n' hn', mul_zero], mul_zero]
  ·
    intro j hj
    have hj' := Finset.mem_Icc.mp hj
    have hj4 : j < 4 := by omega
    have hv0 : ∀ n' ∈ Finset.Ico 1 4, v principal n' 0 = 1 := by
      intro n' hn'
      rw [Finset.mem_Ico] at hn'
      obtain ⟨h1, h4⟩ := hn'
      interval_cases n'
      · change (T principal + 2 * Ua principal) / 3 = 1
        rw [hpT, hpU]
        norm_num
      · change (Ax principal + 2 * Bx principal) / 3 = 1
        rw [hpA, hpB]
        norm_num
      · change starRingEnd ℂ ((T principal + 2 * Ua principal) / 3) = 1
        rw [hpT, hpU]
        norm_num
    have hv1' : ∀ n' ∈ Finset.Ico 1 4, v principal n' 1 = 0 := by
      intro n' hn'
      rw [Finset.mem_Ico] at hn'
      obtain ⟨h1, h4⟩ := hn'
      interval_cases n'
      · change (T principal - Ua principal) / 3 = 0
        rw [hpT, hpU]
        norm_num
      · change (Ax principal - Bx principal) / 3 = 0
        rw [hpA, hpB]
        norm_num
      · change starRingEnd ℂ ((T principal - Ua principal) / 3) = 0
        rw [hpT, hpU]
        norm_num
    refine ⟨?_, ?_⟩
    · rw [hfF, fourierTransform_congr (w := fun _ => 1) hv0]
      exact fourierTransform_one hζ hj'.1 hj4
    · rw [hfF, fourierTransform_congr (w := fun _ => 0) hv1']
      exact fourierTransform_zero _ _ _
  ·
    intro χ hχ n' hn' ℓ
    have hn'' := Finset.mem_Icc.mp hn'
    have h := fourierTransform_inversion hζ (fun n' => v χ n' ℓ) hn''.1 (by norm_num; omega)
    rw [show (2 ^ 2 : ℕ) = 4 by norm_num] at h
    rw [← h, show Finset.Icc 1 3 = Finset.Ico 1 4 by rfl]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [hfF, zpow_neg_mul_eq_pow (by norm_num) hi4 (by omega), mul_comm]
  ·
    intro χ hχ χ' hχ' j hj ℓ
    have hj' := Finset.mem_Icc.mp hj
    have hTc : T χ' = starRingEnd ℂ (T χ) := hχ' a
    have hUc : Ua χ' = starRingEnd ℂ (Ua χ) := hχ' (a * z)
    have hAc : Ax χ' = Ax χ := (hχ' x).trans (hAreal χ hχ)
    have hBc : Bx χ' = Bx χ := (hχ' (x * z)).trans (hBreal χ hχ)
    have hw1 : v χ' 1 = v χ 3 := by rw [hv1, hv3, hTc, hUc]
    have hw2 : v χ' 2 = v χ 2 := by rw [hv2, hv2, hAc, hBc]
    have hw3 : v χ' 3 = v χ 1 := by rw [hv3, hv1, hTc, hUc, Complex.conj_conj, Complex.conj_conj]
    have hi3 : i ^ 3 = -i := by
      rw [pow_succ, hi]
      ring
    have hi6 : i ^ 6 = -1 := by
      rw [show (6 : ℕ) = 2 * 3 by rfl, pow_mul, hi]
      norm_num
    have hi9 : i ^ 9 = i := by
      rw [show (9 : ℕ) = 2 * 4 + 1 by rfl, pow_succ, pow_mul, hi]
      norm_num
    simp only [f, show Finset.Icc 1 3 = ({1, 2, 3} : Finset ℕ) by rfl]
    rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton,
      Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton, hw1, hw2,
      hw3]
    obtain ⟨h1, h3⟩ := hj'
    interval_cases j <;>
      simp only [Nat.reduceMul, Nat.reduceSub, pow_one, hi, hi3, hi4, hi6, hi9] <;> ring
  ·
    intro j hj k hk
    rw [hfgram j hj k hk 0 0]
    simp only [M]
    split_ifs <;> norm_num

end CFSG.Wreathed.FourPointCentralFourier

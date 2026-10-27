module

public import CFSG.CharacterTheory.Wreathed.ConditionalPrincipalSeriesValues
public import CFSG.CharacterTheory.Wreathed.ConditionalPrincipalSeriesBlocks
public import CFSG.CharacterTheory.Wreathed.CentralSL2.SemilinearPrincipalSeries
public import CFSG.CharacterTheory.Wreathed.ConditionalLinearAugmentationTwists
public import CFSG.CharacterTheory.Wreathed.ConditionalPrincipalSeriesCount

public noncomputable section

open scoped Classical

namespace CFSG.Wreathed

open Matrix CFSG.Wreathed.CyclicCentralSL2Extension CFSG.TwoRankLowerBound.Helpers
  CFSG.ComponentClassification.CatalogueSchreierLinearTwo CFSG.Wreathed.CentralSL2Abelianization
  CFSG.Wreathed.CentralSL2

section Auxiliary

theorem exists_two_pow_orderOf_of_forall_odd {K : Type*} [Group K] [Finite K] (η : K →* ℂˣ)
    (hη : ∀ c : K, Odd (orderOf c) → η c = 1) : ∃ k : ℕ, orderOf η = 2 ^ k := by
  set v := (Nat.card K).factorization 2 with hv
  have hN : Nat.card K ≠ 0 := Nat.card_pos.ne'
  have hodd : ∀ c : K, Odd (orderOf (c ^ (2 ^ v))) := by
    intro c
    have h1 : (c ^ (2 ^ v)) ^ (Nat.card K / 2 ^ v) = 1 := by
      rw [← pow_mul, Nat.mul_div_cancel' (Nat.ordProj_dvd _ _), pow_card_eq_one']
    have h2 : orderOf (c ^ (2 ^ v)) ∣ Nat.card K / 2 ^ v := orderOf_dvd_of_pow_eq_one h1
    have h3 : ¬ 2 ∣ Nat.card K / 2 ^ v := Nat.not_dvd_ordCompl Nat.prime_two hN
    rw [← Nat.not_even_iff_odd, even_iff_two_dvd]
    exact fun h => h3 (h.trans h2)
  have hpow : η ^ (2 ^ v) = 1 := MonoidHom.ext fun c => by
    rw [MonoidHom.pow_apply, ← map_pow, hη _ (hodd c), MonoidHom.one_apply]
  obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp (orderOf_dvd_of_pow_eq_one hpow)
  exact ⟨k, hk⟩

theorem eq_one_of_norm_le_one_of_sum_eq_card {ι : Type*} (s : Finset ι) (w : ι → ℂ)
    (hw : ∀ i ∈ s, ‖w i‖ ≤ 1) (hsum : ∑ i ∈ s, w i = s.card) : ∀ i ∈ s, w i = 1 := by
  have hre : ∀ i ∈ s, (w i).re ≤ 1 := fun i hi => (Complex.re_le_norm (w i)).trans (hw i hi)
  have hsumre : ∑ i ∈ s, (w i).re = ∑ i ∈ s, (1 : ℝ) := by
    rw [← Complex.re_sum, hsum]
    simp
  have heq := (Finset.sum_eq_sum_iff_of_le hre).mp hsumre
  intro i hi
  have h1 : (w i).re = 1 := heq i hi
  have hn : Complex.normSq (w i) ≤ 1 := by
    rw [Complex.normSq_eq_norm_sq]
    have h0 := norm_nonneg (w i)
    nlinarith [hw i hi]
  rw [Complex.normSq_apply, h1] at hn
  have h2 : (w i).im = 0 := by nlinarith [mul_self_nonneg (w i).im]
  exact Complex.ext (by simp [h1]) (by simp [h2])

theorem unitsField_inv_apply_apply {F : Type} [Field F] {Sigma : Subgroup (F ≃+* F)} (σ : Sigma)
    (c : Fˣ) :
    unitsField ((σ⁻¹ : Sigma) : F ≃+* F) (unitsField (σ : F ≃+* F) c) = c := by
  rw [← unitsField_mul_apply, ← Subgroup.coe_mul, inv_mul_cancel, Subgroup.coe_one]
  exact Units.ext rfl

end Auxiliary

section Model

variable {G : Type} [Group G] {n : ℕ} (hn : 2 ≤ n) {S : Sylow 2 G}
  {e : S ≃* Wreath (2 ^ n)} {F : Type} [Field F] [Fintype F]
  {Sigma : Subgroup (F ≃+* F)} {b : Fˣ} {hSigma : ∀ σ ∈ Sigma, σ (b : F) = b}
  {Ψ : SemilinearExtension F b (2 ^ n) (wreathModulus_pos n) (wreathModulus_even hn) Sigma
    hSigma ≃* centralizerOddCoreQuotient n S e}

local notation "W" => SemilinearExtension F b (2 ^ n) (wreathModulus_pos n)
  (wreathModulus_even hn) Sigma hSigma
local notation "H" => centralizerOddCoreQuotient n S e

theorem principalSeries_irreducible_H (hb : ¬ IsSquare b) (hd : Odd (Nat.card Sigma))
    {P : PrincipalSeriesParameter F b (2 ^ n)} (hP : P.1.1 ≠ 1)
    (ν : parameterStabilizer hSigma P →* ℂˣ) :
    (fun h => principalInduced (hm := wreathModulus_pos n) (heven := wreathModulus_even hn)
      hSigma P ν (Ψ.symm h)) ∈ BlocksIrr H ∧
    principalInduced (hm := wreathModulus_pos n) (heven := wreathModulus_even hn) hSigma P ν
        (Ψ.symm 1) = ((parameterStabilizer hSigma P).index : ℂ) * ((Nat.card F : ℂ) + 1) := by
  obtain ⟨hirr, hdeg⟩ := (principal_clifford (hm := wreathModulus_pos n)
    (heven := wreathModulus_even hn) hSigma hb hd hP).1 ν
  refine ⟨Semidihedral.Principal.comp_mem_blocksIrr Ψ.symm.toMonoidHom Ψ.symm.surjective hirr,
    ?_⟩
  rw [map_one]
  exact hdeg

theorem principalSeries_principal_iff_H [Finite G]
    {ρ : centralizerFullQuotient n hn S e →* coordinateE F} {p f : ℕ} (hp : p.Prime)
    (hpodd : p ≠ 2) (hdata : ConditionalCompatibleModelData n hn S e p f F Sigma b hSigma ρ Ψ)
    {ΦH : H → ℂ}
    (hΦ : ∀ h, ΦH h = (Nat.card {x : Omega F // ((ρ (centralizerFullQuotientMap n hn S e h) :
      coordinateE F) : Equiv.Perm (Omega F)) x = x} : ℂ) - 1)
    [Fintype H] (ideal : Ideal ComplexAlgebraicIntegers) [ideal.IsMaximal]
    [CharP (ComplexAlgebraicIntegers ⧸ ideal) 2] (basisH : FiniteIrreducibleCharacterBasis H)
    (principalH : basisH.index) (hprincipalH : (basisH.representation principalH).character = 1)
    {ε : ℤ} {M : Matrix (Fin 2) (Fin 2) ℤ}
    (hH : PrincipalRegularIntegralBasisData basisH ideal principalH ΦH ε (Nat.card F) M)
    {P : PrincipalSeriesParameter F b (2 ^ n)} (hP : P.1.1 ≠ 1)
    (ν : parameterStabilizer hSigma P →* ℂˣ) :
    (∃ l ∈ coefficientBlock basisH (localizedComplexIntegerRing ideal) principalH,
      (basisH.representation l).character = fun h => principalInduced
        (hm := wreathModulus_pos n) (heven := wreathModulus_even hn) hSigma P ν (Ψ.symm h)) ↔
      (∃ k : ℕ, orderOf P.1.1 = 2 ^ k) ∧ ν = 1 := by
  have hb := hdata.nonsquare
  have hd := hdata.sigma_odd
  have : Fact p.Prime := ⟨hp⟩
  have : CharP F p :=
    CFSG.Semidihedral.FixedFieldData.characteristic_of_prime_power_card F hp hdata.card
  have hq0 : (Nat.card F : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Nat.card_pos.ne'
  have hodd_symm : ∀ y : H, Odd (orderOf y) → Odd (orderOf (Ψ.symm y)) := fun y hy => by
    rw [MulEquiv.orderOf_eq]; exact hy
  have hodd_map : ∀ g : W, Odd (orderOf g) → Odd (orderOf (Ψ g)) := fun g hg => by
    rw [MulEquiv.orderOf_eq]; exact hg
  constructor
  · rintro ⟨l, hl, hchar⟩
    obtain ⟨a, c, hac, -, -, h1, -⟩ := hH.coefficients l hl
    have hval : ∀ g : W, Odd (orderOf g) → principalInduced (hm := wreathModulus_pos n)
        (heven := wreathModulus_even hn) hSigma P ν g =
          a + c * (fixedPointCount W (Omega F) g - 1) := by
      intro g hg
      have h := hac (Ψ g) (hodd_map g hg)
      simp only [hchar, MulEquiv.symm_apply_apply] at h
      rw [compatibleModel_augmentation hn hdata hΦ] at h
      exact h
    set u := (parameterStabilizer hSigma P).index with hu
    have hUodd : Odd (orderOf (SemidirectProduct.inl
        (unipotentElement F b (2 ^ n) (wreathModulus_pos n) (wreathModulus_even hn) 1) : W)) := by
      have hpow : (SemidirectProduct.inl
          (unipotentElement F b (2 ^ n) (wreathModulus_pos n) (wreathModulus_even hn) 1) : W) ^ p =
            1 := by
        rw [← map_pow, unipotentElement_pow, mul_one, CharP.cast_eq_zero, unipotentElement_zero,
          map_one]
      exact (hp.odd_of_ne_two hpodd).of_dvd_nat (orderOf_dvd_of_pow_eq_one hpow)
    have ha : (a : ℂ) = u := by
      have h := hval _ hUodd
      rw [principalInduced_unipotent hSigma hb hd hP ν one_ne_zero,
        fixedPointCount_inl_unipotent hSigma one_ne_zero, sub_self, mul_zero, add_zero] at h
      exact h.symm
    have hc : (c : ℂ) = u := by
      simp only [hchar] at h1
      rw [(principalSeries_irreducible_H hn hb hd hP ν).2, ha] at h1
      have h2 : ((c : ℂ) - u) * (Nat.card F : ℂ) = 0 := by linear_combination -h1
      exact sub_eq_zero.mp ((mul_eq_zero.mp h2).resolve_right hq0)
    obtain ⟨C, hC⟩ := CFSG.Wreathed.exists_leftCoset_reps (parameterStabilizer hSigma P)
    have hCcard : C.card = u := card_coset_reps _ C hC
    have htorus : ∀ c₁ : Fˣ, Odd (orderOf c₁) → c₁ ≠ 1 → ∀ σ ∈ C,
        (fieldParameter hSigma σ P).1.1 c₁ = 1 := by
      intro c₁ hc₁ hne
      have hsq : (c₁ : F) ^ 2 ≠ 1 := by
        intro h
        have h2 : c₁ ^ 2 = 1 := Units.ext (by rw [Units.val_pow_eq_pow_val, h, Units.val_one])
        have h3 : orderOf c₁ ∣ 2 := orderOf_dvd_of_pow_eq_one h2
        have h4 : orderOf c₁ = 1 := by
          rcases (Nat.dvd_prime Nat.prime_two).mp h3 with h5 | h5
          · exact h5
          · rw [h5] at hc₁
            exact absurd hc₁ (by decide)
        exact hne (orderOf_eq_one_iff.mp h4)
      have hTodd : Odd (orderOf (SemidirectProduct.inl
          (torusDiag F b (2 ^ n) (wreathModulus_pos n) (wreathModulus_even hn) c₁) : W)) := by
        have hpow : (SemidirectProduct.inl
            (torusDiag F b (2 ^ n) (wreathModulus_pos n) (wreathModulus_even hn) c₁) : W) ^
              orderOf c₁ = 1 := by
          rw [← map_pow, ← torusDiag_pow, pow_orderOf_eq_one, torusDiag_one, map_one]
        exact hc₁.of_dvd_nat (orderOf_dvd_of_pow_eq_one hpow)
      have h := hval _ hTodd
      rw [principalInduced_torusDiag hSigma hb hd hP ν C hC hsq,
        fixedPointCount_inl_torusDiag hSigma hb hsq, ha, hc] at h
      have hnorm : ∀ σ ∈ C, ‖(((fieldParameter hSigma σ P).1.1 c₁ : ℂˣ) : ℂ) +
          ((fieldParameter hSigma σ P).1.1 c₁⁻¹ : ℂ)‖ / 2 ≤ 1 := by
        intro σ _
        have hfin : ∀ w : Fˣ, ‖(((fieldParameter hSigma σ P).1.1 w : ℂˣ) : ℂ)‖ = 1 := by
          intro w
          apply Complex.norm_eq_one_of_pow_eq_one (n := Nat.card Fˣ)
          · rw [← Units.val_pow_eq_pow_val, ← map_pow, pow_card_eq_one', map_one, Units.val_one]
          · exact Nat.card_pos.ne'
        have := norm_add_le (((fieldParameter hSigma σ P).1.1 c₁ : ℂˣ) : ℂ)
          ((fieldParameter hSigma σ P).1.1 c₁⁻¹ : ℂ)
        rw [hfin, hfin] at this
        linarith
      have hsum : ∑ σ ∈ C, ((((fieldParameter hSigma σ P).1.1 c₁ : ℂˣ) : ℂ) +
          ((fieldParameter hSigma σ P).1.1 c₁⁻¹ : ℂ)) / 2 = C.card := by
        rw [← Finset.sum_div, h, hCcard]
        ring
      have hall := eq_one_of_norm_le_one_of_sum_eq_card C _ (fun σ hσ => by
        rw [norm_div, Complex.norm_ofNat]; exact hnorm σ hσ) hsum
      intro σ hσ
      have h2 := hall σ hσ
      have hfin : ‖(((fieldParameter hSigma σ P).1.1 c₁ : ℂˣ) : ℂ)‖ = 1 := by
        apply Complex.norm_eq_one_of_pow_eq_one (n := Nat.card Fˣ)
        · rw [← Units.val_pow_eq_pow_val, ← map_pow, pow_card_eq_one', map_one, Units.val_one]
        · exact Nat.card_pos.ne'
      have h3 : (((fieldParameter hSigma σ P).1.1 c₁ : ℂˣ) : ℂ) +
          ((fieldParameter hSigma σ P).1.1 c₁⁻¹ : ℂ) = 2 := by
        field_simp at h2
        linear_combination h2
      have h4 := eq_one_of_norm_le_one_of_sum_eq_card (Finset.univ : Finset (Fin 2))
        ![(((fieldParameter hSigma σ P).1.1 c₁ : ℂˣ) : ℂ),
          ((fieldParameter hSigma σ P).1.1 c₁⁻¹ : ℂ)]
        (fun i _ => by fin_cases i <;> simp [hfin]) (by simpa using h3) 0 (by simp)
      exact Units.ext (by simpa using h4)
    have hCne : C.Nonempty := by
      obtain ⟨σ, ⟨hσ, -⟩, -⟩ := hC ((1 : Sigma) : Sigma ⧸ parameterStabilizer hSigma P)
      exact ⟨σ, hσ⟩
    obtain ⟨σ, hσC⟩ := hCne
    have hηodd : ∀ c₁ : Fˣ, Odd (orderOf c₁) → P.1.1 c₁ = 1 := by
      intro c₁ hc₁
      by_cases h1 : c₁ = 1
      · rw [h1, map_one]
      · have hc₂ : Odd (orderOf (unitsField (σ : F ≃+* F) c₁)) := by
          rw [orderOf_injective (unitsField (σ : F ≃+* F)) (fun x y hxy => by
            have := congrArg (unitsField ((σ⁻¹ : Sigma) : F ≃+* F)) hxy
            rwa [unitsField_inv_apply_apply, unitsField_inv_apply_apply] at this)]
          exact hc₁
        have hne : unitsField (σ : F ≃+* F) c₁ ≠ 1 := by
          intro h
          apply h1
          have := congrArg (unitsField ((σ⁻¹ : Sigma) : F ≃+* F)) h
          rwa [unitsField_inv_apply_apply, map_one] at this
        have h2 := htorus _ hc₂ hne σ hσC
        rw [fieldParameter_fst, MonoidHom.comp_apply, unitsField_inv_apply_apply] at h2
        exact h2
    obtain ⟨k, hk⟩ := exists_two_pow_orderOf_of_forall_odd P.1.1 hηodd
    refine ⟨⟨k, hk⟩, ?_⟩
    have hStab := parameterStabilizer_eq_top_of_two_power hSigma hd P hk
    have hu1 : u = 1 := by rw [hu, hStab, Subgroup.index_top]
    obtain ⟨σ₀, hσ₀⟩ := @IsCyclic.exists_generator _ _ hdata.sigma_cyclic
    have hzodd : Odd (orderOf (SemidirectProduct.inr σ₀ : W)) := by
      rw [orderOf_injective _ SemidirectProduct.inr_injective]
      exact hd.of_dvd_nat (orderOf_dvd_natCard σ₀)
    have hz := hval _ hzodd
    rw [principalInduced_eq_mul_of_top hSigma hStab ν, principalInduced_one_odd hSigma hd rfl hk
      hzodd, ha, hc, hu1] at hz
    have hfix : fixedPointCount W (Omega F) (SemidirectProduct.inr σ₀) ≠ 0 := by
      change fixedPointCount W (Omega F) ⟨1, σ₀⟩ ≠ 0
      rw [fixedPointCount_field F b _ _ _ Sigma hSigma hp hdata.card σ₀]
      have hpos : (0 : ℝ) < 1 + (p : ℝ) ^ (f / orderOf σ₀) := by positivity
      intro h0
      have := congrArg Complex.re h0
      simp only [Complex.add_re, Complex.one_re, Complex.zero_re] at this
      rw [← Complex.ofReal_natCast, ← Complex.ofReal_pow, Complex.ofReal_re] at this
      linarith
    have hν0 : ν ⟨(SemidirectProduct.inr σ₀ : W).right, hStab ▸ Subgroup.mem_top _⟩ = 1 := by
      apply Units.ext
      have h2 : fixedPointCount W (Omega F) (SemidirectProduct.inr σ₀) *
          ((ν ⟨(SemidirectProduct.inr σ₀ : W).right, hStab ▸ Subgroup.mem_top _⟩ : ℂˣ) : ℂ) =
          fixedPointCount W (Omega F) (SemidirectProduct.inr σ₀) * 1 := by
        rw [hz]
        push_cast
        ring
      exact mul_left_cancel₀ hfix h2
    refine MonoidHom.ext fun τ => ?_
    obtain ⟨j, hj⟩ : ∃ j : ℕ, σ₀ ^ j = (τ : Sigma) :=
      (Submonoid.mem_powers_iff _ _).mp (mem_powers_iff_mem_zpowers.mpr (hσ₀ τ))
    have hτ : τ = (⟨(SemidirectProduct.inr σ₀ : W).right, hStab ▸ Subgroup.mem_top _⟩ :
        parameterStabilizer hSigma P) ^ j := by
      apply Subtype.ext
      rw [SubgroupClass.coe_pow]
      exact hj.symm
    rw [hτ, map_pow, hν0, one_pow, MonoidHom.one_apply]
  · rintro ⟨⟨k, hk⟩, rfl⟩
    obtain ⟨l, hl⟩ := CFSG.BlockBasics.exists_label_of_mem_irr basisH
      (principalSeries_irreducible_H hn hb hd hP 1).1
    refine ⟨l, ?_, hl⟩
    apply mem_coefficientBlock_of_odd_eq_span basisH ideal principalH
      (one_add_mem_span_principalBlock basisH ideal principalH hprincipalH hH.irreducible)
    intro y hy
    rw [hl]
    dsimp only
    rw [principalInduced_one_odd hSigma hd rfl hk (hodd_symm y hy), Pi.add_apply,
      Pi.one_apply, compatibleModel_augmentation_symm hn hdata hΦ]
    ring

theorem principalSeriesSet_eq_image [Finite G]
    {ρ : centralizerFullQuotient n hn S e →* coordinateE F} {p f : ℕ} (hp : p.Prime)
    (hpodd : p ≠ 2) (hdata : ConditionalCompatibleModelData n hn S e p f F Sigma b hSigma ρ Ψ)
    {ΦH : H → ℂ}
    (hΦ : ∀ h, ΦH h = (Nat.card {x : Omega F // ((ρ (centralizerFullQuotientMap n hn S e h) :
      coordinateE F) : Equiv.Perm (Omega F)) x = x} : ℂ) - 1)
    [Fintype H] (ideal : Ideal ComplexAlgebraicIntegers) [ideal.IsMaximal]
    [CharP (ComplexAlgebraicIntegers ⧸ ideal) 2] (basisH : FiniteIrreducibleCharacterBasis H)
    (principalH : basisH.index) (hprincipalH : (basisH.representation principalH).character = 1)
    {ε : ℤ} {M : Matrix (Fin 2) (Fin 2) ℤ}
    (hH : PrincipalRegularIntegralBasisData basisH ideal principalH ΦH ε (Nat.card F) M) :
    {θ : H → ℂ | ∃ x : (P : PrincipalSeriesParameter F b (2 ^ n)) ×
        (parameterStabilizer hSigma P →* ℂˣ), x.1.1.1 ≠ 1 ∧
        θ = (fun h => principalInduced (hm := wreathModulus_pos n)
          (heven := wreathModulus_even hn) hSigma x.1 x.2 (Ψ.symm h)) ∧
        ∃ l ∈ coefficientBlock basisH (localizedComplexIntegerRing ideal) principalH,
          (basisH.representation l).character = θ} =
      (fun P : PrincipalSeriesParameter F b (2 ^ n) => fun h => principalInduced
        (hm := wreathModulus_pos n) (heven := wreathModulus_even hn) hSigma P 1 (Ψ.symm h)) ''
        {P | (∃ k : ℕ, orderOf P.1.1 = 2 ^ k) ∧ P.1.1 ≠ 1} := by
  ext θ
  constructor
  · rintro ⟨⟨P, ν⟩, hP, rfl, hprin⟩
    obtain ⟨hk, hν⟩ := (principalSeries_principal_iff_H hn hp hpodd hdata hΦ ideal basisH
      principalH hprincipalH hH hP ν).mp hprin
    refine ⟨P, ⟨hk, hP⟩, ?_⟩
    dsimp only
    rw [hν]
  · rintro ⟨P, ⟨hk, hP⟩, rfl⟩
    exact ⟨⟨P, 1⟩, hP, rfl, (principalSeries_principal_iff_H hn hp hpodd hdata hΦ ideal basisH
      principalH hprincipalH hH hP 1).mpr ⟨hk, rfl⟩⟩

theorem ncard_principalSeriesSet [Finite G]
    {ρ : centralizerFullQuotient n hn S e →* coordinateE F} {p f : ℕ} (hp : p.Prime)
    (hpodd : p ≠ 2) (hdata : ConditionalCompatibleModelData n hn S e p f F Sigma b hSigma ρ Ψ)
    {ΦH : H → ℂ}
    (hΦ : ∀ h, ΦH h = (Nat.card {x : Omega F // ((ρ (centralizerFullQuotientMap n hn S e h) :
      coordinateE F) : Equiv.Perm (Omega F)) x = x} : ℂ) - 1)
    [Fintype H] (ideal : Ideal ComplexAlgebraicIntegers) [ideal.IsMaximal]
    [CharP (ComplexAlgebraicIntegers ⧸ ideal) 2] (basisH : FiniteIrreducibleCharacterBasis H)
    (principalH : basisH.index) (hprincipalH : (basisH.representation principalH).character = 1)
    {ε : ℤ} {M : Matrix (Fin 2) (Fin 2) ℤ}
    (hH : PrincipalRegularIntegralBasisData basisH ideal principalH ΦH ε (Nat.card F) M) :
    Set.ncard {θ : H → ℂ | ∃ x : (P : PrincipalSeriesParameter F b (2 ^ n)) ×
        (parameterStabilizer hSigma P →* ℂˣ), x.1.1.1 ≠ 1 ∧
        θ = (fun h => principalInduced (hm := wreathModulus_pos n)
          (heven := wreathModulus_even hn) hSigma x.1 x.2 (Ψ.symm h)) ∧
        ∃ l ∈ coefficientBlock basisH (localizedComplexIntegerRing ideal) principalH,
          (basisH.representation l).character = θ} =
      2 ^ n * (2 ^ (Nat.card F - 1).factorization 2 - 1) / 2 := by
  rw [principalSeriesSet_eq_image hn hp hpodd hdata hΦ ideal basisH principalH hprincipalH hH]
  have himg : (fun P : PrincipalSeriesParameter F b (2 ^ n) => fun h => principalInduced
      (hm := wreathModulus_pos n) (heven := wreathModulus_even hn) hSigma P 1 (Ψ.symm h)) =
      (fun φ : W → ℂ => fun h => φ (Ψ.symm h)) ∘ fun P => principalInduced
        (hm := wreathModulus_pos n) (heven := wreathModulus_even hn) hSigma P 1 := rfl
  have hinj : Function.Injective (fun φ : W → ℂ => fun h : H => φ (Ψ.symm h)) := by
    intro φ φ' h
    funext g
    have := congrFun h (Ψ g)
    simpa only [MulEquiv.symm_apply_apply] using this
  rw [himg, Set.image_comp, Set.ncard_image_of_injective _ hinj]
  exact ncard_principalInduced_two_power hSigma hdata.nonsquare hdata.sigma_odd

theorem principalSeries_two_power_values [Finite G]
    {ρ : centralizerFullQuotient n hn S e →* coordinateE F} {p f : ℕ}
    (hdata : ConditionalCompatibleModelData n hn S e p f F Sigma b hSigma ρ Ψ)
    {ΦH : H → ℂ}
    (hΦ : ∀ h, ΦH h = (Nat.card {x : Omega F // ((ρ (centralizerFullQuotientMap n hn S e h) :
      coordinateE F) : Equiv.Perm (Omega F)) x = x} : ℂ) - 1)
    {P : PrincipalSeriesParameter F b (2 ^ n)} {k : ℕ} (hk : orderOf P.1.1 = 2 ^ k)
    (hP : P.1.1 ≠ 1) :
    (∀ y : H, Odd (orderOf y) → principalInduced (hm := wreathModulus_pos n)
      (heven := wreathModulus_even hn) hSigma P 1 (Ψ.symm y) = 1 + ΦH y) ∧
    principalInduced (hm := wreathModulus_pos n) (heven := wreathModulus_even hn) hSigma P 1
      (Ψ.symm 1) = (Nat.card F : ℂ) + 1 := by
  have hd := hdata.sigma_odd
  refine ⟨fun y hy => ?_, ?_⟩
  · rw [principalInduced_one_odd hSigma hd rfl hk (by rw [MulEquiv.orderOf_eq]; exact hy),
      compatibleModel_augmentation_symm hn hdata hΦ]
    ring
  · rw [(principalSeries_irreducible_H hn hdata.nonsquare hd hP 1).2,
      parameterStabilizer_eq_top_of_two_power hSigma hd P hk, Subgroup.index_top, Nat.cast_one,
      one_mul]

theorem compatibleModel_complete_series [Finite G]
    {ρ : centralizerFullQuotient n hn S e →* coordinateE F} {p f : ℕ} (hp : p.Prime)
    (hpodd : p ≠ 2) (hdata : ConditionalCompatibleModelData n hn S e p f F Sigma b hSigma ρ Ψ)
    {ΦH : H → ℂ}
    (hΦ : ∀ h, ΦH h = (Nat.card {x : Omega F // ((ρ (centralizerFullQuotientMap n hn S e h) :
      coordinateE F) : Equiv.Perm (Omega F)) x = x} : ℂ) - 1)
    {σ₀ : Sigma} {hgen : ∀ σ : Sigma, σ ∈ Subgroup.zpowers σ₀} {ζm ζd : ℂ}
    {hζm : IsPrimitiveRoot ζm (2 ^ n)} {hζd : IsPrimitiveRoot ζd (Nat.card Sigma)}
    {lam Ξ : Fin (2 ^ n) → Fin (Nat.card Sigma) → H → ℂ}
    (hlam : ∀ r v h, lam r v h = (linearCharacter F b (2 ^ n) (wreathModulus_pos n)
      (wreathModulus_even hn) Sigma hSigma σ₀ hgen ζm ζd hζm hζd r v (Ψ.symm h) : ℂ))
    (hΞ : ∀ r v h, Ξ r v h = lam r v h * ΦH h) {θ : H → ℂ} (hθ : θ ∈ BlocksIrr H) :
    (∃ r v, θ = lam r v) ∨ (∃ r v, θ = Ξ r v) ∨
      (∃ (P : PrincipalSeriesParameter F b (2 ^ n)) (ν : parameterStabilizer hSigma P →* ℂˣ),
        P.1.1 ≠ 1 ∧ θ = fun h => principalInduced (hm := wreathModulus_pos n)
          (heven := wreathModulus_even hn) hSigma P ν (Ψ.symm h)) ∨
      ∃ u : ℕ, 0 < u ∧ u ∣ Nat.card Sigma ∧ θ 1 = (u : ℂ) * ((Nat.card F : ℂ) - 1) := by
  have : Fact p.Prime := ⟨hp⟩
  have : CharP F p :=
    CFSG.Semidihedral.FixedFieldData.characteristic_of_prime_power_card F hp hdata.card
  have hθW : θ ∘ Ψ.toMonoidHom ∈ BlocksIrr W :=
    Semidihedral.Principal.comp_mem_blocksIrr _ Ψ.surjective hθ
  have hθ1 : (θ ∘ Ψ.toMonoidHom) 1 = θ 1 := by
    change θ (Ψ 1) = θ 1
    rw [map_one]
  have hback : ∀ φ : W → ℂ, θ ∘ Ψ.toMonoidHom = φ → θ = φ ∘ Ψ.symm.toMonoidHom := by
    intro φ hφ
    rw [← hφ]
    funext h
    change θ h = θ (Ψ (Ψ.symm h))
    rw [MulEquiv.apply_symm_apply]
  obtain ⟨hcomplete, -⟩ := semilinear_complete_family (hm := wreathModulus_pos n)
    (heven := wreathModulus_even hn) hSigma σ₀ hgen ζm ζd hζm hζd (hp.odd_of_ne_two hpodd)
    hdata.nonsquare hdata.sigma_odd
  rw [hcomplete] at hθW
  rcases hθW with ((h1 | h2) | h3) | h4
  · obtain ⟨⟨r, v⟩, hrv⟩ := h1
    refine Or.inl ⟨r, v, ?_⟩
    rw [hback _ hrv.symm]
    funext h
    rw [hlam]
    rfl
  · obtain ⟨⟨r, v⟩, hrv⟩ := h2
    refine Or.inr (Or.inl ⟨r, v, ?_⟩)
    rw [hback _ hrv.symm]
    funext h
    rw [hΞ, hlam, compatibleModel_augmentation_symm hn hdata hΦ]
    rfl
  · obtain ⟨P, ρ', hP, hPρ⟩ := h3
    refine Or.inr (Or.inr (Or.inl ⟨P, ρ', hP, ?_⟩))
    rw [hback _ hPρ]
    rfl
  · obtain ⟨θ', hθ', hdeg⟩ := exists_degree_of_mem_aboveFamily hSigma (fun θ hθ => hθ.1) h4
    refine Or.inr (Or.inr (Or.inr ⟨(twistStabilizer hSigma θ').index,
      Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite, Subgroup.index_dvd_card _, ?_⟩))
    rw [← hθ1, hdeg, hθ'.2]

end Model

end CFSG.Wreathed

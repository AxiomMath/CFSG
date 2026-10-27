module

public import CFSG.CharacterTheory.Wreathed.ConditionalFourierColumnsSections
public import CFSG.CharacterTheory.Wreathed.ConditionalFourierColumnsPowers

public section

open scoped BigOperators Classical ComplexConjugate

namespace CFSG.Wreathed.ConditionalFourier

open CFSG.TwoRankLowerBound.Helpers CFSG.Semidihedral.Principal
  CFSG.ComponentClassification.CatalogueSchreierLinearTwo
  CFSG.Semidihedral.SemilinearOddExtensions CFSG.Wreathed.ActualProjectiveLayer
  CFSG.Wreathed.CyclicCentralSL2Extension

theorem conditional_global_central_section_integral_fourier_columns_of_localHyp
    {G : Type} [Group G] [Fintype G]
    (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G)
    (e : S ≃* Wreath (2 ^ n))
    (p f : ℕ) (hp : p.Prime) (hpodd : p ≠ 2) (hf : 1 ≤ f)
    (hloc : ConditionalLocalHyp n hn S e p f)
    [Fintype (centralizerOddCoreQuotient n S e)]
    (ideal : Ideal ComplexAlgebraicIntegers) [ideal.IsMaximal]
    [CharP (ComplexAlgebraicIntegers ⧸ ideal) 2]
    (basis : FiniteIrreducibleCharacterBasis G) (principal : basis.index)
    (hprincipal : (basis.representation principal).character = 1) :
    (∃ (F : Type) (_ : Field F) (_ : Finite F) (Sigma : Subgroup (F ≃+* F)) (b : Fˣ)
      (hSigma : ∀ σ ∈ Sigma, σ (b : F) = b)
      (ρ : centralizerFullQuotient n hn S e →* coordinateE F)
      (Ψ : SemilinearExtension F b (2 ^ n) (wreathModulus_pos n) (wreathModulus_even hn) Sigma
        hSigma ≃* centralizerOddCoreQuotient n S e),
      ConditionalCompatibleModelData n hn S e p f F Sigma b hSigma ρ Ψ) ∧
    ∀ (F : Type) [Field F] [Finite F] (Sigma : Subgroup (F ≃+* F)) (b : Fˣ)
      (hSigma : ∀ σ ∈ Sigma, σ (b : F) = b)
      (ρ : centralizerFullQuotient n hn S e →* coordinateE F)
      (Ψ : SemilinearExtension F b (2 ^ n) (wreathModulus_pos n) (wreathModulus_even hn) Sigma
        hSigma ≃* centralizerOddCoreQuotient n S e),
      ConditionalCompatibleModelData n hn S e p f F Sigma b hSigma ρ Ψ →
      let m : ℕ := 2 ^ n
      let a : G := wreathModelHom S e (Original.a (2 ^ n))
      let ΦH : centralizerOddCoreQuotient n S e → ℂ := fun h =>
        (Nat.card {x : Omega F // ((ρ (centralizerFullQuotientMap n hn S e h) : coordinateE F) :
          Equiv.Perm (Omega F)) x = x} : ℂ) - 1
      let ΦN : G → ℂ := fun g => if hg : g ∈ involutionCentralizer n S e then
        ΦH (centralizerOddCoreMap n S e ⟨g, hg⟩) else 0
      let ε : ℤ := if Nat.card F % 4 = 1 then 1 else -1
      let Bm : Matrix (Fin 2) (Fin 2) ℤ := !![4, -2; -2, ((m / 2 + 1 : ℕ) : ℤ)]
      let B₀ := coefficientBlock basis (localizedComplexIntegerRing ideal) principal
      ∀ ζ : ℂ, IsPrimitiveRoot ζ m →
      ∃ v : basis.index → ℕ → Fin 2 → ℂ,
        (∀ χ ∈ B₀, ∀ k ∈ Finset.Ico 1 m, ∀ ℓ, v χ k ℓ ∈ Algebra.adjoin ℤ ({ζ} : Set ℂ)) ∧
        IsCentralSectionRows basis ideal principal a m
          (fun k => centralSylowPowerCentralizer n S e k) ΦN ε v ∧
        (∀ χ ∈ B₀, ∀ k ∈ Finset.Ico 1 m, ∀ w : Fin 2 → ℂ,
          (∀ r ∈ centralSylowPowerCentralizer n S e k, Odd (orderOf r) →
            (basis.representation χ).character (a ^ k * r) = w 0 + w 1 * (1 + ε * ΦN r)) →
              w = v χ k) ∧
        (∀ k ∈ Finset.Ico 1 m, ∀ h ∈ Finset.Ico 1 m, ∀ ℓ t,
          ∑ χ ∈ B₀, conj (v χ k ℓ) * v χ h t =
            if k = h then (((m : ℤ) • Bm) ℓ t : ℂ) else 0) ∧
        (∀ k ∈ Finset.Ico 1 m, ∀ ℓ,
          ∑ χ ∈ B₀, (basis.representation χ).character 1 * v χ k ℓ = 0) ∧
        (∀ χ ∈ B₀, ∀ j ∈ Finset.Ico 1 m, ∀ ℓ,
          ∃ z : ℤ, fourierTransform m ζ (fun k => v χ k ℓ) j = z) ∧
        (∀ j ∈ Finset.Ico 1 m, ∀ t' ∈ Finset.Ico 1 m, ∀ ℓ t,
          ∑ χ ∈ B₀, fourierTransform m ζ (fun k => v χ k ℓ) j *
              fourierTransform m ζ (fun k => v χ k t) t' =
            ((if j = t' then 1 else 0) + 1) * (Bm ℓ t : ℂ)) ∧
        (∀ j ∈ Finset.Ico 1 m, ∀ ℓ,
          ∑ χ ∈ B₀, (basis.representation χ).character 1 *
            fourierTransform m ζ (fun k => v χ k ℓ) j = 0) ∧
        (∀ j ∈ Finset.Ico 1 m, fourierTransform m ζ (fun k => v principal k 0) j = -1 ∧
          fourierTransform m ζ (fun k => v principal k 1) j = 0) ∧
        (∀ χ ∈ B₀, ∀ k ∈ Finset.Ico 1 m, ∀ ℓ,
          v χ k ℓ = ∑ j ∈ Finset.Ico 1 m,
            ζ ^ (-((j : ℤ) * k)) * fourierTransform m ζ (fun k => v χ k ℓ) j) ∧
        (∀ j ∈ Finset.Ico 1 m,
          ∑ χ ∈ B₀, fourierTransform m ζ (fun k => v χ k 0) j ^ 2 = 8) ∧
        ∀ j ∈ Finset.Ico 1 m, ∀ t' ∈ Finset.Ico 1 m, j ≠ t' →
          ∑ χ ∈ B₀, fourierTransform m ζ (fun k => v χ k 0) j *
            fourierTransform m ζ (fun k => v χ k 0) t' = 4 := by
  refine ⟨hloc.modelData, ?_⟩
  intro F _ _ Sigma b hSigma ρ Ψ hdata m a ΦH ΦN ε Bm B₀ ζ hζ
  have hm4 : 4 ≤ m := by
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  have ha : orderOf a = m := orderOf_wreathModelHom_a n S e
  obtain ⟨basisH⟩ := finiteIrreducibleCharacterBasis_exists (G := centralizerOddCoreQuotient n S e)
  obtain ⟨principalH, hprincipalH⟩ := finiteIrreducibleCharacterBasis_contains_irreducible basisH
    (principalFiniteComplexRepresentation _) (principalFiniteComplexRepresentation_isIrreducible _)
  rw [principalFiniteComplexRepresentation_character] at hprincipalH
  obtain ⟨basisN⟩ := finiteIrreducibleCharacterBasis_exists (G := involutionCentralizer n S e)
  obtain ⟨principalN, hprincipalN⟩ := finiteIrreducibleCharacterBasis_contains_irreducible basisN
    (principalFiniteComplexRepresentation _) (principalFiniteComplexRepresentation_isIrreducible _)
  rw [principalFiniteComplexRepresentation_character] at hprincipalN
  have hreg := (conditional_actual_central_power_principal_regular_integral_bases_of_localHyp.{0} n
    hn S e p f hp hpodd hf hloc ideal basisH principalH hprincipalH basisN principalN
    hprincipalN).2 F Sigma ρ hdata.card hdata.sigma_odd hdata.rho_injective hdata.rho_layer
    hdata.rho_range
  have hpow := hreg.2.2.2
  have hCk : ∀ k : ℕ, centralSylowPowerCentralizer n S e k = Subgroup.centralizer {a ^ k} := by
    intro k
    simp only [centralSylowPowerCentralizer, zpow_natCast]
    rfl
  have hkdvd : ∀ k ∈ Finset.Ico 1 m, ¬ ((2 ^ n : ℕ) : ℤ) ∣ (k : ℤ) := by
    intro k hk hd
    rw [Finset.mem_Ico] at hk
    have h1 := Int.le_of_dvd (by omega) hd
    have h2 : 2 ^ n ≤ k := by exact_mod_cast h1
    omega
  have hdataK : ∀ k ∈ Finset.Ico 1 m,
      ∀ (localBasis : FiniteIrreducibleCharacterBasis (centralSylowPowerCentralizer n S e k))
        (localPrincipal : localBasis.index),
        (localBasis.representation localPrincipal).character = 1 →
        PrincipalRegularIntegralBasisData localBasis ideal localPrincipal (fun c => ΦN c) ε
          (Nat.card F) ((m : ℤ) • Bm) := by
    intro k hk lb l0 hl0
    have h := (hpow k (hkdvd k hk) lb l0 hl0).2.1
    convert h using 2
    · rename_i c
      have hcN : (c : G) ∈ involutionCentralizer n S e :=
        centralizer_zpow_le_involutionCentralizer n hn S e k (hkdvd k hk) c.2
      simp only [ΦN, dite_eq_left hcN]
      rfl
    · simp only [m]
      push_cast
      rfl
  have hΦreal : ∀ g, conj (ΦN g) = ΦN g := by
    intro g
    simp only [ΦN, ΦH]
    split_ifs
    · rw [map_sub, map_one, Complex.conj_natCast]
    · rw [map_zero]
  obtain ⟨v, hvint, hvrow, hvuniq, hvgram, hvdeg⟩ := section_rows_family basis ideal principal
    hprincipal ha ⟨n, rfl⟩ (fun k => centralSylowPowerCentralizer n S e k) hCk ΦN hΦreal ε
    (Nat.card F) ((m : ℤ) • Bm) hdataK
    (fun k hk h hh hkh => wreath_powers_eq_of_isConj n hn S e hk hh hkh) hζ
  have hrow' : ∀ χ ∈ B₀, ∀ k ∈ Finset.Ico 1 m, ∀ r ∈ centralSylowPowerCentralizer n S e k,
      Odd (orderOf r) →
        (basis.representation χ).character (a ^ k * r) =
          v χ k 0 + v χ k 1 * (1 + ε * ΦN r) := by
    intro χ hχ k hk r hr hodd
    exact hvrow χ hχ k hk ⟨r, hr⟩ (by rwa [Subgroup.orderOf_mk])
  have h1m : 1 ∈ Finset.Ico 1 m := Finset.mem_Ico.mpr ⟨le_rfl, by omega⟩
  obtain ⟨lb₁⟩ := finiteIrreducibleCharacterBasis_exists
    (G := centralSylowPowerCentralizer n S e (1 : ℕ))
  obtain ⟨l₁, hl₁⟩ := finiteIrreducibleCharacterBasis_contains_irreducible lb₁
    (principalFiniteComplexRepresentation _) (principalFiniteComplexRepresentation_isIrreducible _)
  rw [principalFiniteComplexRepresentation_character] at hl₁
  have hdata₁ := hdataK 1 h1m lb₁ l₁ hl₁
  have hC₁ : centralSylowPowerCentralizer n S e (1 : ℕ) = Subgroup.centralizer {a} := by
    rw [hCk 1, pow_one]
  have hint : ∀ χ ∈ B₀, ∀ j ∈ Finset.Ico 1 m, ∀ ℓ,
      ∃ z : ℤ, fourierTransform m ζ (fun k => v χ k ℓ) j = z := by
    intro χ hχ j hj ℓ
    rw [Finset.mem_Ico] at hj
    refine fourierTransform_integral_of_regular_basis basis ideal ha ⟨n, rfl⟩ _ hC₁ lb₁ l₁ hl₁
      (fun c => ΦN c) ε (Nat.card F) ((m : ℤ) • Bm) hdata₁ hζ χ (v χ) ?_ hj.1 hj.2 ℓ
    intro k hk y hy
    have hyk : (y : G) ∈ centralSylowPowerCentralizer n S e k := by
      have hmem : (y : G) ∈ Subgroup.centralizer {a} := hC₁ ▸ y.2
      rw [hCk k, Subgroup.mem_centralizer_singleton_iff]
      rw [Subgroup.mem_centralizer_singleton_iff] at hmem
      exact ((Commute.pow_left (show Commute a (y : G) from hmem.symm) k).eq).symm
    exact hrow' χ hχ k hk y hyk (by rwa [Subgroup.orderOf_coe])
  have hP : principal ∈ B₀ := coefficientBlock_self_mem basis _ principal
  have hProw : ∀ k ∈ Finset.Ico 1 m, v principal k 0 = 1 ∧ v principal k 1 = 0 := by
    intro k hk
    have h := hvuniq principal hP k hk ![1, 0] (fun r hr => by
      rw [hprincipal]
      simp)
    exact ⟨(congrFun h 0).symm, (congrFun h 1).symm⟩
  have hreal : ∀ χ ∈ B₀, ∀ j ∈ Finset.Ico 1 m, ∀ ℓ,
      conj (fourierTransform m ζ (fun k => v χ k ℓ) j) =
        fourierTransform m ζ (fun k => v χ k ℓ) j := by
    intro χ hχ j hj ℓ
    obtain ⟨z, hz⟩ := hint χ hχ j hj ℓ
    rw [hz, map_intCast]
  have hm0 : (m : ℂ) ≠ 0 := by exact_mod_cast (show m ≠ 0 by omega)
  have hfgram : ∀ j ∈ Finset.Ico 1 m, ∀ t' ∈ Finset.Ico 1 m, ∀ ℓ t,
      ∑ χ ∈ B₀, fourierTransform m ζ (fun k => v χ k ℓ) j *
          fourierTransform m ζ (fun k => v χ k t) t' =
        ((if j = t' then 1 else 0) + 1) * (Bm ℓ t : ℂ) := by
    intro j hj t' ht' ℓ t
    rw [Finset.mem_Ico] at hj ht'
    have h := fourierTransform_gram B₀ hζ (fun χ k => v χ k ℓ) (fun χ k => v χ k t)
      (((m : ℤ) • Bm) ℓ t : ℂ) (fun k hk h hh => hvgram k hk h hh ℓ t) hj.1 hj.2 ht'.1 ht'.2
    rw [← Finset.sum_congr rfl fun χ hχ => by
      rw [hreal χ hχ j (Finset.mem_Ico.mpr hj) ℓ]] at h
    rw [h]
    simp only [Matrix.smul_apply, smul_eq_mul]
    push_cast
    field_simp
  refine ⟨v, fun χ _ k hk ℓ => hvint χ k hk ℓ, hrow', fun χ hχ k hk w hw => hvuniq χ hχ k hk w
    (fun r hr => hw r r.2 (by rwa [Subgroup.orderOf_coe])), hvgram, hvdeg, hint, hfgram,
    ?_, ?_, ?_, ?_, ?_⟩
  · intro j hj ℓ
    unfold fourierTransform
    simp only [Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_eq_zero
    intro k hk
    have h := hvdeg k hk ℓ
    have h' : ∑ χ ∈ B₀, (basis.representation χ).character 1 * ((m : ℂ)⁻¹ *
        ((ζ ^ (j * k) - 1) * v χ k ℓ)) = (m : ℂ)⁻¹ * (ζ ^ (j * k) - 1) *
          ∑ χ ∈ B₀, (basis.representation χ).character 1 * v χ k ℓ := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun χ _ => ?_
      ring
    rw [h', h, mul_zero]
  · intro j hj
    rw [Finset.mem_Ico] at hj
    refine ⟨?_, ?_⟩
    · rw [fourierTransform_congr (w := fun _ => 1) (fun k hk => (hProw k hk).1) j]
      exact fourierTransform_one hζ hj.1 hj.2
    · rw [fourierTransform_congr (w := fun _ => 0) (fun k hk => (hProw k hk).2) j]
      exact fourierTransform_zero m ζ j
  · intro χ _ k hk ℓ
    rw [Finset.mem_Ico] at hk
    rw [← fourierTransform_inversion hζ (fun k => v χ k ℓ) hk.1 hk.2]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [zpow_neg_mul_eq_pow (by omega) hζ.pow_eq_one hk.2.le]
  · intro j hj
    have h := hfgram j hj j hj 0 0
    rw [ite_eq_left rfl] at h
    simp only [sq]
    rw [h]
    simp [Bm]
    norm_num
  · intro j hj t' ht' hjt
    have h := hfgram j hj t' ht' 0 0
    rw [ite_eq_right hjt] at h
    rw [h]
    simp [Bm]

theorem conditional_global_central_section_integral_fourier_columns
    {G : Type} [Group G] [Fintype G] [IsSimpleGroup G]
    (hnonab : ∃ a b : G, a * b ≠ b * a) (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G)
    (e : S ≃* Wreath (2 ^ n))
    (hfour : ¬ Nonempty (centralizerFullQuotient n hn S e ≃* Equiv.Perm (Fin 4)))
    (p f : ℕ) (hp : p.Prime) (hpodd : p ≠ 2) (hf : 1 ≤ f)
    (hmodel : CFSG.Assembly.LowTwoRank.StatedClassicalModel (centralizerSimpleLayer n hn S e)
      .PSL 2 p f)
    [Fintype (centralizerOddCoreQuotient n S e)]
    (ideal : Ideal ComplexAlgebraicIntegers) [ideal.IsMaximal]
    [CharP (ComplexAlgebraicIntegers ⧸ ideal) 2]
    (basis : FiniteIrreducibleCharacterBasis G) (principal : basis.index)
    (hprincipal : (basis.representation principal).character = 1) :
    (∃ (F : Type) (_ : Field F) (_ : Finite F) (Sigma : Subgroup (F ≃+* F)) (b : Fˣ)
      (hSigma : ∀ σ ∈ Sigma, σ (b : F) = b)
      (ρ : centralizerFullQuotient n hn S e →* coordinateE F)
      (Ψ : SemilinearExtension F b (2 ^ n) (wreathModulus_pos n) (wreathModulus_even hn) Sigma
        hSigma ≃* centralizerOddCoreQuotient n S e),
      ConditionalCompatibleModelData n hn S e p f F Sigma b hSigma ρ Ψ) ∧
    ∀ (F : Type) [Field F] [Finite F] (Sigma : Subgroup (F ≃+* F)) (b : Fˣ)
      (hSigma : ∀ σ ∈ Sigma, σ (b : F) = b)
      (ρ : centralizerFullQuotient n hn S e →* coordinateE F)
      (Ψ : SemilinearExtension F b (2 ^ n) (wreathModulus_pos n) (wreathModulus_even hn) Sigma
        hSigma ≃* centralizerOddCoreQuotient n S e),
      ConditionalCompatibleModelData n hn S e p f F Sigma b hSigma ρ Ψ →
      let m : ℕ := 2 ^ n
      let a : G := wreathModelHom S e (Original.a (2 ^ n))
      let ΦH : centralizerOddCoreQuotient n S e → ℂ := fun h =>
        (Nat.card {x : Omega F // ((ρ (centralizerFullQuotientMap n hn S e h) : coordinateE F) :
          Equiv.Perm (Omega F)) x = x} : ℂ) - 1
      let ΦN : G → ℂ := fun g => if hg : g ∈ involutionCentralizer n S e then
        ΦH (centralizerOddCoreMap n S e ⟨g, hg⟩) else 0
      let ε : ℤ := if Nat.card F % 4 = 1 then 1 else -1
      let Bm : Matrix (Fin 2) (Fin 2) ℤ := !![4, -2; -2, ((m / 2 + 1 : ℕ) : ℤ)]
      let B₀ := coefficientBlock basis (localizedComplexIntegerRing ideal) principal
      ∀ ζ : ℂ, IsPrimitiveRoot ζ m →
      ∃ v : basis.index → ℕ → Fin 2 → ℂ,
        (∀ χ ∈ B₀, ∀ k ∈ Finset.Ico 1 m, ∀ ℓ, v χ k ℓ ∈ Algebra.adjoin ℤ ({ζ} : Set ℂ)) ∧
        IsCentralSectionRows basis ideal principal a m
          (fun k => centralSylowPowerCentralizer n S e k) ΦN ε v ∧
        (∀ χ ∈ B₀, ∀ k ∈ Finset.Ico 1 m, ∀ w : Fin 2 → ℂ,
          (∀ r ∈ centralSylowPowerCentralizer n S e k, Odd (orderOf r) →
            (basis.representation χ).character (a ^ k * r) = w 0 + w 1 * (1 + ε * ΦN r)) →
              w = v χ k) ∧
        (∀ k ∈ Finset.Ico 1 m, ∀ h ∈ Finset.Ico 1 m, ∀ ℓ t,
          ∑ χ ∈ B₀, conj (v χ k ℓ) * v χ h t =
            if k = h then (((m : ℤ) • Bm) ℓ t : ℂ) else 0) ∧
        (∀ k ∈ Finset.Ico 1 m, ∀ ℓ,
          ∑ χ ∈ B₀, (basis.representation χ).character 1 * v χ k ℓ = 0) ∧
        (∀ χ ∈ B₀, ∀ j ∈ Finset.Ico 1 m, ∀ ℓ,
          ∃ z : ℤ, fourierTransform m ζ (fun k => v χ k ℓ) j = z) ∧
        (∀ j ∈ Finset.Ico 1 m, ∀ t' ∈ Finset.Ico 1 m, ∀ ℓ t,
          ∑ χ ∈ B₀, fourierTransform m ζ (fun k => v χ k ℓ) j *
              fourierTransform m ζ (fun k => v χ k t) t' =
            ((if j = t' then 1 else 0) + 1) * (Bm ℓ t : ℂ)) ∧
        (∀ j ∈ Finset.Ico 1 m, ∀ ℓ,
          ∑ χ ∈ B₀, (basis.representation χ).character 1 *
            fourierTransform m ζ (fun k => v χ k ℓ) j = 0) ∧
        (∀ j ∈ Finset.Ico 1 m, fourierTransform m ζ (fun k => v principal k 0) j = -1 ∧
          fourierTransform m ζ (fun k => v principal k 1) j = 0) ∧
        (∀ χ ∈ B₀, ∀ k ∈ Finset.Ico 1 m, ∀ ℓ,
          v χ k ℓ = ∑ j ∈ Finset.Ico 1 m,
            ζ ^ (-((j : ℤ) * k)) * fourierTransform m ζ (fun k => v χ k ℓ) j) ∧
        (∀ j ∈ Finset.Ico 1 m,
          ∑ χ ∈ B₀, fourierTransform m ζ (fun k => v χ k 0) j ^ 2 = 8) ∧
        ∀ j ∈ Finset.Ico 1 m, ∀ t' ∈ Finset.Ico 1 m, j ≠ t' →
          ∑ χ ∈ B₀, fourierTransform m ζ (fun k => v χ k 0) j *
            fourierTransform m ζ (fun k => v χ k 0) t' = 4 :=
  conditional_global_central_section_integral_fourier_columns_of_localHyp n hn S e p f hp hpodd hf
    (ConditionalLocalHyp.of_isSimpleGroup hnonab n hn S e hfour p f hp hpodd hf hmodel)
    ideal basis principal hprincipal

end CFSG.Wreathed.ConditionalFourier

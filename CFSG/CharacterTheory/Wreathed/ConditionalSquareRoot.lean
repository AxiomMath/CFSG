module

public import CFSG.CharacterTheory.Wreathed.ConditionalSquareRootRows
public import CFSG.CharacterTheory.Wreathed.ConditionalFourierColumns
public import CFSG.LocalAnalysis.LyonsUnitaryFour.OrderFifteen.PrincipalGram

public section

open scoped BigOperators Classical ComplexConjugate

namespace CFSG.Wreathed.ConditionalSquareRoot

open CFSG.TwoRankLowerBound.Helpers CFSG.Semidihedral.Principal
  CFSG.ComponentClassification.CatalogueSchreierLinearTwo
  CFSG.Semidihedral.SemilinearOddExtensions CFSG.Wreathed.ActualProjectiveLayer
  CFSG.Wreathed.CyclicCentralSL2Extension CFSG.Wreathed.ConditionalFourier
  CFSG.Wreathed.WreathCentralSquare CFSG.Wreathed.SquareRootSmallCharacterRigidity

theorem eq_of_mod_eq_zero_of_lt {s M : ℕ} (h : s % M = 0) (hpos : 0 < s) (hlt : s < 2 * M) :
    s = M := by
  have hdiv := Nat.div_add_mod s M
  rw [h, add_zero] at hdiv
  have hM : 0 < M := by omega
  have h1 : s / M < 2 := Nat.div_lt_of_lt_mul (by linarith)
  have h2 : 0 < s / M := by
    rcases Nat.eq_zero_or_pos (s / M) with h0 | h0
    · rw [h0, mul_zero] at hdiv
      omega
    · exact h0
  have h3 : s / M = 1 := by omega
  rw [h3, mul_one] at hdiv
  exact hdiv.symm

theorem conditional_square_root_cyclic_section_fourier_columns_and_parity_of_localHyp
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
      let M₀ : ℕ := m / 2
      let a : G := wreathModelHom S e (Original.a m)
      let x : G := wreathModelHom S e (Original.x m)
      let y : G := wreathModelHom S e (Original.s m * Original.z m)
      let D : Subgroup G := Subgroup.centralizer ({y} : Set G)
      let ΦH : centralizerOddCoreQuotient n S e → ℂ := fun h =>
        (Nat.card {x : Omega F // ((ρ (centralizerFullQuotientMap n hn S e h) : coordinateE F) :
          Equiv.Perm (Omega F)) x = x} : ℂ) - 1
      let ΦN : G → ℂ := fun g => if hg : g ∈ involutionCentralizer n S e then
        ΦH (centralizerOddCoreMap n S e ⟨g, hg⟩) else 0
      let ε : ℤ := if Nat.card F % 4 = 1 then 1 else -1
      let B₀ := coefficientBlock basis (localizedComplexIntegerRing ideal) principal
      orderOf y = 2 * m ∧ y ^ 2 = a ∧ y ^ m = x ∧
      (∃ P : Sylow 2 D, (P : Subgroup D).map D.subtype = Subgroup.zpowers y) ∧
      (∃ E : CFSG.oddCore D × Subgroup.zpowers y ≃* D,
        ∀ k z, (E (k, z) : G) = ((k : D) : G) * (z : G)) ∧
      (CFSG.oddCore D).index = 2 * m ∧
      (∀ h t : ℤ, Odd h → Odd t → (IsConj (y ^ h) (y ^ t) ↔ h ≡ t [ZMOD m])) ∧
      ∀ ζ : ℂ, IsPrimitiveRoot ζ m → ∀ η : ℂ, IsPrimitiveRoot η (2 * m) → η ^ 2 = ζ →
        let ν : basis.index → ℕ → ℕ := fun χ t =>
          Module.finrank ℂ (Module.End.eigenspace ((basis.representation χ).representation y)
            (η ^ t))
        let c : basis.index → ℕ → ℤ := fun χ r => (ν χ (2 * r) : ℤ) - ν χ (2 * r + m)
        let Y : ℕ → G → ℂ := fun r g =>
          ∑ χ ∈ B₀, (c χ r : ℂ) * (basis.representation χ).character g
        (∀ χ ∈ B₀, ∀ h : ℤ, Odd h → ∀ z ∈ D, Odd (orderOf z) →
          (basis.representation χ).character (y ^ h * z) =
              (basis.representation χ).character (y ^ h) ∧
            (basis.representation χ).character (y ^ h) =
              ∑ r ∈ Finset.range M₀, (c χ r : ℂ) * ζ ^ ((r : ℤ) * h)) ∧
        (∀ χ ∈ B₀, ∀ r < M₀, (c χ r : ℂ) = (M₀ : ℂ)⁻¹ * ∑ i ∈ Finset.range M₀,
          (basis.representation χ).character (y ^ (2 * i + 1)) *
            ζ ^ (-((r : ℤ) * (2 * i + 1)))) ∧
        (∀ r < M₀, ∀ t < M₀, BlocksInnerProduct (Y r) (Y t) = if r = t then 4 else 0) ∧
        (∀ r < M₀, ∀ t < M₀, ∑ χ ∈ B₀, c χ r * c χ t = if r = t then 4 else 0) ∧
        (∀ r < M₀, Y r 1 = 0) ∧
        c principal 0 = 1 ∧ (∀ r, 0 < r → r < M₀ → c principal r = 0) ∧
        (∀ r < M₀, (B₀.filter (fun χ => c χ r ≠ 0)).card = 4 ∧
          ∀ χ ∈ B₀, c χ r = 0 ∨ c χ r = 1 ∨ c χ r = -1) ∧
        (∃ v : basis.index → ℕ → Fin 2 → ℂ, IsCentralSectionRows basis ideal principal a m
          (fun k => centralSylowPowerCentralizer n S e k) ΦN ε v) ∧
        ∀ v : basis.index → ℕ → Fin 2 → ℂ, IsCentralSectionRows basis ideal principal a m
          (fun k => centralSylowPowerCentralizer n S e k) ΦN ε v →
        ∃ Fc : basis.index → ℕ → Fin 2 → ℤ,
          (∀ χ ∈ B₀, ∀ j ∈ Finset.Ico 1 m, ∀ ℓ,
            (Fc χ j ℓ : ℂ) = fourierTransform m ζ (fun k => v χ k ℓ) j) ∧
          (∀ r < M₀, ∀ j ∈ Finset.Ico 1 m, ∀ ℓ, ∑ χ ∈ B₀, c χ r * Fc χ j ℓ = 0) ∧
          (∀ j ∈ Finset.Ico 1 m, Odd j → ∀ χ ∈ B₀, Fc χ j 0 ≡ c χ 0 [ZMOD 2]) ∧
          (∀ j ∈ Finset.Ico 1 m, Even j → ∀ r, 1 ≤ r → r < M₀ → (r + j / 2) % M₀ = 0 →
            ∀ χ ∈ B₀, Fc χ j 0 ≡ c χ 0 + c χ r [ZMOD 2]) ∧
          (∀ j ∈ Finset.Ico 1 m, Odd j →
            (Finset.Ico 1 m).filter (fun j' => ∀ χ ∈ B₀, Fc χ j' 0 ≡ Fc χ j 0 [ZMOD 2]) =
              (Finset.Ico 1 m).filter Odd) ∧
          ((Finset.Ico 1 m).filter Odd).card = M₀ ∧
          (∀ j ∈ Finset.Ico 1 m, Even j → ∀ j' ∈ Finset.Ico 1 m, Even j' →
            ∀ r, 1 ≤ r → r < M₀ → (r + j / 2) % M₀ = 0 →
            ∀ r', 1 ≤ r' → r' < M₀ → (r' + j' / 2) % M₀ = 0 →
            ((∀ χ ∈ B₀, Fc χ j 0 ≡ Fc χ j' 0 [ZMOD 2]) ↔
              B₀.filter (fun χ => c χ r ≠ 0) = B₀.filter (fun χ => c χ r' ≠ 0))) ∧
          ∀ j ∈ Finset.Ico 1 m, Even j →
            ((Finset.Ico 1 m).filter
              (fun j' => ∀ χ ∈ B₀, Fc χ j' 0 ≡ Fc χ j 0 [ZMOD 2])).card ≤ 3 := by
  refine ⟨hloc.modelData, ?_⟩
  intro F _ _ Sigma b hSigma ρ Ψ hdata m M₀ a x y D ΦH ΦN ε B₀
  have hm4 : 4 ≤ m := by
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  have hm2 : 2 * M₀ = m := by
    obtain ⟨k, hk⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
    simp only [M₀, m]
    rw [hk, pow_succ, Nat.mul_div_cancel _ (by norm_num), mul_comm]
  have hyroot : y = actualRoot S e := rfl
  obtain ⟨hysq, hym, hyord, -, -, hKindex, E, hE, -⟩ := original_root_centralizer_product n hn S e
  refine ⟨hyord, hysq, hym, ?_, ⟨E, hE⟩, hKindex,
    fun h t hh ht => actualRoot_odd_zpow_isConj_iff n hn S e hh ht, ?_⟩
  · obtain ⟨P, hP⟩ := exists_cyclic_centralizer_sylow n hn S e y hyord
    refine ⟨P, ?_⟩
    rw [hP, MonoidHom.map_zpowers]
    rfl
  intro ζ hζ η hη hηζ ν c Y
  have hcdef : ∀ χ r, c χ r =
      signedEvenEigenmultiplicity (basis.representation χ) (actualRoot S e) η (2 ^ n) r :=
    fun _ _ => rfl
  have hνdef : ∀ χ t, ν χ t = cyclicEigenmultiplicity (basis.representation χ) (actualRoot S e)
      η t := fun _ _ => rfl
  obtain ⟨hexp, hcgram, hcdeg, hc0, hcr, hfour'⟩ :=
    actualRoot_signed_even_columns n hn S e basis ideal principal hprincipal hη
  have hdegpos : ∀ χ ∈ B₀, 0 < (Module.finrank ℂ (basis.representation χ).vector : ℤ) := by
    intro χ _
    have h := irreducible_character_degree_ne_zero (basis.representation χ) (basis.irreducible χ)
    rw [FiniteComplexRepresentation.character, Representation.char_one] at h
    have h' : Module.finrank ℂ (basis.representation χ).vector ≠ 0 := by exact_mod_cast h
    omega
  have hcdegZ : ∀ r < M₀, ∑ χ ∈ B₀,
      c χ r * (Module.finrank ℂ (basis.representation χ).vector : ℤ) = 0 := by
    intro r hr
    have h := hcdeg r hr
    apply Int.cast_injective (α := ℂ)
    rw [Int.cast_sum, Int.cast_zero, ← h]
    refine Finset.sum_congr rfl fun χ _ => ?_
    rw [Int.cast_mul, Int.cast_natCast, FiniteComplexRepresentation.character,
      Representation.char_one]
    rfl
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
  let Bm : Matrix (Fin 2) (Fin 2) ℤ := !![4, -2; -2, ((m / 2 + 1 : ℕ) : ℤ)]
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
  have h1m : 1 ∈ Finset.Ico 1 m := Finset.mem_Ico.mpr ⟨le_rfl, by omega⟩
  obtain ⟨lb₁⟩ := finiteIrreducibleCharacterBasis_exists
    (G := centralSylowPowerCentralizer n S e (1 : ℕ))
  obtain ⟨l₁, hl₁⟩ := finiteIrreducibleCharacterBasis_contains_irreducible lb₁
    (principalFiniteComplexRepresentation _) (principalFiniteComplexRepresentation_isIrreducible _)
  rw [principalFiniteComplexRepresentation_character] at hl₁
  have hdata₁ := hdataK 1 h1m lb₁ l₁ hl₁
  have hΦ1 : ΦN 1 = Nat.card F := hdata₁.degree
  have hC₁ : centralSylowPowerCentralizer n S e (1 : ℕ) = Subgroup.centralizer {a} := by
    rw [hCk 1, pow_one]
  have hqodd : Odd (Nat.card F) := by
    rw [hdata.card]
    exact (hp.odd_of_ne_two hpodd).pow
  have hε : ε = 1 ∨ ε = -1 := by
    simp only [ε]
    split_ifs
    · exact Or.inl rfl
    · exact Or.inr rfl
  refine ⟨?_, ?_, ?_, ?_, ?_, hc0, hcr, hfour', ?_, ?_⟩
  ·
    intro χ hχ h hh z hz hzodd
    obtain ⟨h1, h2⟩ := hexp χ hχ h hh z hz hzodd
    refine ⟨h1, ?_⟩
    rw [← hηζ]
    exact h2
  ·
    intro χ _ r _
    rw [hcdef, actualRoot_signed_even_inversion n hn S e (basis.representation χ) hη r, hηζ]
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [mul_comm, inv_pow, ← zpow_natCast ζ, ← zpow_neg]
    congr 2
  ·
    intro r hr t ht
    have h := CFSG.LyonsUnitaryFour.blocksInnerProduct_sum_sum basis B₀ (fun χ => (c χ r : ℂ))
      (fun χ => (c χ t : ℂ))
    simp only [map_intCast] at h
    change BlocksInnerProduct
      (fun g => ∑ χ ∈ B₀, (c χ r : ℂ) * (basis.representation χ).character g)
      (fun g => ∑ χ ∈ B₀, (c χ t : ℂ) * (basis.representation χ).character g) = _
    rw [h]
    have h2 := hcgram r hr t ht
    have h3 : (∑ χ ∈ B₀, (c χ r : ℂ) * (c χ t : ℂ)) = ((∑ χ ∈ B₀, c χ r * c χ t : ℤ) : ℂ) := by
      push_cast
      rfl
    rw [h3]
    change ((∑ χ ∈ B₀, signedEvenEigenmultiplicity (basis.representation χ) (actualRoot S e) η
      (2 ^ n) r * signedEvenEigenmultiplicity (basis.representation χ) (actualRoot S e) η
        (2 ^ n) t : ℤ) : ℂ) = _
    rw [h2]
    split_ifs <;> simp
  · exact hcgram
  · intro r hr
    exact hcdeg r hr
  ·
    obtain ⟨v, -, hv, -⟩ :=
      (conditional_global_central_section_integral_fourier_columns_of_localHyp n hn S e p f hp
        hpodd hf hloc ideal basis principal hprincipal).2 F Sigma b hSigma ρ Ψ
      hdata ζ hζ
    exact ⟨v, hv⟩
  intro v hv
  have hint : ∀ χ ∈ B₀, ∀ j ∈ Finset.Ico 1 m, ∀ ℓ,
      ∃ z : ℤ, fourierTransform m ζ (fun k => v χ k ℓ) j = z := by
    intro χ hχ j hj ℓ
    rw [Finset.mem_Ico] at hj
    refine fourierTransform_integral_of_regular_basis basis ideal (orderOf_wreathModelHom_a n S e)
      ⟨n, rfl⟩ _ hC₁ lb₁ l₁ hl₁ (fun c => ΦN c) ε (Nat.card F) ((m : ℤ) • Bm) hdata₁ hζ χ (v χ) ?_
      hj.1 hj.2 ℓ
    intro k hk z hz
    have hzk : (z : G) ∈ centralSylowPowerCentralizer n S e k := by
      have hmem : (z : G) ∈ Subgroup.centralizer {a} := hC₁ ▸ z.2
      rw [hCk k, Subgroup.mem_centralizer_singleton_iff]
      rw [Subgroup.mem_centralizer_singleton_iff] at hmem
      exact ((Commute.pow_left (show Commute a (z : G) from hmem.symm) k).eq).symm
    exact hv χ hχ k hk z hzk (by rwa [Subgroup.orderOf_coe])
  let Fc : basis.index → ℕ → Fin 2 → ℤ := fun χ j ℓ =>
    if h : χ ∈ B₀ ∧ j ∈ Finset.Ico 1 m then Classical.choose (hint χ h.1 j h.2 ℓ) else 0
  have hFc : ∀ χ ∈ B₀, ∀ j ∈ Finset.Ico 1 m, ∀ ℓ,
      (Fc χ j ℓ : ℂ) = fourierTransform m ζ (fun k => v χ k ℓ) j := by
    intro χ hχ j hj ℓ
    simp only [Fc, dite_eq_left (⟨hχ, hj⟩ : χ ∈ B₀ ∧ j ∈ Finset.Ico 1 m)]
    exact (Classical.choose_spec (hint χ hχ j hj ℓ)).symm
  have hpar : ∀ χ ∈ B₀, ∀ j ∈ Finset.Ico 1 m,
      Fc χ j 0 ≡ (ν χ (m - j) : ℤ) + ν χ (2 * m - j) - ν χ 0 - ν χ m [ZMOD 2] := by
    intro χ hχ j hj
    have h := fourier_rows_at_one_eigen n hn S e basis ideal principal
      (fun k => centralSylowPowerCentralizer n S e k) ΦN ε (Nat.card F) hΦ1 v hv hη hηζ hχ hj
    rw [← hFc χ hχ j hj 0, ← hFc χ hχ j hj 1] at h
    have h' : (Fc χ j 0 : ℂ) + (1 + (ε : ℂ) * (Nat.card F : ℂ)) * (Fc χ j 1 : ℂ) =
        (((ν χ (m - j) : ℤ) + ν χ (2 * m - j) - ν χ 0 - ν χ m : ℤ) : ℂ) := h
    have hZ : Fc χ j 0 + (1 + ε * (Nat.card F : ℤ)) * Fc χ j 1 =
        (ν χ (m - j) : ℤ) + ν χ (2 * m - j) - ν χ 0 - ν χ m := by
      exact_mod_cast h'
    exact modEq_two_of_add_mul hqodd hε hZ
  have hcancel : ∀ χ, ∀ t, Odd t → ν χ t = ν χ (t + m) := fun χ t ht =>
    actual_root_odd_eigenmultiplicity_cancellation n hn S e (basis.representation χ) η hη t ht
  have hc0def : ∀ χ, c χ 0 = (ν χ 0 : ℤ) - ν χ m := by
    intro χ
    simp only [c, mul_zero, zero_add]
  have hodd : ∀ j ∈ Finset.Ico 1 m, Odd j → ∀ χ ∈ B₀, Fc χ j 0 ≡ c χ 0 [ZMOD 2] := by
    intro j hj hjo χ hχ
    have hj' := Finset.mem_Ico.mp hj
    have h := hpar χ hχ j hj
    have hmj : Odd (m - j) := by
      have hme : Even m := (Nat.even_pow' (by omega)).mpr even_two
      exact Nat.Even.sub_odd (by omega) hme hjo
    have hcan := hcancel χ (m - j) hmj
    rw [show m - j + m = 2 * m - j by omega] at hcan
    rw [hc0def χ]
    rw [← hcan] at h
    unfold Int.ModEq at h ⊢
    omega
  have heven : ∀ j ∈ Finset.Ico 1 m, Even j → ∀ χ ∈ B₀,
      Fc χ j 0 ≡ c χ 0 + c χ (M₀ - j / 2) [ZMOD 2] := by
    intro j hj hje χ hχ
    have hj' := Finset.mem_Ico.mp hj
    have h := hpar χ hχ j hj
    obtain ⟨k, rfl⟩ := hje
    have h1 : 2 * (M₀ - (k + k) / 2) = m - (k + k) := by omega
    have h2 : 2 * (M₀ - (k + k) / 2) + m = 2 * m - (k + k) := by omega
    have hcr : c χ (M₀ - (k + k) / 2) = (ν χ (m - (k + k)) : ℤ) - ν χ (2 * m - (k + k)) := by
      show (ν χ (2 * (M₀ - (k + k) / 2)) : ℤ) - ν χ (2 * (M₀ - (k + k) / 2) + m) = _
      rw [h2, h1]
    rw [hc0def χ, hcr]
    unfold Int.ModEq at h ⊢
    omega
  have hcgram' : ∀ r < M₀, ∀ t < M₀, ∑ χ ∈ B₀, c χ r * c χ t = if r = t then 4 else 0 := hcgram
  rw [← hm2] at hodd heven
  obtain ⟨hcls1, hcls2, hcls3, hcls4⟩ := parity_classes B₀ c
    (fun χ => (Module.finrank ℂ (basis.representation χ).vector : ℤ)) hdegpos hcgram' hcdegZ
    hfour' (fun χ j => Fc χ j 0) hodd heven
  rw [hm2] at hcls1 hcls2 hcls3 hcls4 hodd heven
  have hrj : ∀ j ∈ Finset.Ico 1 m, Even j → ∀ r, 1 ≤ r → r < M₀ → (r + j / 2) % M₀ = 0 →
      r = M₀ - j / 2 := by
    intro j hj hje r hr1 hrM hmod
    have hj' := Finset.mem_Ico.mp hj
    obtain ⟨k, rfl⟩ := hje
    have := eq_of_mod_eq_zero_of_lt hmod (by omega) (by omega)
    omega
  refine ⟨Fc, hFc, ?_, hodd, ?_, fun j hj hjo => by convert hcls1 j hj hjo, hcls2, ?_,
    fun j hj hje => by convert hcls4 j hj hje⟩
  ·
    intro r _ j _ ℓ
    have h := signed_even_fourier_orthogonal n hn S e basis ideal principal hprincipal
      (fun k => centralSylowPowerCentralizer n S e k) hCk ΦN hΦreal ε (Nat.card F)
      ((m : ℤ) • Bm) hdataK v hv hη ζ (fun χ => Fc χ j ℓ) ℓ
      (fun χ hχ => hFc χ hχ j ‹j ∈ Finset.Ico 1 m› ℓ) r
    exact h
  · intro j hj hje r hr1 hrM hmod χ hχ
    rw [hrj j hj hje r hr1 hrM hmod]
    exact heven j hj hje χ hχ
  · intro j hj hje j' hj' hje' r hr1 hrM hmod r' hr1' hrM' hmod'
    rw [hrj j hj hje r hr1 hrM hmod, hrj j' hj' hje' r' hr1' hrM' hmod']
    exact hcls3 j hj hje j' hj' hje'

theorem conditional_square_root_cyclic_section_fourier_columns_and_parity
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
      let M₀ : ℕ := m / 2
      let a : G := wreathModelHom S e (Original.a m)
      let x : G := wreathModelHom S e (Original.x m)
      let y : G := wreathModelHom S e (Original.s m * Original.z m)
      let D : Subgroup G := Subgroup.centralizer ({y} : Set G)
      let ΦH : centralizerOddCoreQuotient n S e → ℂ := fun h =>
        (Nat.card {x : Omega F // ((ρ (centralizerFullQuotientMap n hn S e h) : coordinateE F) :
          Equiv.Perm (Omega F)) x = x} : ℂ) - 1
      let ΦN : G → ℂ := fun g => if hg : g ∈ involutionCentralizer n S e then
        ΦH (centralizerOddCoreMap n S e ⟨g, hg⟩) else 0
      let ε : ℤ := if Nat.card F % 4 = 1 then 1 else -1
      let B₀ := coefficientBlock basis (localizedComplexIntegerRing ideal) principal
      orderOf y = 2 * m ∧ y ^ 2 = a ∧ y ^ m = x ∧
      (∃ P : Sylow 2 D, (P : Subgroup D).map D.subtype = Subgroup.zpowers y) ∧
      (∃ E : CFSG.oddCore D × Subgroup.zpowers y ≃* D,
        ∀ k z, (E (k, z) : G) = ((k : D) : G) * (z : G)) ∧
      (CFSG.oddCore D).index = 2 * m ∧
      (∀ h t : ℤ, Odd h → Odd t → (IsConj (y ^ h) (y ^ t) ↔ h ≡ t [ZMOD m])) ∧
      ∀ ζ : ℂ, IsPrimitiveRoot ζ m → ∀ η : ℂ, IsPrimitiveRoot η (2 * m) → η ^ 2 = ζ →
        let ν : basis.index → ℕ → ℕ := fun χ t =>
          Module.finrank ℂ (Module.End.eigenspace ((basis.representation χ).representation y)
            (η ^ t))
        let c : basis.index → ℕ → ℤ := fun χ r => (ν χ (2 * r) : ℤ) - ν χ (2 * r + m)
        let Y : ℕ → G → ℂ := fun r g =>
          ∑ χ ∈ B₀, (c χ r : ℂ) * (basis.representation χ).character g
        (∀ χ ∈ B₀, ∀ h : ℤ, Odd h → ∀ z ∈ D, Odd (orderOf z) →
          (basis.representation χ).character (y ^ h * z) =
              (basis.representation χ).character (y ^ h) ∧
            (basis.representation χ).character (y ^ h) =
              ∑ r ∈ Finset.range M₀, (c χ r : ℂ) * ζ ^ ((r : ℤ) * h)) ∧
        (∀ χ ∈ B₀, ∀ r < M₀, (c χ r : ℂ) = (M₀ : ℂ)⁻¹ * ∑ i ∈ Finset.range M₀,
          (basis.representation χ).character (y ^ (2 * i + 1)) *
            ζ ^ (-((r : ℤ) * (2 * i + 1)))) ∧
        (∀ r < M₀, ∀ t < M₀, BlocksInnerProduct (Y r) (Y t) = if r = t then 4 else 0) ∧
        (∀ r < M₀, ∀ t < M₀, ∑ χ ∈ B₀, c χ r * c χ t = if r = t then 4 else 0) ∧
        (∀ r < M₀, Y r 1 = 0) ∧
        c principal 0 = 1 ∧ (∀ r, 0 < r → r < M₀ → c principal r = 0) ∧
        (∀ r < M₀, (B₀.filter (fun χ => c χ r ≠ 0)).card = 4 ∧
          ∀ χ ∈ B₀, c χ r = 0 ∨ c χ r = 1 ∨ c χ r = -1) ∧
        (∃ v : basis.index → ℕ → Fin 2 → ℂ, IsCentralSectionRows basis ideal principal a m
          (fun k => centralSylowPowerCentralizer n S e k) ΦN ε v) ∧
        ∀ v : basis.index → ℕ → Fin 2 → ℂ, IsCentralSectionRows basis ideal principal a m
          (fun k => centralSylowPowerCentralizer n S e k) ΦN ε v →
        ∃ Fc : basis.index → ℕ → Fin 2 → ℤ,
          (∀ χ ∈ B₀, ∀ j ∈ Finset.Ico 1 m, ∀ ℓ,
            (Fc χ j ℓ : ℂ) = fourierTransform m ζ (fun k => v χ k ℓ) j) ∧
          (∀ r < M₀, ∀ j ∈ Finset.Ico 1 m, ∀ ℓ, ∑ χ ∈ B₀, c χ r * Fc χ j ℓ = 0) ∧
          (∀ j ∈ Finset.Ico 1 m, Odd j → ∀ χ ∈ B₀, Fc χ j 0 ≡ c χ 0 [ZMOD 2]) ∧
          (∀ j ∈ Finset.Ico 1 m, Even j → ∀ r, 1 ≤ r → r < M₀ → (r + j / 2) % M₀ = 0 →
            ∀ χ ∈ B₀, Fc χ j 0 ≡ c χ 0 + c χ r [ZMOD 2]) ∧
          (∀ j ∈ Finset.Ico 1 m, Odd j →
            (Finset.Ico 1 m).filter (fun j' => ∀ χ ∈ B₀, Fc χ j' 0 ≡ Fc χ j 0 [ZMOD 2]) =
              (Finset.Ico 1 m).filter Odd) ∧
          ((Finset.Ico 1 m).filter Odd).card = M₀ ∧
          (∀ j ∈ Finset.Ico 1 m, Even j → ∀ j' ∈ Finset.Ico 1 m, Even j' →
            ∀ r, 1 ≤ r → r < M₀ → (r + j / 2) % M₀ = 0 →
            ∀ r', 1 ≤ r' → r' < M₀ → (r' + j' / 2) % M₀ = 0 →
            ((∀ χ ∈ B₀, Fc χ j 0 ≡ Fc χ j' 0 [ZMOD 2]) ↔
              B₀.filter (fun χ => c χ r ≠ 0) = B₀.filter (fun χ => c χ r' ≠ 0))) ∧
          ∀ j ∈ Finset.Ico 1 m, Even j →
            ((Finset.Ico 1 m).filter
              (fun j' => ∀ χ ∈ B₀, Fc χ j' 0 ≡ Fc χ j 0 [ZMOD 2])).card ≤ 3 :=
  conditional_square_root_cyclic_section_fourier_columns_and_parity_of_localHyp n hn S e p f hp
    hpodd hf
    (ConditionalLocalHyp.of_isSimpleGroup hnonab n hn S e hfour p f hp hpodd hf hmodel)
    ideal basis principal hprincipal

end CFSG.Wreathed.ConditionalSquareRoot

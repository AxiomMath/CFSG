module

public import CFSG.CharacterTheory.Wreathed.ConditionalPrincipalSeriesModel
public import CFSG.CharacterTheory.Wreathed.ConditionalPrincipalSeriesTransport
public import CFSG.CharacterTheory.Wreathed.TwoPartArithmetic
public import CFSG.CharacterTheory.Wreathed.CharacterDegreeCongruence

public noncomputable section

open scoped Classical

namespace CFSG.Wreathed

open Matrix CFSG.TwoRankLowerBound.Helpers CFSG.Semidihedral.Principal
  CFSG.Wreathed.ActualProjectiveLayer CFSG.Wreathed.CyclicCentralSL2Extension
  CFSG.ComponentClassification.CatalogueSchreierLinearTwo CFSG.Wreathed.CentralSL2Abelianization
  CFSG.Wreathed.CentralSL2

universe v

section Assembly

variable {G : Type} [Group G] [Fintype G] [IsSimpleGroup G]

omit [IsSimpleGroup G] in
theorem conditional_actual_principal_series_membership_and_cuspidal_Gram_of_localHyp
    (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n))
    (p f : ℕ) (hp : p.Prime) (hpodd : p ≠ 2) (hf : 1 ≤ f)
    (hloc : ConditionalLocalHyp n hn S e p f)
    [Fintype (centralizerOddCoreQuotient n S e)] (ideal : Ideal ComplexAlgebraicIntegers)
    [ideal.IsMaximal] [CharP (ComplexAlgebraicIntegers ⧸ ideal) 2]
    (basisH : FiniteIrreducibleCharacterBasis (centralizerOddCoreQuotient n S e))
    (principalH : basisH.index) (hprincipalH : (basisH.representation principalH).character = 1)
    (basisN : FiniteIrreducibleCharacterBasis (involutionCentralizer n S e))
    (principalN : basisN.index) (hprincipalN : (basisN.representation principalN).character = 1) :
    (∃ (F : Type) (_ : Field F) (_ : Finite F) (Sigma : Subgroup (F ≃+* F)) (b : Fˣ)
      (hSigma : ∀ σ ∈ Sigma, σ (b : F) = b)
      (ρ : centralizerFullQuotient n hn S e →* coordinateE F)
      (Ψ : SemilinearExtension F b (2 ^ n) (wreathModulus_pos n) (wreathModulus_even hn) Sigma
        hSigma ≃* centralizerOddCoreQuotient n S e),
      ConditionalCompatibleModelData n hn S e p f F Sigma b hSigma ρ Ψ) ∧
    ∀ (F : Type) [Field F] [Fintype F] (Sigma : Subgroup (F ≃+* F)) (b : Fˣ)
      (hSigma : ∀ σ ∈ Sigma, σ (b : F) = b)
      (ρ : centralizerFullQuotient n hn S e →* coordinateE F)
      (Ψ : SemilinearExtension F b (2 ^ n) (wreathModulus_pos n) (wreathModulus_even hn) Sigma
        hSigma ≃* centralizerOddCoreQuotient n S e),
      ConditionalCompatibleModelData n hn S e p f F Sigma b hSigma ρ Ψ →
      ∀ (σ₀ : Sigma) (_hgen : ∀ σ : Sigma, σ ∈ Subgroup.zpowers σ₀) (ζm : ℂ)
        (hζm : IsPrimitiveRoot ζm (2 ^ n)),
      let q := Nat.card F
      let κ := 2 ^ (Nat.card F - 1).factorization 2
      let ΦH : centralizerOddCoreQuotient n S e → ℂ := fun h =>
        (Nat.card {x : Omega F // ((ρ (centralizerFullQuotientMap n hn S e h) : coordinateE F) :
          Equiv.Perm (Omega F)) x = x} : ℂ) - 1
      let ε : ℤ := if Nat.card F % 4 = 1 then 1 else -1
      let π := centralizerOddCoreMap n S e
      let Θ : ((P : PrincipalSeriesParameter F b (2 ^ n)) ×
          (parameterStabilizer hSigma P →* ℂˣ)) → centralizerOddCoreQuotient n S e → ℂ :=
        fun x h => principalInduced (hm := wreathModulus_pos n) (heven := wreathModulus_even hn)
          hSigma x.1 x.2 (Ψ.symm h)
      let adm : ((P : PrincipalSeriesParameter F b (2 ^ n)) ×
          (parameterStabilizer hSigma P →* ℂˣ)) → Prop := fun x => x.1.1.1 ≠ 1
      let sel : ((P : PrincipalSeriesParameter F b (2 ^ n)) ×
          (parameterStabilizer hSigma P →* ℂˣ)) → Prop :=
        fun x => (∃ k : ℕ, orderOf x.1.1.1 = 2 ^ k) ∧ x.2 = 1
      let PH : Set (centralizerOddCoreQuotient n S e → ℂ) :=
        {θ | ∃ x, adm x ∧ θ = Θ x ∧
          ∃ l ∈ coefficientBlock basisH (localizedComplexIntegerRing ideal) principalH,
            (basisH.representation l).character = θ}
      let ℓ : Fin (2 ^ n) → centralizerOddCoreQuotient n S e → ℂ := fun r h =>
        (CentralSL2Abelianization.rootCharacter (2 ^ n) (wreathModulus_pos n) ζm hζm r.val
          (CentralSL2Abelianization.psi F b (2 ^ n) (wreathModulus_pos n) (wreathModulus_even hn)
            Sigma hSigma (Ψ.symm h)).1 : ℂ)
      (∀ (r : Fin (2 ^ n)) (X : SpecialLinearGroup (Fin 2) F) (j k : ℕ),
        ℓ r (Ψ ⟨quotientClass F b (2 ^ n) (wreathModulus_pos n) (wreathModulus_even hn) X
          (j : ZMod (2 * 2 ^ n)), σ₀ ^ k⟩) = ζm ^ (r.val * j)) ∧
      (∀ (P : PrincipalSeriesParameter F b (2 ^ n)) (σ : Sigma),
        σ ∈ parameterStabilizer hSigma P ↔
          P.1.1.comp (Units.map ((σ⁻¹ : Sigma) : F ≃+* F).toRingHom.toMonoidHom) = P.1.1) ∧
      (∀ P : PrincipalSeriesParameter F b (2 ^ n), (∃ k : ℕ, orderOf P.1.1 = 2 ^ k) →
        parameterStabilizer hSigma P = ⊤) ∧
      (∀ θ ∈ PH, θ 1 = (q : ℂ) + 1) ∧
      PH.ncard = 2 ^ n * (κ - 1) / 2 ∧
      (ε = 1 → κ = 2 ^ n) ∧ (ε = -1 → κ = 2) ∧
      ConditionalPrincipalSeriesCuspidalData basisH ideal principalH (MonoidHom.id _) Θ adm sel
        PH ℓ ΦH ε q (Nat.card Sigma) κ ∧
      ConditionalPrincipalSeriesCuspidalData basisN ideal principalN π Θ adm sel PH ℓ ΦH ε q
        (Nat.card Sigma) κ ∧
      PrincipalFamilyCorrespondence π basisH basisN ideal principalH principalN (MonoidHom.id _) π
        ℓ ΦH PH ε ∧
      ∀ (j : ℤ) (hj : ¬ ((2 ^ n : ℕ) : ℤ) ∣ j)
        (basisC : FiniteIrreducibleCharacterBasis (centralSylowPowerCentralizer n S e j))
        (principalC : basisC.index), (basisC.representation principalC).character = 1 →
        CentralSylowPowerQuotientData.{0, v} n hn S e j hj ideal basisN basisH basisC principalN
          principalH principalC ∧
        ConditionalPrincipalSeriesCuspidalData basisC ideal principalC
          (centralSylowPowerMap n hn S e j hj) Θ adm sel PH ℓ ΦH ε q (Nat.card Sigma) κ ∧
        PrincipalFamilyCorrespondence
          (Subgroup.inclusion (centralizer_zpow_le_involutionCentralizer n hn S e j hj))
          basisN basisC ideal principalN principalC π (centralSylowPowerMap n hn S e j hj)
          ℓ ΦH PH ε ∧
        PrincipalFamilyCorrespondence (centralSylowPowerMap n hn S e j hj) basisH basisC ideal
          principalH principalC (MonoidHom.id _) (centralSylowPowerMap n hn S e j hj)
          ℓ ΦH PH ε := by
  refine ⟨hloc.modelData,
    ?_⟩
  intro F _ _ Sigma b hSigma ρ Ψ hdata σ₀ hgen ζm hζm q κ ΦH ε π Θ adm sel PH ℓ
  have hb := hdata.nonsquare
  have hd := hdata.sigma_odd
  have hq3 : 3 ≤ Nat.card F := three_le_card hb
  have hΦ : ∀ h, ΦH h = (Nat.card {x : Omega F // ((ρ (centralizerFullQuotientMap n hn S e h) :
      coordinateE F) : Equiv.Perm (Omega F)) x = x} : ℂ) - 1 := fun _ => rfl
  have hd0 : Nat.card Sigma ≠ 0 := Nat.card_pos.ne'
  set ζd : ℂ := Complex.exp (2 * Real.pi * Complex.I / (Nat.card Sigma : ℂ)) with hζddef
  have hζd : IsPrimitiveRoot ζd (Nat.card Sigma) := Complex.isPrimitiveRoot_exp _ hd0
  have hprev :=
    conditional_actual_principal_linear_augmentation_twists_and_residual_torus_Gram_of_localHyp.{v}
      n hn S e p f hp hpodd hf hloc ideal basisH principalH hprincipalH basisN principalN
      hprincipalN |>.2 F Sigma b hSigma ρ Ψ hdata σ₀ hgen ζm ζd hζm hζd
  obtain ⟨-, -, -, -, hDataH, hDataN, -, hC⟩ := hprev
  obtain ⟨-, hreg⟩ :=
    conditional_actual_central_power_principal_regular_integral_bases_of_localHyp.{v} n hn S e p f
      hp hpodd hf hloc ideal basisH principalH hprincipalH basisN
    principalN hprincipalN
  obtain ⟨hH, -, hcorrN, hCreg⟩ := hreg F Sigma ρ hdata.card hdata.sigma_odd
    hdata.rho_injective hdata.rho_layer hdata.rho_range
  have hℓ : ∀ (r : Fin (2 ^ n)) (h : centralizerOddCoreQuotient n S e),
      (CentralSL2Abelianization.linearCharacter F b (2 ^ n) (wreathModulus_pos n)
        (wreathModulus_even hn) Sigma hSigma σ₀ hgen ζm ζd hζm hζd r 0 (Ψ.symm h) : ℂ) =
        ℓ r h := by
    intro r h
    simp only [CentralSL2Abelianization.linearCharacter,
      CentralSL2Abelianization.quotientLinearCharacter, MonoidHom.comp_apply,
      MonoidHom.mul_apply, MonoidHom.coe_fst, MonoidHom.coe_snd, Fin.val_zero]
    have h0 : ∀ x, CentralSL2Abelianization.rootCharacter (Nat.card Sigma) Nat.card_pos ζd hζd
        0 x = 1 := by
      intro x
      simp [CentralSL2Abelianization.rootCharacter, CentralSL2Abelianization.scalarResidueHom]
    rw [h0, mul_one]
  have hpart : 2 ^ (Nat.card F ^ 2 - 1).factorization 2 = 2 * 2 ^ n := by
    rw [hdata.card]
    exact hloc.qTwoPart
  have hqodd : Nat.card F % 2 = 1 := by
    rw [hdata.card]
    exact Nat.odd_iff.mp ((hp.odd_of_ne_two hpodd).pow)
  have hε : ε = 1 ∨ ε = -1 := by
    by_cases h : Nat.card F % 4 = 1
    · exact Or.inl (ite_eq_left h)
    · exact Or.inr (ite_eq_right h)
  have hκ1 : ε = 1 → κ = 2 ^ n := by
    intro h1
    have hq4 : Nat.card F % 4 = 1 := by
      by_contra h
      have : ε = -1 := ite_eq_right h
      rw [this] at h1
      norm_num at h1
    change 2 ^ (Nat.card F - 1).factorization 2 = 2 ^ n
    rw [two_part_square_sub_one_split _ n hq3 hq4 hpart]
  have hκ2 : ε = -1 → κ = 2 := by
    intro h2
    have hq4 : Nat.card F % 4 = 3 := by
      by_contra h
      have h1 : Nat.card F % 4 = 1 := by omega
      have : ε = 1 := ite_eq_left h1
      rw [this] at h2
      norm_num at h2
    change 2 ^ (Nat.card F - 1).factorization 2 = 2
    rw [two_factorization_eq_one_of_mod_four (Nat.card F - 1) (by omega), pow_one]
  have hΘirr : ∀ x, adm x → Θ x ∈ BlocksIrr (centralizerOddCoreQuotient n S e) := fun x hx =>
    (principalSeries_irreducible_H hn hb hd hx x.2).1
  have hΘP : ∀ x, adm x →
      ((∃ l ∈ coefficientBlock basisH (localizedComplexIntegerRing ideal) principalH,
        (basisH.representation l).character = Θ x) ↔ sel x) := fun x hx =>
    principalSeries_principal_iff_H hn hp hpodd hdata hΦ ideal basisH principalH hprincipalH hH
      hx x.2
  have hPHeq := principalSeriesSet_eq_image hn hp hpodd hdata hΦ ideal basisH principalH
    hprincipalH hH
  have hPHcard : PH.ncard = 2 ^ n * (κ - 1) / 2 :=
    ncard_principalSeriesSet hn hp hpodd hdata hΦ ideal basisH principalH hprincipalH hH
  have hPHprin : ∀ θ ∈ PH, ∃ l ∈ coefficientBlock basisH (localizedComplexIntegerRing ideal)
      principalH, (basisH.representation l).character = θ := fun θ hθ => by
    obtain ⟨-, -, -, h⟩ := hθ
    exact h
  have hPHval : ∀ θ ∈ PH, (∀ y : centralizerOddCoreQuotient n S e, Odd (orderOf y) →
      θ y = 1 + ΦH y) ∧ θ 1 = (q : ℂ) + 1 := by
    intro θ hθ
    have hθ' : θ ∈ (fun P : PrincipalSeriesParameter F b (2 ^ n) => fun h => principalInduced
        (hm := wreathModulus_pos n) (heven := wreathModulus_even hn) hSigma P 1 (Ψ.symm h)) ''
        {P | (∃ k : ℕ, orderOf P.1.1 = 2 ^ k) ∧ P.1.1 ≠ 1} := by
      rw [← hPHeq]
      exact hθ
    obtain ⟨P, ⟨⟨k, hk⟩, hP⟩, rfl⟩ := hθ'
    exact principalSeries_two_power_values hn hdata hΦ hk hP
  have hdegC : ∀ θ ∈ coefficientBlock basisH (localizedComplexIntegerRing ideal) principalH,
      (∃ r, (basisH.representation θ).character = ℓ r ∨
        (basisH.representation θ).character = fun h => ℓ r h * ΦH h) ∨
      (basisH.representation θ).character ∈ PH ∨
      ∃ u : ℕ, 0 < u ∧ u ∣ Nat.card Sigma ∧
        (basisH.representation θ).character 1 = (u : ℂ) * ((q : ℂ) - 1) := by
    intro θ hθ
    rcases compatibleModel_complete_series hn hp hpodd hdata hΦ (σ₀ := σ₀) (hgen := hgen)
        (ζm := ζm) (ζd := ζd) (hζm := hζm) (hζd := hζd) (fun _ _ _ => rfl) (fun _ _ _ => rfl)
        (CFSG.BlockBasics.basis_character_mem_irr basisH θ) with
      ⟨r, v, hrv⟩ | ⟨r, v, hrv⟩ | ⟨P, ν, hP, hPν⟩ | hu
    · have hv : v = 0 := (hDataH.lam_principal r v).mp ⟨θ, hθ, hrv⟩
      subst hv
      refine Or.inl ⟨r, Or.inl ?_⟩
      rw [hrv]
      funext h
      exact hℓ r h
    · have hv : v = 0 := (hDataH.xi_principal r v).mp ⟨θ, hθ, hrv⟩
      subst hv
      refine Or.inl ⟨r, Or.inr ?_⟩
      rw [hrv]
      funext h
      exact congrArg (· * ΦH h) (hℓ r h)
    · exact Or.inr (Or.inl ⟨⟨P, ν⟩, hP, hPν, θ, hθ, rfl⟩)
    · exact Or.inr (Or.inr hu)
  have hℓ0 : ∀ r h, (CentralSL2Abelianization.linearCharacter F b (2 ^ n) (wreathModulus_pos n)
      (wreathModulus_even hn) Sigma hSigma σ₀ hgen ζm ζd hζm hζd r 0 (Ψ.symm h) : ℂ) = ℓ r h :=
    hℓ
  have hmeven : Even (2 ^ n) := wreathModulus_even hn
  have hm2 : 2 ≤ 2 ^ n := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hπ : Function.Surjective π := centralizerOddCoreMap_surjective n S e
  have hblockN := block_inflation_of_regularRowCorrespondence hcorrN
  have hDH : ConditionalPrincipalSeriesCuspidalData basisH ideal principalH (MonoidHom.id _) Θ adm
      sel PH ℓ ΦH ε q (Nat.card Sigma) κ :=
    conditionalPrincipalSeriesCuspidalData_of_inflation basisH basisH ideal principalH principalH
      (MonoidHom.id _) Function.surjective_id
      (fun χ => ⟨fun hχ => ⟨χ, hχ, rfl⟩, fun ⟨θ, hθ, hχθ⟩ => by rwa [basisH.distinct hχθ]⟩)
      hε hDataH hℓ0 (fun r h => congrArg (· * ΦH h) (hℓ r h)) hΘirr hΘP hPHcard hPHprin
      (fun θ hθ => (hPHval θ hθ).1) hdegC hκ1 hκ2 hmeven hm2 hq3
  have hDN : ConditionalPrincipalSeriesCuspidalData basisN ideal principalN π Θ adm sel PH ℓ ΦH ε
      q (Nat.card Sigma) κ :=
    conditionalPrincipalSeriesCuspidalData_of_inflation basisN basisH ideal principalN principalH
      π hπ hblockN hε hDataN hℓ0 (fun r h => congrArg (· * ΦH h) (hℓ r h)) hΘirr hΘP hPHcard
      hPHprin (fun θ hθ => (hPHval θ hθ).1) hdegC hκ1 hκ2 hmeven hm2 hq3
  have hTN : PrincipalFamilyCorrespondence π basisH basisN ideal principalH principalN
      (MonoidHom.id _) π ℓ ΦH PH ε :=
    principalFamilyCorrespondence_of_regularRow π basisH basisN ideal principalH principalN
      (MonoidHom.id _) π (fun _ => rfl) hπ (fun χ _ => ⟨_, rfl⟩) ℓ ΦH PH ε hcorrN
  have hinflN : ∀ χ ∈ coefficientBlock basisN (localizedComplexIntegerRing ideal) principalN,
      ∃ φ : centralizerOddCoreQuotient n S e → ℂ,
        (basisN.representation χ).character = fun y => φ (π y) := by
    intro χ hχ
    obtain ⟨θ, -, hθ⟩ := (hblockN χ).mp hχ
    exact ⟨_, hθ⟩
  refine ⟨fun r X j k => ?_, fun P σ => mem_parameterStabilizer_iff' hSigma P σ,
    fun P ⟨k, hk⟩ => parameterStabilizer_eq_top_of_two_power hSigma hd P hk,
    fun θ hθ => (hPHval θ hθ).2, hPHcard, hκ1, hκ2, hDH, hDN, hTN, ?_⟩
  · simp only [ℓ, MulEquiv.symm_apply_apply, CentralSL2Abelianization.psi_formula, map_natCast]
    exact CentralSL2Abelianization.rootCharacter_natCast _ _ _ _ _ _
  intro j hj basisC principalC hprincipalC
  obtain ⟨hdataj, hDataC, -, -⟩ := hC j hj basisC principalC hprincipalC
  obtain ⟨-, -, hcorrC⟩ := hCreg j hj basisC principalC hprincipalC
  have hπj : Function.Surjective (centralSylowPowerMap n hn S e j hj) := hdataj.map_surjective
  have hDC : ConditionalPrincipalSeriesCuspidalData basisC ideal principalC
      (centralSylowPowerMap n hn S e j hj) Θ adm sel PH ℓ ΦH ε q (Nat.card Sigma) κ :=
    conditionalPrincipalSeriesCuspidalData_of_inflation basisC basisH ideal principalC principalH
      _ hπj hdataj.power_principal_block_inflation hε hDataC hℓ0
      (fun r h => congrArg (· * ΦH h) (hℓ r h)) hΘirr hΘP hPHcard hPHprin
      (fun θ hθ => (hPHval θ hθ).1) hdegC hκ1 hκ2 hmeven hm2 hq3
  have hTC : PrincipalFamilyCorrespondence
      (Subgroup.inclusion (centralizer_zpow_le_involutionCentralizer n hn S e j hj))
      basisN basisC ideal principalN principalC π (centralSylowPowerMap n hn S e j hj)
      ℓ ΦH PH ε :=
    principalFamilyCorrespondence_of_regularRow _ basisN basisC ideal principalN principalC π
      (centralSylowPowerMap n hn S e j hj) (fun _ => rfl) hπj hinflN ℓ ΦH PH ε hcorrC
  exact ⟨hdataj, hDC, hTC, hTN.trans hTC⟩

theorem conditional_actual_principal_series_membership_and_cuspidal_Gram
    (hnonab : ∃ a b : G, a * b ≠ b * a)
    (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n))
    (hfour : ¬ Nonempty (centralizerFullQuotient n hn S e ≃* Equiv.Perm (Fin 4)))
    (p f : ℕ) (hp : p.Prime) (hpodd : p ≠ 2) (hf : 1 ≤ f)
    (hmodel : PSLTwoClassicalModel (centralizerSimpleLayer n hn S e) p f)
    [Fintype (centralizerOddCoreQuotient n S e)] (ideal : Ideal ComplexAlgebraicIntegers)
    [ideal.IsMaximal] [CharP (ComplexAlgebraicIntegers ⧸ ideal) 2]
    (basisH : FiniteIrreducibleCharacterBasis (centralizerOddCoreQuotient n S e))
    (principalH : basisH.index) (hprincipalH : (basisH.representation principalH).character = 1)
    (basisN : FiniteIrreducibleCharacterBasis (involutionCentralizer n S e))
    (principalN : basisN.index) (hprincipalN : (basisN.representation principalN).character = 1) :
    (∃ (F : Type) (_ : Field F) (_ : Finite F) (Sigma : Subgroup (F ≃+* F)) (b : Fˣ)
      (hSigma : ∀ σ ∈ Sigma, σ (b : F) = b)
      (ρ : centralizerFullQuotient n hn S e →* coordinateE F)
      (Ψ : SemilinearExtension F b (2 ^ n) (wreathModulus_pos n) (wreathModulus_even hn) Sigma
        hSigma ≃* centralizerOddCoreQuotient n S e),
      ConditionalCompatibleModelData n hn S e p f F Sigma b hSigma ρ Ψ) ∧
    ∀ (F : Type) [Field F] [Fintype F] (Sigma : Subgroup (F ≃+* F)) (b : Fˣ)
      (hSigma : ∀ σ ∈ Sigma, σ (b : F) = b)
      (ρ : centralizerFullQuotient n hn S e →* coordinateE F)
      (Ψ : SemilinearExtension F b (2 ^ n) (wreathModulus_pos n) (wreathModulus_even hn) Sigma
        hSigma ≃* centralizerOddCoreQuotient n S e),
      ConditionalCompatibleModelData n hn S e p f F Sigma b hSigma ρ Ψ →
      ∀ (σ₀ : Sigma) (_hgen : ∀ σ : Sigma, σ ∈ Subgroup.zpowers σ₀) (ζm : ℂ)
        (hζm : IsPrimitiveRoot ζm (2 ^ n)),
      let q := Nat.card F
      let κ := 2 ^ (Nat.card F - 1).factorization 2
      let ΦH : centralizerOddCoreQuotient n S e → ℂ := fun h =>
        (Nat.card {x : Omega F // ((ρ (centralizerFullQuotientMap n hn S e h) : coordinateE F) :
          Equiv.Perm (Omega F)) x = x} : ℂ) - 1
      let ε : ℤ := if Nat.card F % 4 = 1 then 1 else -1
      let π := centralizerOddCoreMap n S e
      let Θ : ((P : PrincipalSeriesParameter F b (2 ^ n)) ×
          (parameterStabilizer hSigma P →* ℂˣ)) → centralizerOddCoreQuotient n S e → ℂ :=
        fun x h => principalInduced (hm := wreathModulus_pos n) (heven := wreathModulus_even hn)
          hSigma x.1 x.2 (Ψ.symm h)
      let adm : ((P : PrincipalSeriesParameter F b (2 ^ n)) ×
          (parameterStabilizer hSigma P →* ℂˣ)) → Prop := fun x => x.1.1.1 ≠ 1
      let sel : ((P : PrincipalSeriesParameter F b (2 ^ n)) ×
          (parameterStabilizer hSigma P →* ℂˣ)) → Prop :=
        fun x => (∃ k : ℕ, orderOf x.1.1.1 = 2 ^ k) ∧ x.2 = 1
      let PH : Set (centralizerOddCoreQuotient n S e → ℂ) :=
        {θ | ∃ x, adm x ∧ θ = Θ x ∧
          ∃ l ∈ coefficientBlock basisH (localizedComplexIntegerRing ideal) principalH,
            (basisH.representation l).character = θ}
      let ℓ : Fin (2 ^ n) → centralizerOddCoreQuotient n S e → ℂ := fun r h =>
        (CentralSL2Abelianization.rootCharacter (2 ^ n) (wreathModulus_pos n) ζm hζm r.val
          (CentralSL2Abelianization.psi F b (2 ^ n) (wreathModulus_pos n) (wreathModulus_even hn)
            Sigma hSigma (Ψ.symm h)).1 : ℂ)
      (∀ (r : Fin (2 ^ n)) (X : SpecialLinearGroup (Fin 2) F) (j k : ℕ),
        ℓ r (Ψ ⟨quotientClass F b (2 ^ n) (wreathModulus_pos n) (wreathModulus_even hn) X
          (j : ZMod (2 * 2 ^ n)), σ₀ ^ k⟩) = ζm ^ (r.val * j)) ∧
      (∀ (P : PrincipalSeriesParameter F b (2 ^ n)) (σ : Sigma),
        σ ∈ parameterStabilizer hSigma P ↔
          P.1.1.comp (Units.map ((σ⁻¹ : Sigma) : F ≃+* F).toRingHom.toMonoidHom) = P.1.1) ∧
      (∀ P : PrincipalSeriesParameter F b (2 ^ n), (∃ k : ℕ, orderOf P.1.1 = 2 ^ k) →
        parameterStabilizer hSigma P = ⊤) ∧
      (∀ θ ∈ PH, θ 1 = (q : ℂ) + 1) ∧
      PH.ncard = 2 ^ n * (κ - 1) / 2 ∧
      (ε = 1 → κ = 2 ^ n) ∧ (ε = -1 → κ = 2) ∧
      ConditionalPrincipalSeriesCuspidalData basisH ideal principalH (MonoidHom.id _) Θ adm sel
        PH ℓ ΦH ε q (Nat.card Sigma) κ ∧
      ConditionalPrincipalSeriesCuspidalData basisN ideal principalN π Θ adm sel PH ℓ ΦH ε q
        (Nat.card Sigma) κ ∧
      PrincipalFamilyCorrespondence π basisH basisN ideal principalH principalN (MonoidHom.id _) π
        ℓ ΦH PH ε ∧
      ∀ (j : ℤ) (hj : ¬ ((2 ^ n : ℕ) : ℤ) ∣ j)
        (basisC : FiniteIrreducibleCharacterBasis (centralSylowPowerCentralizer n S e j))
        (principalC : basisC.index), (basisC.representation principalC).character = 1 →
        CentralSylowPowerQuotientData.{0, v} n hn S e j hj ideal basisN basisH basisC principalN
          principalH principalC ∧
        ConditionalPrincipalSeriesCuspidalData basisC ideal principalC
          (centralSylowPowerMap n hn S e j hj) Θ adm sel PH ℓ ΦH ε q (Nat.card Sigma) κ ∧
        PrincipalFamilyCorrespondence
          (Subgroup.inclusion (centralizer_zpow_le_involutionCentralizer n hn S e j hj))
          basisN basisC ideal principalN principalC π (centralSylowPowerMap n hn S e j hj)
          ℓ ΦH PH ε ∧
        PrincipalFamilyCorrespondence (centralSylowPowerMap n hn S e j hj) basisH basisC ideal
          principalH principalC (MonoidHom.id _) (centralSylowPowerMap n hn S e j hj)
          ℓ ΦH PH ε :=
  conditional_actual_principal_series_membership_and_cuspidal_Gram_of_localHyp n hn S e p f hp
    hpodd hf
    (ConditionalLocalHyp.of_isSimpleGroup hnonab n hn S e hfour p f hp hpodd hf hmodel)
    ideal basisH principalH hprincipalH basisN principalN hprincipalN

end Assembly

end CFSG.Wreathed

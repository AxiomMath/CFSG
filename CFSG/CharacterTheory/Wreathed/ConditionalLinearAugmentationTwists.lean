module

public import CFSG.CharacterTheory.Wreathed.ConditionalLinearAugmentationTwistsModel
public import CFSG.CharacterTheory.Wreathed.ConditionalLinearAugmentationTwistsRows

public noncomputable section

open scoped Classical

namespace CFSG.Wreathed

open Matrix CFSG.TwoRankLowerBound.Helpers CFSG.Semidihedral.Principal
  CFSG.Wreathed.ActualProjectiveLayer CFSG.Wreathed.CyclicCentralSL2Extension
  CFSG.ComponentClassification.CatalogueSchreierLinearTwo CFSG.Wreathed.CentralSL2Abelianization

universe v

theorem block_inflation_of_regularRowCorrespondence {E E' : Type} [Group E] [Fintype E]
    [Group E'] [Fintype E'] {σ : E' →* E} {basis : FiniteIrreducibleCharacterBasis E}
    {basis' : FiniteIrreducibleCharacterBasis E'} {ideal : Ideal ComplexAlgebraicIntegers}
    [ideal.IsMaximal] {principal : basis.index} {principal' : basis'.index} {Φ : E → ℂ}
    {Φ' : E' → ℂ} {ε : ℤ}
    (h : RegularRowCorrespondence σ basis basis' ideal principal principal' Φ Φ' ε) (χ) :
    χ ∈ coefficientBlock basis' (localizedComplexIntegerRing ideal) principal' ↔
      ∃ θ ∈ coefficientBlock basis (localizedComplexIntegerRing ideal) principal,
        (basis'.representation χ).character = (basis.representation θ).character ∘ σ := by
  obtain ⟨bij, hbij, -, -⟩ := h
  constructor
  · intro hχ
    refine ⟨(bij.symm ⟨χ, hχ⟩).1, (bij.symm ⟨χ, hχ⟩).2, ?_⟩
    have := hbij (bij.symm ⟨χ, hχ⟩)
    rwa [Equiv.apply_symm_apply] at this
  · rintro ⟨θ, hθ, hχθ⟩
    have hχ : χ = (bij ⟨θ, hθ⟩).1 := basis'.distinct (hχθ.trans (hbij ⟨θ, hθ⟩).symm)
    rw [hχ]
    exact (bij ⟨θ, hθ⟩).2

section Assembly

variable {G : Type} [Group G] [Fintype G] [IsSimpleGroup G]

omit [IsSimpleGroup G] in
theorem conditional_actual_principal_linear_augmentation_twists_and_residual_torus_Gram_of_localHyp
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
    ∀ (F : Type) [Field F] [Finite F] (Sigma : Subgroup (F ≃+* F)) (b : Fˣ)
      (hSigma : ∀ σ ∈ Sigma, σ (b : F) = b)
      (ρ : centralizerFullQuotient n hn S e →* coordinateE F)
      (Ψ : SemilinearExtension F b (2 ^ n) (wreathModulus_pos n) (wreathModulus_even hn) Sigma
        hSigma ≃* centralizerOddCoreQuotient n S e),
      ConditionalCompatibleModelData n hn S e p f F Sigma b hSigma ρ Ψ →
      ∀ (σ₀ : Sigma) (hgen : ∀ σ : Sigma, σ ∈ Subgroup.zpowers σ₀) (ζm ζd : ℂ)
        (hζm : IsPrimitiveRoot ζm (2 ^ n)) (hζd : IsPrimitiveRoot ζd (Nat.card Sigma)),
      let ΦH : centralizerOddCoreQuotient n S e → ℂ := fun h =>
        (Nat.card {x : Omega F // ((ρ (centralizerFullQuotientMap n hn S e h) : coordinateE F) :
          Equiv.Perm (Omega F)) x = x} : ℂ) - 1
      let lam : Fin (2 ^ n) → Fin (Nat.card Sigma) → centralizerOddCoreQuotient n S e → ℂ :=
        fun r v h => (linearCharacter F b (2 ^ n) (wreathModulus_pos n) (wreathModulus_even hn)
          Sigma hSigma σ₀ hgen ζm ζd hζm hζd r v (Ψ.symm h) : ℂ)
      let Ξ : Fin (2 ^ n) → Fin (Nat.card Sigma) → centralizerOddCoreQuotient n S e → ℂ :=
        fun r v h => lam r v h * ΦH h
      let ε : ℤ := if Nat.card F % 4 = 1 then 1 else -1
      let π := centralizerOddCoreMap n S e
      (∀ r v (X : SpecialLinearGroup (Fin 2) F) (j k : ℕ),
        lam r v (Ψ ⟨quotientClass F b (2 ^ n) (wreathModulus_pos n) (wreathModulus_even hn) X
          (j : ZMod (2 * 2 ^ n)), σ₀ ^ k⟩) = ζm ^ (r.val * j) * ζd ^ (v.val * k)) ∧
      (∀ θ ∈ BlocksIrr (centralizerOddCoreQuotient n S e), θ 1 = 1 → ∃ r v, θ = lam r v) ∧
      Function.Injective (fun rv : Fin (2 ^ n) × Fin (Nat.card Sigma) => lam rv.1 rv.2) ∧
      Function.Injective (fun rv : Fin (2 ^ n) × Fin (Nat.card Sigma) => Ξ rv.1 rv.2) ∧
      ConditionalTwistResidualData basisH ideal principalH (MonoidHom.id _) lam Ξ ΦH ε
        (Nat.card F) ∧
      ConditionalTwistResidualData basisN ideal principalN π lam Ξ ΦH ε (Nat.card F) ∧
      ResidualTorusCorrespondence π basisH basisN ideal principalH principalN (MonoidHom.id _) π
        lam Ξ ΦH ε ∧
      ∀ (j : ℤ) (hj : ¬ ((2 ^ n : ℕ) : ℤ) ∣ j)
        (basisC : FiniteIrreducibleCharacterBasis (centralSylowPowerCentralizer n S e j))
        (principalC : basisC.index), (basisC.representation principalC).character = 1 →
        CentralSylowPowerQuotientData.{0, v} n hn S e j hj ideal basisN basisH basisC principalN
          principalH principalC ∧
        ConditionalTwistResidualData basisC ideal principalC (centralSylowPowerMap n hn S e j hj)
          lam Ξ ΦH ε (Nat.card F) ∧
        ResidualTorusCorrespondence
          (Subgroup.inclusion (centralizer_zpow_le_involutionCentralizer n hn S e j hj))
          basisN basisC ideal principalN principalC π (centralSylowPowerMap n hn S e j hj)
          lam Ξ ΦH ε ∧
        ResidualTorusCorrespondence (centralSylowPowerMap n hn S e j hj) basisH basisC ideal
          principalH principalC (MonoidHom.id _) (centralSylowPowerMap n hn S e j hj)
          lam Ξ ΦH ε := by
  refine ⟨hloc.modelData,
    ?_⟩
  intro F _ _ Sigma b hSigma ρ Ψ hdata σ₀ hgen ζm ζd hζm hζd ΦH lam Ξ ε π
  obtain ⟨-, hreg⟩ :=
    conditional_actual_central_power_principal_regular_integral_bases_of_localHyp.{v} n hn S e p f
      hp hpodd hf hloc ideal basisH principalH hprincipalH basisN principalN
    hprincipalN
  obtain ⟨hH, hN, hcorrN, hC⟩ := hreg F Sigma ρ hdata.card hdata.sigma_odd hdata.rho_injective
    hdata.rho_layer hdata.rho_range
  have hlam : ∀ r v h, lam r v h = (linearCharacter F b (2 ^ n) (wreathModulus_pos n)
      (wreathModulus_even hn) Sigma hSigma σ₀ hgen ζm ζd hζm hζd r v (Ψ.symm h) : ℂ) :=
    fun _ _ _ => rfl
  have hΦ : ∀ h, ΦH h = (Nat.card {x : Omega F // ((ρ (centralizerFullQuotientMap n hn S e h) :
      coordinateE F) : Equiv.Perm (Omega F)) x = x} : ℂ) - 1 := fun _ => rfl
  have hΞ : ∀ r v h, Ξ r v h = lam r v h * ΦH h := fun _ _ _ => rfl
  have hε : ε = 1 ∨ ε = -1 := by
    by_cases h : Nat.card F % 4 = 1
    · exact Or.inl (ite_eq_left h)
    · exact Or.inr (ite_eq_right h)
  have hq : Nat.card F ≠ 0 := by
    rw [hdata.card]
    exact pow_ne_zero _ hp.ne_zero
  have hq3 : 3 ≤ Nat.card F := CentralSL2.three_le_card hdata.nonsquare
  have hlamirr := compatibleModel_lam_mem_blocksIrr hn hlam
  obtain ⟨hxi, hxiinj⟩ := compatibleModel_xi hn hdata hΦ hlam hΞ
  obtain ⟨hu, hΦu, hlamu⟩ := compatibleModel_unipotent hn hp hpodd hdata hΦ hlam
  obtain ⟨-, hz, -, hΦz, hlamz⟩ := compatibleModel_field hn hp hdata hΦ hlam
  have hodd : ∀ r v, v.val = 0 → ∀ y, Odd (orderOf y) → lam r v y = 1 :=
    fun r v hv y hy => compatibleModel_lam_odd hn hlam r v hv hy
  obtain ⟨hlamP, hxiP⟩ := principal_linear_augmentation_iff basisH ideal principalH hprincipalH hH
    hq hζd hlamirr (fun r v => (hxi r v).1) hΞ hodd hu hΦu hlamu hz hΦz hlamz
  have hlamP0 : ∀ r v, (∃ l ∈ coefficientBlock basisH (localizedComplexIntegerRing ideal)
      principalH, (basisH.representation l).character = lam r v) ↔ v = 0 :=
    fun r v => (hlamP r v).trans Fin.val_eq_zero_iff
  have hxiP0 : ∀ r v, (∃ l ∈ coefficientBlock basisH (localizedComplexIntegerRing ideal)
      principalH, (basisH.representation l).character = Ξ r v) ↔ v = 0 :=
    fun r v => (hxiP r v).trans Fin.val_eq_zero_iff
  have hlam_odd : ∀ r (y : centralizerOddCoreQuotient n S e), Odd (orderOf y) → lam r 0 y = 1 :=
    fun r y hy => hodd r 0 rfl y hy
  have hxi_odd : ∀ r (y : centralizerOddCoreQuotient n S e), Odd (orderOf y) →
      Ξ r 0 y = ΦH y := fun r y hy => by rw [hΞ, hlam_odd r y hy, one_mul]
  have hinj : Function.Injective (Sum.elim (fun r : Fin (2 ^ n) => lam r 0)
      (fun r : Fin (2 ^ n) => Ξ r 0)) := by
    rintro (r | r) (r' | r') h
    · exact congrArg Sum.inl
        (congrArg Prod.fst (compatibleModel_lam_injective hn hlam (a₁ := (r, 0)) (a₂ := (r', 0)) h))
    · have h1 := congrFun h 1
      simp only [Sum.elim_inl, Sum.elim_inr, (hlamirr r 0).2, (hxi r' 0).2] at h1
      have h1' : ((Nat.card F : ℕ) : ℂ) = ((1 : ℕ) : ℂ) := by rw [Nat.cast_one]; exact h1.symm
      exact absurd (Nat.cast_injective h1') (by omega)
    · have h1 := congrFun h 1
      simp only [Sum.elim_inl, Sum.elim_inr, (hlamirr r' 0).2, (hxi r 0).2] at h1
      have h1' : ((Nat.card F : ℕ) : ℂ) = ((1 : ℕ) : ℂ) := by rw [Nat.cast_one]; exact h1
      exact absurd (Nat.cast_injective h1') (by omega)
    · exact congrArg Sum.inr (congrArg Prod.fst (hxiinj (a₁ := (r, 0)) (a₂ := (r', 0)) h))
  have hdeg : ∀ θ : basisH.index,
      (∃ r v, (basisH.representation θ).character = lam r v) ∨
      (∃ r v, (basisH.representation θ).character = Ξ r v) ∨
      ∃ u : ℕ, 0 < u ∧ u ∣ Nat.card Sigma ∧
        ((basisH.representation θ).character 1 = (u : ℂ) * ((Nat.card F : ℂ) + 1) ∨
          (basisH.representation θ).character 1 = (u : ℂ) * ((Nat.card F : ℂ) - 1)) :=
    fun θ => compatibleModel_complete hn hp hpodd hdata hΦ hlam hΞ
      (CFSG.BlockBasics.basis_character_mem_irr basisH θ)
  have hcast : ((2 ^ n : ℕ) : ℤ) = (2 : ℤ) ^ n := by push_cast; rfl
  have hπ : Function.Surjective π := centralizerOddCoreMap_surjective n S e
  have hblockN := block_inflation_of_regularRowCorrespondence hcorrN
  have hinflN : ∀ χ ∈ coefficientBlock basisN (localizedComplexIntegerRing ideal) principalN,
      ∃ φ : centralizerOddCoreQuotient n S e → ℂ,
        (basisN.representation χ).character = fun y => φ (π y) := by
    intro χ hχ
    obtain ⟨θ, -, hθ⟩ := (hblockN χ).mp hχ
    exact ⟨_, hθ⟩
  have hDataH : ConditionalTwistResidualData basisH ideal principalH (MonoidHom.id _) lam Ξ ΦH ε
      (Nat.card F) := by
    refine conditionalTwistResidualData_of_inflation basisH basisH ideal principalH principalH
      (MonoidHom.id _) Function.surjective_id (fun χ => ⟨fun hχ => ⟨χ, hχ, rfl⟩, ?_⟩) hε ?_
      hlamirr hxi hlamP0 hxiP0 hlam_odd hxi_odd hinj hdeg
    · rintro ⟨θ, hθ, hχθ⟩
      rwa [basisH.distinct hχθ]
    · rw [hcast]
      exact hH
  have hDataN : ConditionalTwistResidualData basisN ideal principalN π lam Ξ ΦH ε
      (Nat.card F) := by
    refine conditionalTwistResidualData_of_inflation basisN basisH ideal principalN principalH π hπ
      hblockN hε ?_ hlamirr hxi hlamP0 hxiP0 hlam_odd hxi_odd hinj hdeg
    rw [hcast]
    exact hN
  have hTN : ResidualTorusCorrespondence π basisH basisN ideal principalH principalN
      (MonoidHom.id _) π lam Ξ ΦH ε :=
    residualTorusCorrespondence_of_regularRow π basisH basisN ideal principalH principalN
      (MonoidHom.id _) π (fun _ => rfl) hπ (fun χ _ => ⟨_, rfl⟩) lam Ξ ΦH ε hcorrN
  refine ⟨compatibleModel_lam_formula hn hlam, fun θ hθ h1 =>
    compatibleModel_lam_exhaustive hn hlam hdata.nonsquare hθ h1,
    compatibleModel_lam_injective hn hlam, hxiinj, hDataH, hDataN, hTN, ?_⟩
  intro j hj basisC principalC hprincipalC
  obtain ⟨hdataj, hCreg, hcorrC⟩ := hC j hj basisC principalC hprincipalC
  have hπj : Function.Surjective (centralSylowPowerMap n hn S e j hj) := hdataj.map_surjective
  have hDataC : ConditionalTwistResidualData basisC ideal principalC
      (centralSylowPowerMap n hn S e j hj) lam Ξ ΦH ε (Nat.card F) := by
    refine conditionalTwistResidualData_of_inflation basisC basisH ideal principalC principalH
      (centralSylowPowerMap n hn S e j hj) hπj hdataj.power_principal_block_inflation hε ?_
      hlamirr hxi hlamP0 hxiP0 hlam_odd hxi_odd hinj hdeg
    rw [hcast]
    exact hCreg
  have hTC : ResidualTorusCorrespondence
      (Subgroup.inclusion (centralizer_zpow_le_involutionCentralizer n hn S e j hj))
      basisN basisC ideal principalN principalC π (centralSylowPowerMap n hn S e j hj)
      lam Ξ ΦH ε :=
    residualTorusCorrespondence_of_regularRow _ basisN basisC ideal principalN principalC π
      (centralSylowPowerMap n hn S e j hj) (fun _ => rfl) hπj hinflN lam Ξ ΦH ε hcorrC
  exact ⟨hdataj, hDataC, hTC, hTN.trans hTC⟩

theorem conditional_actual_principal_linear_augmentation_twists_and_residual_torus_Gram
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
    ∀ (F : Type) [Field F] [Finite F] (Sigma : Subgroup (F ≃+* F)) (b : Fˣ)
      (hSigma : ∀ σ ∈ Sigma, σ (b : F) = b)
      (ρ : centralizerFullQuotient n hn S e →* coordinateE F)
      (Ψ : SemilinearExtension F b (2 ^ n) (wreathModulus_pos n) (wreathModulus_even hn) Sigma
        hSigma ≃* centralizerOddCoreQuotient n S e),
      ConditionalCompatibleModelData n hn S e p f F Sigma b hSigma ρ Ψ →
      ∀ (σ₀ : Sigma) (hgen : ∀ σ : Sigma, σ ∈ Subgroup.zpowers σ₀) (ζm ζd : ℂ)
        (hζm : IsPrimitiveRoot ζm (2 ^ n)) (hζd : IsPrimitiveRoot ζd (Nat.card Sigma)),
      let ΦH : centralizerOddCoreQuotient n S e → ℂ := fun h =>
        (Nat.card {x : Omega F // ((ρ (centralizerFullQuotientMap n hn S e h) : coordinateE F) :
          Equiv.Perm (Omega F)) x = x} : ℂ) - 1
      let lam : Fin (2 ^ n) → Fin (Nat.card Sigma) → centralizerOddCoreQuotient n S e → ℂ :=
        fun r v h => (linearCharacter F b (2 ^ n) (wreathModulus_pos n) (wreathModulus_even hn)
          Sigma hSigma σ₀ hgen ζm ζd hζm hζd r v (Ψ.symm h) : ℂ)
      let Ξ : Fin (2 ^ n) → Fin (Nat.card Sigma) → centralizerOddCoreQuotient n S e → ℂ :=
        fun r v h => lam r v h * ΦH h
      let ε : ℤ := if Nat.card F % 4 = 1 then 1 else -1
      let π := centralizerOddCoreMap n S e
      (∀ r v (X : SpecialLinearGroup (Fin 2) F) (j k : ℕ),
        lam r v (Ψ ⟨quotientClass F b (2 ^ n) (wreathModulus_pos n) (wreathModulus_even hn) X
          (j : ZMod (2 * 2 ^ n)), σ₀ ^ k⟩) = ζm ^ (r.val * j) * ζd ^ (v.val * k)) ∧
      (∀ θ ∈ BlocksIrr (centralizerOddCoreQuotient n S e), θ 1 = 1 → ∃ r v, θ = lam r v) ∧
      Function.Injective (fun rv : Fin (2 ^ n) × Fin (Nat.card Sigma) => lam rv.1 rv.2) ∧
      Function.Injective (fun rv : Fin (2 ^ n) × Fin (Nat.card Sigma) => Ξ rv.1 rv.2) ∧
      ConditionalTwistResidualData basisH ideal principalH (MonoidHom.id _) lam Ξ ΦH ε
        (Nat.card F) ∧
      ConditionalTwistResidualData basisN ideal principalN π lam Ξ ΦH ε (Nat.card F) ∧
      ResidualTorusCorrespondence π basisH basisN ideal principalH principalN (MonoidHom.id _) π
        lam Ξ ΦH ε ∧
      ∀ (j : ℤ) (hj : ¬ ((2 ^ n : ℕ) : ℤ) ∣ j)
        (basisC : FiniteIrreducibleCharacterBasis (centralSylowPowerCentralizer n S e j))
        (principalC : basisC.index), (basisC.representation principalC).character = 1 →
        CentralSylowPowerQuotientData.{0, v} n hn S e j hj ideal basisN basisH basisC principalN
          principalH principalC ∧
        ConditionalTwistResidualData basisC ideal principalC (centralSylowPowerMap n hn S e j hj)
          lam Ξ ΦH ε (Nat.card F) ∧
        ResidualTorusCorrespondence
          (Subgroup.inclusion (centralizer_zpow_le_involutionCentralizer n hn S e j hj))
          basisN basisC ideal principalN principalC π (centralSylowPowerMap n hn S e j hj)
          lam Ξ ΦH ε ∧
        ResidualTorusCorrespondence (centralSylowPowerMap n hn S e j hj) basisH basisC ideal
          principalH principalC (MonoidHom.id _) (centralSylowPowerMap n hn S e j hj)
          lam Ξ ΦH ε :=
  conditional_actual_principal_linear_augmentation_twists_and_residual_torus_Gram_of_localHyp n hn
    S e p f hp hpodd hf
    (ConditionalLocalHyp.of_isSimpleGroup hnonab n hn S e hfour p f hp hpodd hf hmodel)
    ideal basisH principalH hprincipalH basisN principalN hprincipalN

end Assembly

end CFSG.Wreathed

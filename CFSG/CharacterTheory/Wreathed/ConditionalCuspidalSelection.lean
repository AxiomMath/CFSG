module

public import CFSG.CharacterTheory.Wreathed.ConditionalCuspidalSelectionModel
public import CFSG.CharacterTheory.Wreathed.ConditionalCuspidalSelectionPullback

public noncomputable section

open scoped Classical

namespace CFSG.Wreathed

open Matrix CFSG.TwoRankLowerBound.Helpers CFSG.Semidihedral.Principal
  CFSG.Wreathed.ActualProjectiveLayer CFSG.Wreathed.CyclicCentralSL2Extension
  CFSG.ComponentClassification.CatalogueSchreierLinearTwo CFSG.Wreathed.CentralSL2Abelianization
  CFSG.Wreathed.CentralSL2

universe v

section Arithmetic

theorem two_pow_factorization_succ_of_mod_four_one {q : ℕ} (hq : q % 4 = 1) :
    2 ^ (q + 1).factorization 2 = 2 := by
  rw [two_factorization_eq_one_of_mod_four (q + 1) (by omega), pow_one]

theorem block_card_arithmetic {n κp κm : ℕ} (hn : 2 ≤ n)
    (hκ : (κp = 2 ^ n ∧ κm = 2) ∨ (κp = 2 ∧ κm = 2 ^ n)) :
    2 ^ n + 2 ^ n + 2 ^ n * (κp - 1) / 2 + 2 ^ n * (κm - 1) / 2 =
      2 ^ n * (2 ^ n + 4) / 2 := by
  obtain ⟨k, hk⟩ : Even (2 ^ n) := wreathModulus_even hn
  have hk1 : 1 ≤ k := by
    have : 4 ≤ 2 ^ n := by
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
    omega
  have e1 : (k + k) * (k + k - 1) / 2 = k * (2 * k - 1) := by
    rw [show (k + k) * (k + k - 1) = 2 * (k * (2 * k - 1)) by
      rw [show k + k - 1 = 2 * k - 1 by omega]
      ring]
    exact Nat.mul_div_cancel_left _ two_pos
  have e2 : (k + k) * (2 - 1) / 2 = k := by omega
  have e3 : (k + k) * (k + k + 4) / 2 = k * (2 * k + 4) := by
    rw [show (k + k) * (k + k + 4) = 2 * (k * (2 * k + 4)) by ring]
    exact Nat.mul_div_cancel_left _ two_pos
  have e4 : k * (2 * k - 1) = 2 * k * k - k := by
    rw [Nat.mul_sub, mul_one]
    ring_nf
  rcases hκ with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · rw [hk, e1, e2, e3, e4]
    have : k ≤ 2 * k * k := by nlinarith
    zify [this]
    ring
  · rw [hk, e1, e2, e3, e4]
    have : k ≤ 2 * k * k := by nlinarith
    zify [this]
    ring

end Arithmetic

section Assembly

variable {G : Type} [Group G] [Fintype G] [IsSimpleGroup G]

omit [IsSimpleGroup G] in
theorem conditional_actual_principal_cuspidal_selection_and_full_degree_counts_of_localHyp
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
        hSigma ≃* centralizerOddCoreQuotient n S e)
      (hdata : ConditionalCompatibleModelData n hn S e p f F Sigma b hSigma ρ Ψ)
      (σ₀ : Sigma) (_hgen : ∀ σ : Sigma, σ ∈ Subgroup.zpowers σ₀) (ζm : ℂ)
      (hζm : IsPrimitiveRoot ζm (2 ^ n))
      (E : Type) [Field E] [Algebra F E] (basis : Module.Basis (Fin 2) F E) (z₀ y₀ : Eˣ)
      (hz₀ : (z₀ : E) * (z₀ : E) ^ Nat.card F = algebraMap F E b)
      (hy₀ : (y₀ : E) * (y₀ : E) ^ Nat.card F = -1) (ψ : AddChar F ℂ) (_hψ : ψ ≠ 1),
      let hb : ¬ IsSquare b := hdata.nonsquare
      let h2 : (2 : F) ≠ 0 := two_ne_zero_of_not_isSquare hb
      let q := Nat.card F
      let d := Nat.card Sigma
      let q₀ := p ^ (f / d)
      let κp := 2 ^ (Nat.card F - 1).factorization 2
      let κm := 2 ^ (Nat.card F + 1).factorization 2
      let Hc := centralizerOddCoreQuotient n S e
      let K := CentralExtension F b (2 ^ n) (wreathModulus_pos n) (wreathModulus_even hn)
      let Hh := SemilinearExtension F b (2 ^ n) (wreathModulus_pos n) (wreathModulus_even hn)
        Sigma hSigma
      let t₀ : Hh := ⟨1, σ₀⟩
      let σact := fieldAction F b (2 ^ n) (wreathModulus_pos n) (wreathModulus_even hn) Sigma
        hSigma σ₀
      let ΦH : Hc → ℂ := fun h =>
        (Nat.card {x : Omega F // ((ρ (centralizerFullQuotientMap n hn S e h) : coordinateE F) :
          Equiv.Perm (Omega F)) x = x} : ℂ) - 1
      let ε : ℤ := if Nat.card F % 4 = 1 then 1 else -1
      let π := centralizerOddCoreMap n S e
      let Θ : ((P : PrincipalSeriesParameter F b (2 ^ n)) ×
          (parameterStabilizer hSigma P →* ℂˣ)) → Hc → ℂ :=
        fun x h => principalInduced (hm := wreathModulus_pos n) (heven := wreathModulus_even hn)
          hSigma x.1 x.2 (Ψ.symm h)
      let B0 := coefficientBlock basisH (localizedComplexIntegerRing ideal) principalH
      let chr : basisH.index → Hc → ℂ := fun l => (basisH.representation l).character
      let PH : Set (Hc → ℂ) := {θ | ∃ x, x.1.1.1 ≠ 1 ∧ θ = Θ x ∧ ∃ l ∈ B0, chr l = θ}
      let ℓ : Fin (2 ^ n) → Hc → ℂ := fun r h =>
        (CentralSL2Abelianization.rootCharacter (2 ^ n) (wreathModulus_pos n) ζm hζm r.val
          (CentralSL2Abelianization.psi F b (2 ^ n) (wreathModulus_pos n) (wreathModulus_even hn)
            Sigma hSigma (Ψ.symm h)).1 : ℂ)
      let FH := linearAugmentationLabels basisH (MonoidHom.id Hc) ℓ ΦH
      let PL := principalSeriesLabels basisH (MonoidHom.id Hc) PH
      let CH := cuspidalLabels basisH ideal principalH (MonoidHom.id Hc) ℓ ΦH PH
      let res : (Hc → ℂ) → K → ℂ := fun χ g => χ (Ψ (SemidirectProduct.inl g))
      let Tm := nonsplitTorus F b (2 ^ n) (wreathModulus_pos n) (wreathModulus_even hn) E basis
      let lam := nonsplitCharacter F b (2 ^ n) (wreathModulus_pos n) (wreathModulus_even hn) E
        basis h2 z₀ hz₀
      let weylP := nonsplitWeylParameter F b (2 ^ n) (wreathModulus_even hn) E basis h2 z₀ hz₀
      let wm : (Tm →* ℂˣ) → (Tm →* ℂˣ) := fun μ => μ.comp (minusWeylConj h2 y₀ hy₀)
      let Λ : (Tm →* ℂˣ) → K → ℂ := fun μ =>
        inducedFunction (auSubgroup F b (2 ^ n) (wreathModulus_pos n) (wreathModulus_even hn))
          (fun g => auCharacter hb (restrictA hb μ) ψ g) -
        inducedFunction Tm fun t => (μ t : ℂ)
      let Par2 : Set (NonsplitParameter F E b (2 ^ n) h2 z₀ hz₀) :=
        {P | P.1.1 ≠ 1 ∧ ∃ k : ℕ, orderOf P.1.1 = 2 ^ k}
      let D₂ : Set (K → ℂ) := (fun P => Λ (lam P)) '' Par2
      let TN : Set (Hc → ℂ) := {χ | ∃ θ ∈ D₂, ∃ (V : Type) (_ : AddCommGroup V) (_ : Module ℂ V)
        (_ : FiniteDimensional ℂ V) (R : Representation ℂ K V) (T : (Module.End ℂ V)ˣ)
        (ρ' : Representation ℂ Hh V), R.IsIrreducible ∧ R.character = θ ∧
        (∀ k, (T : Module.End ℂ V) * R k * ((T⁻¹ : (Module.End ℂ V)ˣ) : Module.End ℂ V) =
          R (σact k)) ∧ T ^ d = 1 ∧
        (∀ (k : K) (j : ℕ), ρ' ⟨k, σ₀ ^ j⟩ = R k *
          ((((q₀ : ℂ) - 1) / LinearMap.trace ℂ V (T : Module.End ℂ V)) •
            (T : Module.End ℂ V)) ^ j) ∧
        χ = fun h => ρ'.character (Ψ.symm h)}
      let BH : Set (Hc → ℂ) := chr '' ↑(FH ∪ PL ∪ CH)
      let I : (K → ℂ) → Subgroup Hh := fun θ => semilinearInertia (twistStabilizer hSigma θ)
      let ΘO : (θ : K → ℂ) → (I θ → ℂ) → (twistStabilizer hSigma θ →* ℂˣ) → Hh → ℂ :=
        fun θ χ ν => inducedFunction (I θ) fun y => χ y * (ν ⟨(y : Hh).right, y.2⟩ : ℂ)
      1 < q₀ ∧
      (∀ P : NonsplitParameter F E b (2 ^ n) h2 z₀ hz₀,
        (∀ t, lam P ⟨nonsplitDiag F b (2 ^ n) (wreathModulus_pos n) (wreathModulus_even hn) E
          basis t, nonsplitDiag_mem t⟩ = P.1.1 t) ∧
        lam P ⟨nonsplitGenerator F b (2 ^ n) (wreathModulus_pos n) (wreathModulus_even hn) E
          basis z₀ hz₀, nonsplitGenerator_mem z₀ hz₀⟩ = P.1.2) ∧
      Function.Bijective lam ∧
      (∀ P : NonsplitParameter F E b (2 ^ n) h2 z₀ hz₀, wm (lam P) = lam (weylP P) ∧
        (weylP P).1 = (P.1.1⁻¹, P.1.1 (βE F E basis z₀) * P.1.2) ∧ weylP (weylP P) = P ∧
        (P.1.1 ≠ 1 → weylP P ≠ P)) ∧
      (∀ P ∈ Par2, weylP P ∈ Par2) ∧ (∀ θ ∈ D₂, θ ∈ BlocksIrr K ∧ θ 1 = (q : ℂ) - 1) ∧
      D₂ = Λ '' {μ | wm μ ≠ μ ∧ ∃ k : ℕ, orderOf μ = 2 ^ k} ∧
      (∀ P ∈ Par2, ∀ P' ∈ Par2, Λ (lam P) = Λ (lam P') ↔ P' = P ∨ P' = weylP P) ∧
      D₂.ncard = 2 ^ n * (κm - 1) / 2 ∧
      (∀ l ∈ CH, res (chr l) ∈ BlocksIrr K ∧ chr l 1 = (q : ℂ) - 1 ∧
        chr l (Ψ t₀) = (q₀ : ℂ) - 1 ∧ ∀ y : Hc, Odd (orderOf y) → chr l y = ΦH y - 1) ∧
      Set.BijOn (fun l => res (chr l)) ↑CH D₂ ∧
      (∀ θ ∈ D₂, ∀ σ : Sigma, fieldTwist hSigma σ θ = θ) ∧
      (∀ θ ∈ D₂, ∃! l, l ∈ B0 ∧ res (chr l) = θ) ∧
      (∀ θ ∈ D₂, ∀ (V : Type) [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
          (R : Representation ℂ K V), R.IsIrreducible → R.character = θ →
        (∃ T : (Module.End ℂ V)ˣ, (∀ k, (T : Module.End ℂ V) * R k *
          ((T⁻¹ : (Module.End ℂ V)ˣ) : Module.End ℂ V) = R (σact k)) ∧ T ^ d = 1) ∧
        ∀ T : (Module.End ℂ V)ˣ, (∀ k, (T : Module.End ℂ V) * R k *
          ((T⁻¹ : (Module.End ℂ V)ˣ) : Module.End ℂ V) = R (σact k)) → T ^ d = 1 →
          let c : ℂ := ((q₀ : ℂ) - 1) / LinearMap.trace ℂ V (T : Module.End ℂ V)
          LinearMap.trace ℂ V (T : Module.End ℂ V) ≠ 0 ∧ c ^ d = 1 ∧
          (∃ ρ' : Representation ℂ Hh V, ∀ (k : K) (j : ℕ),
            ρ' ⟨k, σ₀ ^ j⟩ = R k * (c • (T : Module.End ℂ V)) ^ j) ∧
          (∀ ρ' : Representation ℂ Hh V, (∀ (k : K) (j : ℕ),
            ρ' ⟨k, σ₀ ^ j⟩ = R k * (c • (T : Module.End ℂ V)) ^ j) →
            ∃ l ∈ CH, res (chr l) = θ ∧ chr l = fun h => ρ'.character (Ψ.symm h)) ∧
          ∀ ω : ℂ, ω ^ d = 1 →
            (∃ ρ' : Representation ℂ Hh V, ∀ (k : K) (j : ℕ),
              ρ' ⟨k, σ₀ ^ j⟩ = R k * (ω • (T : Module.End ℂ V)) ^ j) ∧
            ∀ ρ' : Representation ℂ Hh V, (∀ (k : K) (j : ℕ),
              ρ' ⟨k, σ₀ ^ j⟩ = R k * (ω • (T : Module.End ℂ V)) ^ j) →
              ((∃ l ∈ B0, chr l = fun h => ρ'.character (Ψ.symm h)) ↔ ω = c)) ∧
      chr '' ↑CH = TN ∧ (∀ χ₁ ∈ TN, ∀ χ₂ ∈ TN, res χ₁ = res χ₂ → χ₁ = χ₂) ∧
      (∀ θ : K → ℂ, θ ∈ BlocksIrr K → θ 1 = (q : ℂ) - 1 →
        ∀ χ : I θ → ℂ, χ ∈ BlocksIrr (I θ) →
          (∀ (g : K) (hg : (SemidirectProduct.inl g : Hh) ∈ I θ),
            χ ⟨SemidirectProduct.inl g, hg⟩ = θ g) →
        ∀ ν : twistStabilizer hSigma θ →* ℂˣ,
          ((∃ l ∈ B0, chr l = fun h => ΘO θ χ ν (Ψ.symm h)) ↔
            {θ' | ∃ σ : Sigma, θ' = fieldTwist hSigma σ θ} = {θ} ∧ θ ∈ D₂ ∧
              ∃ hσ : σ₀ ∈ twistStabilizer hSigma θ,
                (ν ⟨σ₀, hσ⟩ : ℂ) = ((q₀ : ℂ) - 1) / χ ⟨t₀, hσ⟩) ∧
          ((∃ l ∈ B0, chr l = fun h => ΘO θ χ ν (Ψ.symm h)) →
            twistStabilizer hSigma θ = ⊤ ∧
              ∀ hσ : σ₀ ∈ twistStabilizer hSigma θ, χ ⟨t₀, hσ⟩ ≠ 0)) ∧
      B0 = FH ∪ PL ∪ CH ∧ (ε = 1 → κm = 2) ∧ (ε = -1 → κm = 2 ^ n) ∧
      CuspidalSelectionPullbackData basisH ideal principalH (MonoidHom.id Hc) ℓ ΦH PH BH TN D₂
        res q κp κm ∧
      CuspidalSelectionPullbackData basisN ideal principalN π ℓ ΦH PH BH TN D₂ res q κp κm ∧
      ∀ (j : ℤ) (hj : ¬ ((2 ^ n : ℕ) : ℤ) ∣ j)
        (basisC : FiniteIrreducibleCharacterBasis (centralSylowPowerCentralizer n S e j))
        (principalC : basisC.index), (basisC.representation principalC).character = 1 →
        CentralSylowPowerQuotientData.{0, v} n hn S e j hj ideal basisN basisH basisC principalN
          principalH principalC ∧
        CuspidalSelectionPullbackData basisC ideal principalC (centralSylowPowerMap n hn S e j hj)
          ℓ ΦH PH BH TN D₂ res q κp κm := by
  refine ⟨hloc.modelData,
    ?_⟩
  intro F _ _ Sigma b hSigma ρ Ψ hdata σ₀ hgen ζm hζm E _ _ basis z₀ y₀ hz₀ hy₀ ψ hψ hb h2 q d q₀
    κp κm Hc K Hh t₀ σact ΦH ε π Θ B0 chr PH ℓ FH PL CH res Tm lam weylP wm Λ Par2 D₂ TN BH I ΘO
  have hd := hdata.sigma_odd
  have hpo : Odd p := hp.odd_of_ne_two hpodd
  have : Fact p.Prime := ⟨hp⟩
  have : CharP F p :=
    CFSG.Semidihedral.FixedFieldData.characteristic_of_prime_power_card F hp hdata.card
  have hq3 : 3 ≤ Nat.card F := three_le_card hb
  have hq1 : ((q : ℂ) - 1) ≠ 0 := by
    rw [sub_ne_zero, ← Nat.cast_one, Ne, Nat.cast_inj]
    omega
  have hΦ : ∀ h, ΦH h = (Nat.card {x : Omega F // ((ρ (centralizerFullQuotientMap n hn S e h) :
      coordinateE F) : Equiv.Perm (Omega F)) x = x} : ℂ) - 1 := fun _ => rfl
  have hq₀ : 1 < q₀ := one_lt_fixedFieldCard hp hf hdata.sigma_dvd
  have hq₀1 : ((q₀ : ℂ) - 1) ≠ 0 := by
    rw [sub_ne_zero, ← Nat.cast_one, Ne, Nat.cast_inj]
    omega
  have hprev := (conditional_actual_principal_series_membership_and_cuspidal_Gram_of_localHyp.{v} n
    hn S e p f hp hpodd hf hloc ideal basisH principalH hprincipalH basisN principalN
    hprincipalN).2 F Sigma b hSigma ρ Ψ hdata σ₀ hgen ζm hζm
  obtain ⟨-, -, -, hPH1, -, hκ1, hκ2, hDH, -, hTNcorr, hCprev⟩ := hprev
  have hd0 : Nat.card Sigma ≠ 0 := Nat.card_pos.ne'
  set ζd : ℂ := Complex.exp (2 * Real.pi * Complex.I / (Nat.card Sigma : ℂ)) with hζddef
  have hζd : IsPrimitiveRoot ζd (Nat.card Sigma) := Complex.isPrimitiveRoot_exp _ hd0
  have hprev2 :=
    conditional_actual_principal_linear_augmentation_twists_and_residual_torus_Gram_of_localHyp.{v}
      n hn S e p f hp hpodd hf hloc ideal basisH principalH hprincipalH basisN principalN
      hprincipalN |>.2 F Sigma b hSigma ρ Ψ hdata σ₀ hgen ζm ζd hζm hζd
  obtain ⟨-, -, -, -, hDataH, -, -, -⟩ := hprev2
  have hℓ : ∀ (r : Fin (2 ^ n)) (h : Hc),
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
  have hlamP := fun r v h => (hDataH.lam_principal r v).mp h
  have hxiP := fun r v h => (hDataH.xi_principal r v).mp h
  have hPHmem : ∀ (P : PrincipalSeriesParameter F b (2 ^ n))
      (ν : parameterStabilizer hSigma P →* ℂˣ), P.1.1 ≠ 1 →
      (∃ l ∈ B0, chr l = fun h => principalInduced (hm := wreathModulus_pos n)
        (heven := wreathModulus_even hn) hSigma P ν (Ψ.symm h)) →
      (fun h => principalInduced (hm := wreathModulus_pos n) (heven := wreathModulus_even hn)
        hSigma P ν (Ψ.symm h)) ∈ PH :=
    fun P ν hP hprin => ⟨⟨P, ν⟩, hP, rfl, hprin⟩
  have hℓ1 : ∀ r, ℓ r 1 = 1 := by
    intro r
    rw [← hℓ r 1]
    simp
  have hΦ1 : ΦH 1 = q := hDataH.regular_basis.degree
  obtain ⟨u, hu, hsum1, hsum2⟩ := hDH.cuspidal
  have hCfacts : ∀ l (hl : l ∈ CH), res (chr l) ∈ cuspBase ∧
      twistStabilizer hSigma (res (chr l)) = ⊤ ∧ chr l 1 = (q : ℂ) - 1 ∧
      chr l (Ψ t₀) = (q₀ : ℂ) - 1 ∧ (∀ y : Hc, Odd (orderOf y) → chr l y = ΦH y - 1) ∧
      u ⟨l, hl⟩ = 1 := by
    intro l hl
    obtain ⟨hu0, -, hu1, huodd, -⟩ := hu ⟨l, hl⟩
    have habove := cuspidalLabel_comp_mem_aboveFamily hn hp hpodd hdata hΦ ideal basisH
      principalH (σ₀ := σ₀) (hgen := hgen) (ζm := ζm) (ζd := ζd) (hζm := hζm) (hζd := hζd)
      (fun _ _ _ => rfl) (fun _ _ _ => rfl) hℓ hlamP hxiP hPHmem hl
    obtain ⟨hθ, hStab, hval⟩ := cuspidalLabel_restrict hn hp hf hdata hΦ habove hgen hu0 huodd
    have h1 : chr l 1 = (q : ℂ) - 1 := by
      have h := hθ.2
      change chr l (Ψ (SemidirectProduct.inl 1)) = _ at h
      rwa [map_one, map_one] at h
    have hu1' : u ⟨l, hl⟩ = 1 := by
      have h := hu1.symm.trans h1
      have h' : ((u ⟨l, hl⟩ : ℂ) - 1) * ((q : ℂ) - 1) = 0 := by linear_combination h
      have h'' := sub_eq_zero.mp ((mul_eq_zero.mp h').resolve_right hq1)
      exact_mod_cast h''
    refine ⟨hθ, hStab, h1, ?_, fun y hy => ?_, hu1'⟩
    · change (basisH.representation l).character (Ψ ⟨1, σ₀⟩) =
        ((p ^ (f / Nat.card Sigma) : ℕ) : ℂ) - 1
      rw [hval, hu1', Nat.cast_one, one_mul, Nat.cast_pow]
    · change (basisH.representation l).character y = ΦH y - 1
      rw [huodd y hy, hu1', Nat.cast_one, one_mul]
      rfl
  have hinjlam : Function.Injective lam := (nonsplitCharacterEquiv F b (2 ^ n)
    (wreathModulus_pos n) (wreathModulus_even hn) E basis h2 z₀ hz₀).injective
  have hwm : ∀ P, wm (lam P) = lam (weylP P) := fun P =>
    nonsplitCharacter_comp_minusWeylConj h2 z₀ hz₀ y₀ hy₀ P
  have hfinP : Finite (NonsplitParameter F E b (2 ^ n) h2 z₀ hz₀) :=
    Nat.finite_of_card_ne_zero (by
      rw [card_nonsplitParameter F b (2 ^ n) (wreathModulus_pos n) E basis h2 z₀ hz₀]
      exact Nat.mul_ne_zero (by omega) (wreathModulus_pos n).ne')
  have hD₂fin : D₂.Finite := (Set.toFinite Par2).image _
  have hD₂card : D₂.ncard = 2 ^ n * (κm - 1) / 2 :=
    ncard_twoPrimaryCuspidal hpo hb h2 z₀ hz₀ y₀ hy₀ hψ
  have hD₂mem : ∀ l ∈ CH, res (chr l) ∈ D₂ := by
    intro l hl
    obtain ⟨hθ, -, -, -, hodd, -⟩ := hCfacts l hl
    obtain ⟨P, hP, hPθ⟩ := cuspidalLabel_mem_twoPrimary hn hp hpodd hdata hΦ hθ hodd E basis h2
      z₀ y₀ hz₀ hy₀ hψ
    exact ⟨P, hP, hPθ.symm⟩
  have hξirr : ∀ l, (fun g => chr l (Ψ g)) ∈ BlocksIrr Hh := fun l =>
    Semidihedral.Principal.comp_mem_blocksIrr Ψ.toMonoidHom Ψ.surjective
      (CFSG.BlockBasics.basis_character_mem_irr basisH l)
  have hinj : Set.InjOn (fun l => res (chr l)) ↑CH := by
    intro l₁ hl₁ l₂ hl₂ hres
    obtain ⟨hθ₁, hStab₁, -, hv₁, -, -⟩ := hCfacts l₁ hl₁
    obtain ⟨-, -, -, hv₂, -, -⟩ := hCfacts l₂ hl₂
    have heq := eq_of_restrict_eq_of_generator_value hSigma hgen hθ₁.1 hStab₁ (hξirr l₁)
      (hξirr l₂) rfl hres.symm (hv₁.trans hv₂.symm) (by rw [hv₁]; exact hq₀1)
    apply basisH.distinct
    funext h
    have := congrFun heq (Ψ.symm h)
    simpa using this
  have hpart : 2 ^ (Nat.card F ^ 2 - 1).factorization 2 = 2 * 2 ^ n := by
    rw [hdata.card]
    exact hloc.qTwoPart
  have hqodd : Nat.card F % 2 = 1 := by
    rw [hdata.card]
    exact Nat.odd_iff.mp hpo.pow
  have hε : ε = 1 ∨ ε = -1 := by
    by_cases h : Nat.card F % 4 = 1
    · exact Or.inl (ite_eq_left h)
    · exact Or.inr (ite_eq_right h)
  have hq4 : ε = 1 → Nat.card F % 4 = 1 := by
    intro h1
    by_contra h
    have : ε = -1 := ite_eq_right h
    rw [this] at h1
    norm_num at h1
  have hq4' : ε = -1 → Nat.card F % 4 = 3 := by
    intro h2'
    by_contra h
    have h1 : Nat.card F % 4 = 1 := by omega
    have : ε = 1 := ite_eq_left h1
    rw [this] at h2'
    norm_num at h2'
  have hκm1 : ε = 1 → κm = 2 := fun h => two_pow_factorization_succ_of_mod_four_one (hq4 h)
  have hκm2 : ε = -1 → κm = 2 ^ n := fun h => by
    change 2 ^ (Nat.card F + 1).factorization 2 = 2 ^ n
    rw [two_part_square_sub_one_nonsplit _ n hq3 (hq4' h) hpart]
  have hCHcard : CH.card = 2 ^ n * (κm - 1) / 2 := by
    have hsumu : ∑ χ, u χ ^ 2 = CH.card := by
      rw [Finset.sum_congr rfl fun χ _ => by rw [(hCfacts χ.1 χ.2).2.2.2.2.2, one_pow],
        Finset.sum_const, Finset.card_univ, smul_eq_mul, mul_one, Fintype.card_coe]
    rcases hε with h | h
    · rw [← hsumu, hsum1 h, hκm1 h]
      simp
    · rw [← hsumu, hsum2 h, hκm2 h]
  have hbij : Set.BijOn (fun l => res (chr l)) ↑CH D₂ := by
    refine ⟨fun l hl => hD₂mem l hl, hinj, ?_⟩
    have hsub : (fun l => res (chr l)) '' ↑CH ⊆ D₂ := by
      rintro _ ⟨l, hl, rfl⟩
      exact hD₂mem l hl
    have himg : (fun l => res (chr l)) '' ↑CH = D₂ :=
      Set.eq_of_subset_of_ncard_le hsub (by
        rw [hinj.ncard_image, Set.ncard_coe_finset, hCHcard, hD₂card]) hD₂fin
    intro θ hθ
    rw [← himg] at hθ
    exact hθ
  have hD₂res : ∀ θ ∈ D₂, ∃ l ∈ CH, res (chr l) = θ := fun θ hθ => hbij.2.2 hθ
  have hinv : ∀ θ ∈ D₂, ∀ σ : Sigma, fieldTwist hSigma σ θ = θ := by
    intro θ hθ σ
    obtain ⟨l, hl, rfl⟩ := hD₂res θ hθ
    have hσ : σ ∈ twistStabilizer hSigma (res (chr l)) := by
      rw [(hCfacts l hl).2.1]
      exact Subgroup.mem_top σ
    exact hσ
  have hθdeg : ∀ θ ∈ D₂, θ 1 = (q : ℂ) - 1 := by
    rintro θ ⟨P, -, rfl⟩
    exact cuspidalCharacter_one hb ψ (lam P)
  have huniqC : ∀ θ ∈ D₂, ∀ l' ∈ B0, res (chr l') = θ → l' ∈ CH := by
    intro θ hθ l' hl' hres
    apply mem_cuspidalLabels_of_degree basisH ideal principalH hq3 hℓ1 hΦ1 hPH1 hl' odd_one
    rw [Nat.cast_one, one_mul, ← hθdeg θ hθ, ← hres]
    change chr l' 1 = chr l' (Ψ (SemidirectProduct.inl 1))
    rw [map_one, map_one]
  have hunique : ∀ θ ∈ D₂, ∃! l, l ∈ B0 ∧ res (chr l) = θ := by
    intro θ hθ
    obtain ⟨l, hl, hlθ⟩ := hD₂res θ hθ
    refine ⟨l, ⟨Finset.sdiff_subset hl, hlθ⟩, fun l' hl' => ?_⟩
    exact hinj (huniqC θ hθ l' hl'.1 hl'.2) hl (hl'.2.trans hlθ.symm)
  have htrace : ∀ θ ∈ D₂, ∀ (V : Type) [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
      (R : Representation ℂ K V), R.IsIrreducible → R.character = θ →
      (∃ T : (Module.End ℂ V)ˣ, (∀ k, (T : Module.End ℂ V) * R k *
        ((T⁻¹ : (Module.End ℂ V)ˣ) : Module.End ℂ V) = R (σact k)) ∧ T ^ d = 1) ∧
      ∀ T : (Module.End ℂ V)ˣ, (∀ k, (T : Module.End ℂ V) * R k *
        ((T⁻¹ : (Module.End ℂ V)ˣ) : Module.End ℂ V) = R (σact k)) → T ^ d = 1 →
        let c : ℂ := ((q₀ : ℂ) - 1) / LinearMap.trace ℂ V (T : Module.End ℂ V)
        LinearMap.trace ℂ V (T : Module.End ℂ V) ≠ 0 ∧ c ^ d = 1 ∧
        (∃ ρ' : Representation ℂ Hh V, ∀ (k : K) (j : ℕ),
          ρ' ⟨k, σ₀ ^ j⟩ = R k * (c • (T : Module.End ℂ V)) ^ j) ∧
        (∀ ρ' : Representation ℂ Hh V, (∀ (k : K) (j : ℕ),
          ρ' ⟨k, σ₀ ^ j⟩ = R k * (c • (T : Module.End ℂ V)) ^ j) →
          ∃ l ∈ CH, res (chr l) = θ ∧ chr l = fun h => ρ'.character (Ψ.symm h)) ∧
        ∀ ω : ℂ, ω ^ d = 1 →
          (∃ ρ' : Representation ℂ Hh V, ∀ (k : K) (j : ℕ),
            ρ' ⟨k, σ₀ ^ j⟩ = R k * (ω • (T : Module.End ℂ V)) ^ j) ∧
          ∀ ρ' : Representation ℂ Hh V, (∀ (k : K) (j : ℕ),
            ρ' ⟨k, σ₀ ^ j⟩ = R k * (ω • (T : Module.End ℂ V)) ^ j) →
            ((∃ l ∈ B0, chr l = fun h => ρ'.character (Ψ.symm h)) ↔ ω = c) := by
    intro θ hθ V _ _ _ R hR hRθ
    obtain ⟨l, hl, hlθ⟩ := hD₂res θ hθ
    obtain ⟨hθc, hStab, -, hv, -, -⟩ := hCfacts l hl
    rw [hlθ] at hθc hStab
    have hinvR : ∀ k, R.character (σact k) = R.character k := by
      intro k
      rw [hRθ]
      have hσ : σ₀⁻¹ ∈ twistStabilizer hSigma θ := by
        rw [hStab]
        exact Subgroup.mem_top _
      have h := congrFun ((mem_twistStabilizer_iff hSigma θ σ₀⁻¹).mp hσ) k
      rw [fieldTwist_apply, inv_inv] at h
      exact h
    refine ⟨exists_normalized_intertwiner hSigma hgen R hR hinvR, fun T hT hTd => ?_⟩
    obtain ⟨htr, hcd, hiff⟩ := trace_normalization hSigma hgen hθc.1 hStab (hξirr l) hlθ hv
      hq₀1 R hR hRθ T hT hTd
    have hresρ : ∀ (ω : ℂ) (ρ' : Representation ℂ Hh V), (∀ (k : K) (j : ℕ),
        ρ' ⟨k, σ₀ ^ j⟩ = R k * (ω • (T : Module.End ℂ V)) ^ j) →
        res (fun h => ρ'.character (Ψ.symm h)) = θ := by
      intro ω ρ' hρ'
      have hcomp := semilinear_representation_comp_inl hSigma R _ ρ' hρ'
      rw [← hRθ]
      funext k
      change ρ'.character (Ψ.symm (Ψ (SemidirectProduct.inl k))) = R.character k
      rw [MulEquiv.symm_apply_apply]
      change LinearMap.trace ℂ V (ρ' (SemidirectProduct.inl k)) = LinearMap.trace ℂ V (R k)
      rw [← MonoidHom.comp_apply, hcomp]
    refine ⟨htr, hcd, exists_scaled_semilinear_representation hSigma hgen R T hT hTd hcd,
      fun ρ' hρ' => ?_, fun ω hω =>
        ⟨exists_scaled_semilinear_representation hSigma hgen R T hT hTd hω, fun ρ' hρ' => ?_⟩⟩
    · have hc := (hiff _ ρ' hρ').mpr rfl
      refine ⟨l, hl, hlθ, ?_⟩
      funext h
      rw [hc]
      exact (congrArg (chr l) (MulEquiv.apply_symm_apply Ψ h)).symm
    · constructor
      · rintro ⟨l', hl', hl'χ⟩
        have hres' : res (chr l') = θ := by
          rw [hl'χ]
          exact hresρ ω ρ' hρ'
        have hl'l : l' = l := hinj (huniqC θ hθ l' hl' hres') hl (hres'.trans hlθ.symm)
        subst hl'l
        apply (hiff ω ρ' hρ').mp
        funext g
        have h := congrFun hl'χ (Ψ g)
        rw [MulEquiv.symm_apply_apply] at h
        exact h.symm
      · intro hωc
        refine ⟨l, Finset.sdiff_subset hl, ?_⟩
        funext h
        rw [(hiff ω ρ' hρ').mpr hωc]
        exact (congrArg (chr l) (MulEquiv.apply_symm_apply Ψ h)).symm
  have hTNeq : chr '' ↑CH = TN := by
    ext χ
    constructor
    · rintro ⟨l, hl, rfl⟩
      have hθ := hD₂mem l hl
      obtain ⟨V, i₁, i₂, i₃, R, hR, hRθ⟩ := (hCfacts l hl).1.1
      obtain ⟨⟨T, hT, hTd⟩, hTall⟩ := htrace _ hθ V R hR hRθ
      obtain ⟨-, -, ⟨ρ', hρ'⟩, hρ'char, -⟩ := hTall T hT hTd
      obtain ⟨l', hl', hl'θ, hl'χ⟩ := hρ'char ρ' hρ'
      have hll' : l' = l := hinj hl' hl hl'θ
      subst hll'
      exact ⟨_, hθ, V, i₁, i₂, i₃, R, T, ρ', hR, hRθ, hT, hTd, hρ', hl'χ⟩
    · rintro ⟨θ, hθ, V, i₁, i₂, i₃, R, T, ρ', hR, hRθ, hT, hTd, hρ', rfl⟩
      obtain ⟨-, hTall⟩ := htrace θ hθ V R hR hRθ
      obtain ⟨-, -, -, hρ'char, -⟩ := hTall T hT hTd
      obtain ⟨l, hl, -, hlχ⟩ := hρ'char ρ' hρ'
      exact ⟨l, hl, hlχ⟩
  have hTNindep : ∀ χ₁ ∈ TN, ∀ χ₂ ∈ TN, res χ₁ = res χ₂ → χ₁ = χ₂ := by
    intro χ₁ h₁ χ₂ h₂ hres
    rw [← hTNeq] at h₁ h₂
    obtain ⟨l₁, hl₁, rfl⟩ := h₁
    obtain ⟨l₂, hl₂, rfl⟩ := h₂
    rw [hinj hl₁ hl₂ hres]
  have hΘO : ∀ θ : K → ℂ, θ ∈ BlocksIrr K → θ 1 = (q : ℂ) - 1 →
      ∀ χ : I θ → ℂ, χ ∈ BlocksIrr (I θ) →
        (∀ (g : K) (hg : (SemidirectProduct.inl g : Hh) ∈ I θ),
          χ ⟨SemidirectProduct.inl g, hg⟩ = θ g) →
      ∀ ν : twistStabilizer hSigma θ →* ℂˣ,
        ((∃ l ∈ B0, chr l = fun h => ΘO θ χ ν (Ψ.symm h)) ↔
          {θ' | ∃ σ : Sigma, θ' = fieldTwist hSigma σ θ} = {θ} ∧ θ ∈ D₂ ∧
            ∃ hσ : σ₀ ∈ twistStabilizer hSigma θ,
              (ν ⟨σ₀, hσ⟩ : ℂ) = ((q₀ : ℂ) - 1) / χ ⟨t₀, hσ⟩) ∧
        ((∃ l ∈ B0, chr l = fun h => ΘO θ χ ν (Ψ.symm h)) →
          twistStabilizer hSigma θ = ⊤ ∧
            ∀ hσ : σ₀ ∈ twistStabilizer hSigma θ, χ ⟨t₀, hσ⟩ ≠ 0) := by
    intro θ hθ hθ1 χ hχ hres ν
    have hΘ : ΘO θ χ ν = twistInduced hSigma θ χ ν := rfl
    obtain ⟨hdeg, -, -, -, -⟩ := twist_clifford hSigma hθ hχ hres
    obtain ⟨hΘirr, hΘ1⟩ := hdeg ν
    have hmemt : ∀ hσ : σ₀ ∈ twistStabilizer hSigma θ, t₀ ∈ I θ := fun hσ => hσ
    have hfwd : (∃ l ∈ B0, chr l = fun h => ΘO θ χ ν (Ψ.symm h)) →
        twistStabilizer hSigma θ = ⊤ ∧ ∃ l ∈ CH, chr l = fun h => ΘO θ χ ν (Ψ.symm h) := by
      rintro ⟨l, hl, hlΘ⟩
      have hidx : Odd (twistStabilizer hSigma θ).index :=
        hd.of_dvd_nat (Subgroup.index_dvd_card _)
      have hl1 : chr l 1 = ((twistStabilizer hSigma θ).index : ℂ) * ((q : ℂ) - 1) := by
        rw [hlΘ]
        change ΘO θ χ ν (Ψ.symm 1) = _
        rw [map_one, hΘ, hΘ1, hθ1]
      have hlC := mem_cuspidalLabels_of_degree basisH ideal principalH hq3 hℓ1 hΦ1 hPH1 hl hidx hl1
      obtain ⟨-, -, -, hv, -, -⟩ := hCfacts l hlC
      have hne : twistInduced hSigma θ χ ν ⟨1, σ₀⟩ ≠ 0 := by
        have h := congrFun hlΘ (Ψ t₀)
        rw [hv, MulEquiv.symm_apply_apply] at h
        rw [← hΘ]
        change ΘO θ χ ν t₀ ≠ 0
        rw [← h]
        exact hq₀1
      have hσ := mem_twistStabilizer_of_twistInduced_ne_zero hSigma hθ hχ hres ν 1 σ₀ hne
      exact ⟨eq_top_of_generator_mem hgen hσ, l, hlC, hlΘ⟩
    have hval : ∀ (hStab : twistStabilizer hSigma θ = ⊤) (hσ : σ₀ ∈ twistStabilizer hSigma θ),
        ΘO θ χ ν t₀ = χ ⟨t₀, hmemt hσ⟩ * (ν ⟨σ₀, hσ⟩ : ℂ) := fun hStab hσ =>
      twistInduced_of_top hSigma hStab hχ ν t₀ (hmemt hσ)
    refine ⟨⟨fun hprin => ?_, fun ⟨horb, hθD, hσ, hνv⟩ => ?_⟩, fun hprin => ?_⟩
    · obtain ⟨hStab, l, hlC, hlΘ⟩ := hfwd hprin
      obtain ⟨-, -, -, hv, -, -⟩ := hCfacts l hlC
      have hσ : σ₀ ∈ twistStabilizer hSigma θ := by
        rw [hStab]
        exact Subgroup.mem_top _
      have hlres : res (chr l) = θ := by
        rw [hlΘ]
        funext g
        change ΘO θ χ ν (Ψ.symm (Ψ (SemidirectProduct.inl g))) = θ g
        rw [MulEquiv.symm_apply_apply]
        exact congrFun (twistInduced_inl_of_top hSigma hStab hχ hres ν) g
      have hvt : ΘO θ χ ν t₀ = (q₀ : ℂ) - 1 := by
        have h := congrFun hlΘ (Ψ t₀)
        rw [hv, MulEquiv.symm_apply_apply] at h
        exact h.symm
      have hχ0 : χ ⟨t₀, hmemt hσ⟩ ≠ 0 := by
        intro h0
        rw [hval hStab hσ, h0, zero_mul] at hvt
        exact hq₀1 hvt.symm
      refine ⟨?_, hlres ▸ hD₂mem l hlC, hσ, ?_⟩
      · ext θ'
        simp only [Set.mem_ofPred_eq, Set.mem_singleton_iff]
        constructor
        · rintro ⟨τ, rfl⟩
          have hτ : τ ∈ twistStabilizer hSigma θ := by
            rw [hStab]
            exact Subgroup.mem_top _
          exact hτ
        · rintro rfl
          exact ⟨1, (fieldTwist_one hSigma θ').symm⟩
      · rw [hval hStab hσ] at hvt
        rw [← hvt]
        field_simp
    ·
      have hStab : twistStabilizer hSigma θ = ⊤ := by
        rw [eq_top_iff]
        intro τ _
        have h : fieldTwist hSigma τ θ ∈ {θ' | ∃ σ : Sigma, θ' = fieldTwist hSigma σ θ} :=
          ⟨τ, rfl⟩
        rw [horb] at h
        exact h
      obtain ⟨l, hl, hlθ⟩ := hD₂res θ hθD
      obtain ⟨-, -, -, hv, -, -⟩ := hCfacts l hl
      have hχ0 : χ ⟨t₀, hmemt hσ⟩ ≠ 0 := by
        intro h0
        rw [h0, div_zero] at hνv
        exact Units.ne_zero _ hνv
      have hvt : ΘO θ χ ν t₀ = (q₀ : ℂ) - 1 := by
        rw [hval hStab hσ, hνv]
        field_simp
      have heq := eq_of_restrict_eq_of_generator_value hSigma hgen hθ hStab hΘirr (hξirr l)
        (twistInduced_inl_of_top hSigma hStab hχ hres ν) hlθ (hvt.trans hv.symm)
        (by rw [← hΘ]; change ΘO θ χ ν t₀ ≠ 0; rw [hvt]; exact hq₀1)
      refine ⟨l, Finset.sdiff_subset hl, ?_⟩
      funext h
      rw [hΘ, heq]
      exact (congrArg (chr l) (MulEquiv.apply_symm_apply Ψ h)).symm
    · obtain ⟨hStab, l, hlC, hlΘ⟩ := hfwd hprin
      obtain ⟨-, -, -, hv, -, -⟩ := hCfacts l hlC
      refine ⟨hStab, fun hσ h0 => ?_⟩
      have hvt : ΘO θ χ ν t₀ = (q₀ : ℂ) - 1 := by
        have h := congrFun hlΘ (Ψ t₀)
        rw [hv, MulEquiv.symm_apply_apply] at h
        exact h.symm
      rw [hval hStab hσ, h0, zero_mul] at hvt
      exact hq₀1 hvt.symm
  have hlab₁ : ∀ r : Fin (2 ^ n), ∃ l ∈ B0, chr l = ℓ r := fun r => by
    obtain ⟨l, hl, hlc⟩ := (hDataH.lam_principal r 0).mpr rfl
    exact ⟨l, hl, hlc.trans (funext fun h => hℓ r h)⟩
  have hlab₂ : ∀ r : Fin (2 ^ n), ∃ l ∈ B0, chr l = fun h => ℓ r h * ΦH h := fun r => by
    obtain ⟨l, hl, hlc⟩ := (hDataH.xi_principal r 0).mpr rfl
    exact ⟨l, hl, hlc.trans (funext fun h => congrArg (· * ΦH h) (hℓ r h))⟩
  choose lbl₁ hlbl₁B hlbl₁ using hlab₁
  choose lbl₂ hlbl₂B hlbl₂ using hlab₂
  have hfam := hDataH.family_injective
  have hℓinj : Function.Injective ℓ := by
    intro r r' h
    have h' := @hfam (Sum.inl r) (Sum.inl r') (by
      funext y
      simp only [Sum.elim_inl]
      rw [hℓ, hℓ]
      exact congrFun h y)
    exact Sum.inl_injective h'
  have hℓΦinj : Function.Injective fun r => fun h => ℓ r h * ΦH h := by
    intro r r' h
    have h' := @hfam (Sum.inr r) (Sum.inr r') (by
      funext y
      simp only [Sum.elim_inr, MonoidHom.id_apply]
      rw [hℓ, hℓ]
      exact congrFun h y)
    exact Sum.inr_injective h'
  have hlbl₁inj : Function.Injective lbl₁ := fun r r' h =>
    hℓinj (by rw [← hlbl₁ r, ← hlbl₁ r', h])
  have hlbl₂inj : Function.Injective lbl₂ := fun r r' h =>
    hℓΦinj (by
      show (fun h => ℓ r h * ΦH h) = fun h => ℓ r' h * ΦH h
      rw [← hlbl₂ r, ← hlbl₂ r', h])
  have hFHeq : FH = Finset.univ.image lbl₁ ∪ Finset.univ.image lbl₂ := by
    ext l
    simp only [FH, linearAugmentationLabels, Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_union, Finset.mem_image]
    constructor
    · rintro ⟨r, hr | hr⟩
      · exact Or.inl ⟨r, basisH.distinct ((hlbl₁ r).trans hr.symm)⟩
      · exact Or.inr ⟨r, basisH.distinct ((hlbl₂ r).trans hr.symm)⟩
    · rintro (⟨r, rfl⟩ | ⟨r, rfl⟩)
      · exact ⟨r, Or.inl (hlbl₁ r)⟩
      · exact ⟨r, Or.inr (hlbl₂ r)⟩
  have hFHsub : FH ⊆ B0 := by
    rw [hFHeq]
    refine Finset.union_subset ?_ ?_
    · intro l hl
      obtain ⟨r, -, rfl⟩ := Finset.mem_image.mp hl
      exact hlbl₁B r
    · intro l hl
      obtain ⟨r, -, rfl⟩ := Finset.mem_image.mp hl
      exact hlbl₂B r
  have hB0 : B0 = FH ∪ PL ∪ CH :=
    (Finset.union_sdiff_of_subset (Finset.union_subset hFHsub hDH.series_subset)).symm
  have hq1C : (1 : ℂ) ≠ q := by
    rw [← Nat.cast_one, Ne, Nat.cast_inj]
    omega
  have hdeg : B0.val.map (fun l => chr l 1) = Multiset.replicate (2 ^ n) 1 +
      Multiset.replicate (2 ^ n) (q : ℂ) +
      Multiset.replicate (2 ^ n * (κp - 1) / 2) ((q : ℂ) + 1) +
      Multiset.replicate (2 ^ n * (κm - 1) / 2) ((q : ℂ) - 1) := by
    have hcard₁ : (Finset.univ.image lbl₁).card = 2 ^ n := by
      rw [Finset.card_image_of_injective _ hlbl₁inj, Finset.card_univ, Fintype.card_fin]
    have hcard₂ : (Finset.univ.image lbl₂).card = 2 ^ n := by
      rw [Finset.card_image_of_injective _ hlbl₂inj, Finset.card_univ, Fintype.card_fin]
    have h4 := map_val_eq_replicate_four B0 (Finset.univ.image lbl₁) (Finset.univ.image lbl₂) PL CH
      (fun l => chr l 1) 1 (q : ℂ) ((q : ℂ) + 1) ((q : ℂ) - 1) (by rw [hB0, hFHeq]) ?_ ?_ ?_ ?_
      ?_ ?_ ?_ ?_ ?_ ?_
    · rw [h4, hcard₁, hcard₂, hDH.series_card, hCHcard]
    · intro l hl
      obtain ⟨r, -, rfl⟩ := Finset.mem_image.mp hl
      rw [hlbl₁ r, hℓ1]
    · intro l hl
      obtain ⟨r, -, rfl⟩ := Finset.mem_image.mp hl
      rw [hlbl₂ r]
      dsimp only
      rw [hℓ1, one_mul, hΦ1]
    · intro l hl
      simp only [PL, principalSeriesLabels, Finset.mem_filter, Finset.mem_univ, true_and] at hl
      obtain ⟨θ, hθ, hlθ⟩ := hl
      change (basisH.representation l).character 1 = _
      rw [hlθ]
      exact hPH1 θ hθ
    · intro l hl
      exact (hCfacts l hl).2.2.1
    · exact hq1C
    · intro h
      have : (0 : ℂ) = q := by linear_combination h
      exact_mod_cast (show (0 : ℕ) ≠ q by omega) (by exact_mod_cast this)
    · intro h
      have : ((2 : ℕ) : ℂ) = q := by push_cast; linear_combination h
      exact (show (2 : ℕ) ≠ q by omega) (by exact_mod_cast this)
    · intro h
      have : (0 : ℂ) = 1 := by linear_combination h
      exact zero_ne_one this
    · intro h
      have : (1 : ℂ) = 0 := by linear_combination h
      exact one_ne_zero this
    · intro h
      have : (2 : ℂ) = 0 := by linear_combination h
      exact two_ne_zero this
  have hB0card : B0.card = 2 ^ n * (2 ^ n + 4) / 2 := by
    have h := congrArg Multiset.card hdeg
    rw [Multiset.card_map, Multiset.card_add, Multiset.card_add, Multiset.card_add,
      Multiset.card_replicate, Multiset.card_replicate, Multiset.card_replicate,
      Multiset.card_replicate] at h
    change B0.card = _ at h
    rw [h]
    apply block_card_arithmetic hn
    rcases hε with h1 | h1
    · exact Or.inl ⟨hκ1 h1, hκm1 h1⟩
    · exact Or.inr ⟨hκ2 h1, hκm2 h1⟩
  have hidimg : ∀ X : Set (Hc → ℂ), (fun (χ : Hc → ℂ) (y : Hc) => χ (MonoidHom.id Hc y)) '' X =
      X := by
    intro X
    ext χ
    simp
  have hPDH : CuspidalSelectionPullbackData basisH ideal principalH (MonoidHom.id Hc) ℓ ΦH PH
      BH TN D₂ res q κp κm := by
    refine ⟨?_, ?_, fun l hl y hy => (hCfacts l hl).2.2.2.2.1 y hy, fun θ hθ => ?_, hdeg,
      hCHcard, hB0card⟩
    · rw [hidimg]
      change chr '' ↑B0 = chr '' ↑(FH ∪ PL ∪ CH)
      rw [← hB0]
    · rw [hidimg]
      exact hTNeq
    · obtain ⟨l, hl, hlθ⟩ := hD₂res θ hθ
      refine ⟨l, ⟨hl, chr l, hTNeq ▸ ⟨l, hl, rfl⟩, rfl, hlθ⟩, ?_⟩
      rintro l'' ⟨hl''C, χ'', -, hl''χ, hres''⟩
      have h : res (chr l'') = θ := by
        rw [← hres'']
        congr 1
      exact hinj hl''C hl (h.trans hlθ.symm)
  have hπ : Function.Surjective π := centralizerOddCoreMap_surjective n S e
  have hPDN := cuspidalSelectionPullbackData_of_correspondence basisH basisN ideal principalH
    principalN π hπ hTNcorr hPDH
  have hD₂alt : D₂ = Λ '' {μ | wm μ ≠ μ ∧ ∃ k : ℕ, orderOf μ = 2 ^ k} := by
    ext θ
    constructor
    · rintro ⟨P, ⟨hP1, hP2⟩, rfl⟩
      refine ⟨lam P, ⟨fun h => hP1 ((minusWeyl_fixed_iff hb y₀ hy₀ h2 z₀ hz₀ P).mp h), ?_⟩, rfl⟩
      exact (nonsplitCharacter_two_pow_iff F E basis b (wreathModulus_pos n)
        (wreathModulus_even hn) h2 z₀ hz₀ rfl P).mpr hP2
    · rintro ⟨μ, ⟨hμ1, hμ2⟩, rfl⟩
      set eqv := nonsplitCharacterEquiv F b (2 ^ n) (wreathModulus_pos n)
        (wreathModulus_even hn) E basis h2 z₀ hz₀ with heqv
      have hμP : μ = lam (eqv.symm μ) := (eqv.apply_symm_apply μ).symm
      refine ⟨eqv.symm μ, ⟨fun h => hμ1 ?_, ?_⟩, ?_⟩
      · rw [hμP]
        exact (minusWeyl_fixed_iff hb y₀ hy₀ h2 z₀ hz₀ _).mpr h
      · have hμ' : nonsplitCharacter F b (2 ^ n) (wreathModulus_pos n) (wreathModulus_even hn) E
            basis h2 z₀ hz₀ (eqv.symm μ) = μ := eqv.apply_symm_apply μ
        rw [← nonsplitCharacter_two_pow_iff F E basis b (wreathModulus_pos n)
          (wreathModulus_even hn) h2 z₀ hz₀ rfl, hμ']
        exact hμ2
      · change Λ (lam (eqv.symm μ)) = Λ μ
        rw [← hμP]
  have hD₂irr : ∀ θ ∈ D₂, θ ∈ BlocksIrr K ∧ θ 1 = (q : ℂ) - 1 := by
    rintro θ ⟨P, ⟨hP1, -⟩, rfl⟩
    refine ⟨cuspidalCharacter_mem_blocksIrr hpo hb y₀ hy₀ h2 hψ (lam P) fun h =>
      hP1 ((minusWeyl_fixed_iff hb y₀ hy₀ h2 z₀ hz₀ P).mp h), cuspidalCharacter_one hb ψ (lam P)⟩
  have hC7 : ∀ l ∈ CH, res (chr l) ∈ BlocksIrr K ∧ chr l 1 = (q : ℂ) - 1 ∧
      chr l (Ψ t₀) = (q₀ : ℂ) - 1 ∧ ∀ y : Hc, Odd (orderOf y) → chr l y = ΦH y - 1 := by
    intro l hl
    obtain ⟨hθ, -, h1, hv, hodd, -⟩ := hCfacts l hl
    exact ⟨hθ.1, h1, hv, hodd⟩
  refine ⟨hq₀, fun P => nonsplitCharacter_spec F b (2 ^ n) (wreathModulus_pos n)
      (wreathModulus_even hn) E basis h2 z₀ hz₀ P,
    (nonsplitCharacterEquiv F b (2 ^ n) (wreathModulus_pos n) (wreathModulus_even hn) E basis h2
      z₀ hz₀).bijective, fun P => ⟨hwm P, rfl,
        nonsplitWeylParameter_involutive F b (2 ^ n) (wreathModulus_even hn) E basis h2 z₀ hz₀ P,
        fun hP h => hP ((nonsplitWeylParameter_eq_self_iff F b (2 ^ n) (wreathModulus_even hn) E
          basis h2 z₀ hz₀ hb P).mp h)⟩,
    fun P hP => (nonsplitWeylParameter_two_pow hb h2 z₀ hz₀ hP).1, hD₂irr, hD₂alt,
    fun P hP P' _ => cuspidalCharacter_nonsplit_eq_iff hpo hb h2 z₀ hz₀ y₀ hy₀ hψ hP.1, hD₂card,
    hC7, hbij, hinv, hunique, htrace, hTNeq, hTNindep, hΘO, hB0, hκm1, hκm2, hPDH, hPDN, ?_⟩
  intro j hj basisC principalC hprincipalC
  obtain ⟨hdataj, -, -, hTC⟩ := hCprev j hj basisC principalC hprincipalC
  exact ⟨hdataj, cuspidalSelectionPullbackData_of_correspondence basisH basisC ideal principalH
    principalC _ hdataj.map_surjective hTC hPDH⟩

theorem conditional_actual_principal_cuspidal_selection_and_full_degree_counts
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
        hSigma ≃* centralizerOddCoreQuotient n S e)
      (hdata : ConditionalCompatibleModelData n hn S e p f F Sigma b hSigma ρ Ψ)
      (σ₀ : Sigma) (_hgen : ∀ σ : Sigma, σ ∈ Subgroup.zpowers σ₀) (ζm : ℂ)
      (hζm : IsPrimitiveRoot ζm (2 ^ n))
      (E : Type) [Field E] [Algebra F E] (basis : Module.Basis (Fin 2) F E) (z₀ y₀ : Eˣ)
      (hz₀ : (z₀ : E) * (z₀ : E) ^ Nat.card F = algebraMap F E b)
      (hy₀ : (y₀ : E) * (y₀ : E) ^ Nat.card F = -1) (ψ : AddChar F ℂ) (_hψ : ψ ≠ 1),
      let hb : ¬ IsSquare b := hdata.nonsquare
      let h2 : (2 : F) ≠ 0 := two_ne_zero_of_not_isSquare hb
      let q := Nat.card F
      let d := Nat.card Sigma
      let q₀ := p ^ (f / d)
      let κp := 2 ^ (Nat.card F - 1).factorization 2
      let κm := 2 ^ (Nat.card F + 1).factorization 2
      let Hc := centralizerOddCoreQuotient n S e
      let K := CentralExtension F b (2 ^ n) (wreathModulus_pos n) (wreathModulus_even hn)
      let Hh := SemilinearExtension F b (2 ^ n) (wreathModulus_pos n) (wreathModulus_even hn)
        Sigma hSigma
      let t₀ : Hh := ⟨1, σ₀⟩
      let σact := fieldAction F b (2 ^ n) (wreathModulus_pos n) (wreathModulus_even hn) Sigma
        hSigma σ₀
      let ΦH : Hc → ℂ := fun h =>
        (Nat.card {x : Omega F // ((ρ (centralizerFullQuotientMap n hn S e h) : coordinateE F) :
          Equiv.Perm (Omega F)) x = x} : ℂ) - 1
      let ε : ℤ := if Nat.card F % 4 = 1 then 1 else -1
      let π := centralizerOddCoreMap n S e
      let Θ : ((P : PrincipalSeriesParameter F b (2 ^ n)) ×
          (parameterStabilizer hSigma P →* ℂˣ)) → Hc → ℂ :=
        fun x h => principalInduced (hm := wreathModulus_pos n) (heven := wreathModulus_even hn)
          hSigma x.1 x.2 (Ψ.symm h)
      let B0 := coefficientBlock basisH (localizedComplexIntegerRing ideal) principalH
      let chr : basisH.index → Hc → ℂ := fun l => (basisH.representation l).character
      let PH : Set (Hc → ℂ) := {θ | ∃ x, x.1.1.1 ≠ 1 ∧ θ = Θ x ∧ ∃ l ∈ B0, chr l = θ}
      let ℓ : Fin (2 ^ n) → Hc → ℂ := fun r h =>
        (CentralSL2Abelianization.rootCharacter (2 ^ n) (wreathModulus_pos n) ζm hζm r.val
          (CentralSL2Abelianization.psi F b (2 ^ n) (wreathModulus_pos n) (wreathModulus_even hn)
            Sigma hSigma (Ψ.symm h)).1 : ℂ)
      let FH := linearAugmentationLabels basisH (MonoidHom.id Hc) ℓ ΦH
      let PL := principalSeriesLabels basisH (MonoidHom.id Hc) PH
      let CH := cuspidalLabels basisH ideal principalH (MonoidHom.id Hc) ℓ ΦH PH
      let res : (Hc → ℂ) → K → ℂ := fun χ g => χ (Ψ (SemidirectProduct.inl g))
      let Tm := nonsplitTorus F b (2 ^ n) (wreathModulus_pos n) (wreathModulus_even hn) E basis
      let lam := nonsplitCharacter F b (2 ^ n) (wreathModulus_pos n) (wreathModulus_even hn) E
        basis h2 z₀ hz₀
      let weylP := nonsplitWeylParameter F b (2 ^ n) (wreathModulus_even hn) E basis h2 z₀ hz₀
      let wm : (Tm →* ℂˣ) → (Tm →* ℂˣ) := fun μ => μ.comp (minusWeylConj h2 y₀ hy₀)
      let Λ : (Tm →* ℂˣ) → K → ℂ := fun μ =>
        inducedFunction (auSubgroup F b (2 ^ n) (wreathModulus_pos n) (wreathModulus_even hn))
          (fun g => auCharacter hb (restrictA hb μ) ψ g) -
        inducedFunction Tm fun t => (μ t : ℂ)
      let Par2 : Set (NonsplitParameter F E b (2 ^ n) h2 z₀ hz₀) :=
        {P | P.1.1 ≠ 1 ∧ ∃ k : ℕ, orderOf P.1.1 = 2 ^ k}
      let D₂ : Set (K → ℂ) := (fun P => Λ (lam P)) '' Par2
      let TN : Set (Hc → ℂ) := {χ | ∃ θ ∈ D₂, ∃ (V : Type) (_ : AddCommGroup V) (_ : Module ℂ V)
        (_ : FiniteDimensional ℂ V) (R : Representation ℂ K V) (T : (Module.End ℂ V)ˣ)
        (ρ' : Representation ℂ Hh V), R.IsIrreducible ∧ R.character = θ ∧
        (∀ k, (T : Module.End ℂ V) * R k * ((T⁻¹ : (Module.End ℂ V)ˣ) : Module.End ℂ V) =
          R (σact k)) ∧ T ^ d = 1 ∧
        (∀ (k : K) (j : ℕ), ρ' ⟨k, σ₀ ^ j⟩ = R k *
          ((((q₀ : ℂ) - 1) / LinearMap.trace ℂ V (T : Module.End ℂ V)) •
            (T : Module.End ℂ V)) ^ j) ∧
        χ = fun h => ρ'.character (Ψ.symm h)}
      let BH : Set (Hc → ℂ) := chr '' ↑(FH ∪ PL ∪ CH)
      let I : (K → ℂ) → Subgroup Hh := fun θ => semilinearInertia (twistStabilizer hSigma θ)
      let ΘO : (θ : K → ℂ) → (I θ → ℂ) → (twistStabilizer hSigma θ →* ℂˣ) → Hh → ℂ :=
        fun θ χ ν => inducedFunction (I θ) fun y => χ y * (ν ⟨(y : Hh).right, y.2⟩ : ℂ)
      1 < q₀ ∧
      (∀ P : NonsplitParameter F E b (2 ^ n) h2 z₀ hz₀,
        (∀ t, lam P ⟨nonsplitDiag F b (2 ^ n) (wreathModulus_pos n) (wreathModulus_even hn) E
          basis t, nonsplitDiag_mem t⟩ = P.1.1 t) ∧
        lam P ⟨nonsplitGenerator F b (2 ^ n) (wreathModulus_pos n) (wreathModulus_even hn) E
          basis z₀ hz₀, nonsplitGenerator_mem z₀ hz₀⟩ = P.1.2) ∧
      Function.Bijective lam ∧
      (∀ P : NonsplitParameter F E b (2 ^ n) h2 z₀ hz₀, wm (lam P) = lam (weylP P) ∧
        (weylP P).1 = (P.1.1⁻¹, P.1.1 (βE F E basis z₀) * P.1.2) ∧ weylP (weylP P) = P ∧
        (P.1.1 ≠ 1 → weylP P ≠ P)) ∧
      (∀ P ∈ Par2, weylP P ∈ Par2) ∧ (∀ θ ∈ D₂, θ ∈ BlocksIrr K ∧ θ 1 = (q : ℂ) - 1) ∧
      D₂ = Λ '' {μ | wm μ ≠ μ ∧ ∃ k : ℕ, orderOf μ = 2 ^ k} ∧
      (∀ P ∈ Par2, ∀ P' ∈ Par2, Λ (lam P) = Λ (lam P') ↔ P' = P ∨ P' = weylP P) ∧
      D₂.ncard = 2 ^ n * (κm - 1) / 2 ∧
      (∀ l ∈ CH, res (chr l) ∈ BlocksIrr K ∧ chr l 1 = (q : ℂ) - 1 ∧
        chr l (Ψ t₀) = (q₀ : ℂ) - 1 ∧ ∀ y : Hc, Odd (orderOf y) → chr l y = ΦH y - 1) ∧
      Set.BijOn (fun l => res (chr l)) ↑CH D₂ ∧
      (∀ θ ∈ D₂, ∀ σ : Sigma, fieldTwist hSigma σ θ = θ) ∧
      (∀ θ ∈ D₂, ∃! l, l ∈ B0 ∧ res (chr l) = θ) ∧
      (∀ θ ∈ D₂, ∀ (V : Type) [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
          (R : Representation ℂ K V), R.IsIrreducible → R.character = θ →
        (∃ T : (Module.End ℂ V)ˣ, (∀ k, (T : Module.End ℂ V) * R k *
          ((T⁻¹ : (Module.End ℂ V)ˣ) : Module.End ℂ V) = R (σact k)) ∧ T ^ d = 1) ∧
        ∀ T : (Module.End ℂ V)ˣ, (∀ k, (T : Module.End ℂ V) * R k *
          ((T⁻¹ : (Module.End ℂ V)ˣ) : Module.End ℂ V) = R (σact k)) → T ^ d = 1 →
          let c : ℂ := ((q₀ : ℂ) - 1) / LinearMap.trace ℂ V (T : Module.End ℂ V)
          LinearMap.trace ℂ V (T : Module.End ℂ V) ≠ 0 ∧ c ^ d = 1 ∧
          (∃ ρ' : Representation ℂ Hh V, ∀ (k : K) (j : ℕ),
            ρ' ⟨k, σ₀ ^ j⟩ = R k * (c • (T : Module.End ℂ V)) ^ j) ∧
          (∀ ρ' : Representation ℂ Hh V, (∀ (k : K) (j : ℕ),
            ρ' ⟨k, σ₀ ^ j⟩ = R k * (c • (T : Module.End ℂ V)) ^ j) →
            ∃ l ∈ CH, res (chr l) = θ ∧ chr l = fun h => ρ'.character (Ψ.symm h)) ∧
          ∀ ω : ℂ, ω ^ d = 1 →
            (∃ ρ' : Representation ℂ Hh V, ∀ (k : K) (j : ℕ),
              ρ' ⟨k, σ₀ ^ j⟩ = R k * (ω • (T : Module.End ℂ V)) ^ j) ∧
            ∀ ρ' : Representation ℂ Hh V, (∀ (k : K) (j : ℕ),
              ρ' ⟨k, σ₀ ^ j⟩ = R k * (ω • (T : Module.End ℂ V)) ^ j) →
              ((∃ l ∈ B0, chr l = fun h => ρ'.character (Ψ.symm h)) ↔ ω = c)) ∧
      chr '' ↑CH = TN ∧ (∀ χ₁ ∈ TN, ∀ χ₂ ∈ TN, res χ₁ = res χ₂ → χ₁ = χ₂) ∧
      (∀ θ : K → ℂ, θ ∈ BlocksIrr K → θ 1 = (q : ℂ) - 1 →
        ∀ χ : I θ → ℂ, χ ∈ BlocksIrr (I θ) →
          (∀ (g : K) (hg : (SemidirectProduct.inl g : Hh) ∈ I θ),
            χ ⟨SemidirectProduct.inl g, hg⟩ = θ g) →
        ∀ ν : twistStabilizer hSigma θ →* ℂˣ,
          ((∃ l ∈ B0, chr l = fun h => ΘO θ χ ν (Ψ.symm h)) ↔
            {θ' | ∃ σ : Sigma, θ' = fieldTwist hSigma σ θ} = {θ} ∧ θ ∈ D₂ ∧
              ∃ hσ : σ₀ ∈ twistStabilizer hSigma θ,
                (ν ⟨σ₀, hσ⟩ : ℂ) = ((q₀ : ℂ) - 1) / χ ⟨t₀, hσ⟩) ∧
          ((∃ l ∈ B0, chr l = fun h => ΘO θ χ ν (Ψ.symm h)) →
            twistStabilizer hSigma θ = ⊤ ∧
              ∀ hσ : σ₀ ∈ twistStabilizer hSigma θ, χ ⟨t₀, hσ⟩ ≠ 0)) ∧
      B0 = FH ∪ PL ∪ CH ∧ (ε = 1 → κm = 2) ∧ (ε = -1 → κm = 2 ^ n) ∧
      CuspidalSelectionPullbackData basisH ideal principalH (MonoidHom.id Hc) ℓ ΦH PH BH TN D₂
        res q κp κm ∧
      CuspidalSelectionPullbackData basisN ideal principalN π ℓ ΦH PH BH TN D₂ res q κp κm ∧
      ∀ (j : ℤ) (hj : ¬ ((2 ^ n : ℕ) : ℤ) ∣ j)
        (basisC : FiniteIrreducibleCharacterBasis (centralSylowPowerCentralizer n S e j))
        (principalC : basisC.index), (basisC.representation principalC).character = 1 →
        CentralSylowPowerQuotientData.{0, v} n hn S e j hj ideal basisN basisH basisC principalN
          principalH principalC ∧
        CuspidalSelectionPullbackData basisC ideal principalC (centralSylowPowerMap n hn S e j hj)
          ℓ ΦH PH BH TN D₂ res q κp κm :=
  conditional_actual_principal_cuspidal_selection_and_full_degree_counts_of_localHyp n hn S e p f
    hp hpodd hf
    (ConditionalLocalHyp.of_isSimpleGroup hnonab n hn S e hfour p f hp hpodd hf hmodel)
    ideal basisH principalH hprincipalH basisN principalN hprincipalN

end Assembly

end CFSG.Wreathed

module

public import CFSG.CharacterTheory.Wreathed.ConditionalCuspidalSelection
public import CFSG.CharacterTheory.Wreathed.ConditionalExplicitPrincipalOrderFamilies
public import CFSG.CharacterTheory.Wreathed.InvolutionInducedCharacters
public import CFSG.CharacterTheory.Wreathed.ConditionalExplicitPrincipalOrderBlocks
public import CFSG.CharacterTheory.Wreathed.ConditionalExplicitPrincipalOrderTori

public noncomputable section

open scoped Classical

namespace CFSG.Wreathed

open Matrix CFSG.TwoRankLowerBound.Helpers CFSG.Semidihedral.Principal
  CFSG.Wreathed.ActualProjectiveLayer CFSG.Wreathed.CyclicCentralSL2Extension
  CFSG.ComponentClassification.CatalogueSchreierLinearTwo CFSG.Wreathed.CentralSL2Abelianization
  CFSG.Wreathed.CentralSL2 CFSG.Wreathed.OddNormalQuotientInvolutions

section Auxiliary

theorem four_family_moment_eq {m q Φ ε UP UC : ℂ} (hq0 : q ≠ 0) (hqp : q + 1 ≠ 0)
    (hqm : q - 1 ≠ 0)
    (h : (ε = 1 ∧ UP = m * (m - 2) ∧ UC = 0) ∨ (ε = -1 ∧ UP = 0 ∧ UC = m * (m - 2))) :
    m + m * Φ / q + UP * (1 + Φ) / (q + 1) + UC * (Φ - 1) / (q - 1) =
      m / (q * (q + ε)) * (q * (q + ε * (m - 1)) + (q * (m - 1) + ε) * Φ) := by
  rcases h with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
  · field_simp
    ring
  · have hqm' : q + -1 ≠ 0 := by rw [← sub_eq_add_neg]; exact hqm
    field_simp
    ring

theorem sum_coefficientBlock_comp_eq {E E' : Type} [Group E] [Fintype E] [Group E']
    [Fintype E'] (basis : FiniteIrreducibleCharacterBasis E)
    (basis' : FiniteIrreducibleCharacterBasis E') (B : Finset basis.index)
    (B' : Finset basis'.index) (σ : E' →* E) (τ : B ≃ B')
    (hτ : ∀ θ, (basis'.representation (τ θ)).character =
      (basis.representation θ).character ∘ σ) (g : (E' → ℂ) → ℂ) :
    ∑ l ∈ B', g (basis'.representation l).character =
      ∑ l ∈ B, g ((basis.representation l).character ∘ σ) := by
  rw [← Finset.sum_coe_sort B', ← Finset.sum_coe_sort B,
    ← Equiv.sum_comp τ (fun l => g (basis'.representation l.1).character)]
  exact Finset.sum_congr rfl fun θ _ => by rw [hτ]

end Auxiliary

section Assembly

variable {G : Type} [Group G] [Fintype G] [IsSimpleGroup G]

omit [IsSimpleGroup G] in
theorem conditional_explicit_global_principal_order_identity_of_localHyp
    (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n))
    (p f : ℕ) (hp : p.Prime) (hpodd : p ≠ 2) (hf : 1 ≤ f)
    (hloc : ConditionalLocalHyp n hn S e p f)
    [Fintype (centralizerOddCoreQuotient n S e)] (ideal : Ideal ComplexAlgebraicIntegers)
    [ideal.IsMaximal] [CharP (ComplexAlgebraicIntegers ⧸ ideal) 2]
    (basisG : FiniteIrreducibleCharacterBasis G) (principalG : basisG.index)
    (hprincipalG : (basisG.representation principalG).character = 1)
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
      let m := 2 ^ n
      let q := Nat.card F
      let d := Nat.card Sigma
      let N := involutionCentralizer n S e
      let R := centralizerOddCore n S e
      let π := centralizerOddCoreMap n S e
      let x : G := wreathModelHom S e (Original.x m)
      let xN : N := ⟨x, Subgroup.mem_centralizer_singleton_iff.mpr rfl⟩
      let ι : CentralExtension F b m (wreathModulus_pos n) (wreathModulus_even hn) →*
          SemilinearExtension F b m (wreathModulus_pos n) (wreathModulus_even hn) Sigma hSigma :=
        SemidirectProduct.inl
      let u := cyclicGenerator F b m (wreathModulus_pos n) (wreathModulus_even hn)
      let xK := u ^ m
      let yK := (u ^ 2) ^ (m / 4) *
        specialInclusion F b m (wreathModulus_pos n) (wreathModulus_even hn) (weyl F)
      let ε : ℤ := if q % 4 = 1 then 1 else -1
      let ΦH : centralizerOddCoreQuotient n S e → ℂ := fun h =>
        (Nat.card {w : Omega F // ((ρ (centralizerFullQuotientMap n hn S e h) :
          coordinateE F) : Equiv.Perm (Omega F)) w = w} : ℂ) - 1
      let ΦN : N → ℂ := fun g => ΦH (π g)
      let B₀ := coefficientBlock basisG (localizedComplexIntegerRing ideal) principalG
      let B₀N := coefficientBlock basisN (localizedComplexIntegerRing ideal) principalN
      Ψ (ι xK) = π xN ∧ (∃ y : N, orderOf y = 2 ∧ π y = Ψ (ι yK)) ∧
      ∀ y : N, orderOf y = 2 → π y = Ψ (ι yK) →
        let D : ℤ := (kernelCentralizer R y).index * q * (q + ε)
        let c : ℕ := Nat.card N
        c = Nat.card R * m * d * q * (q ^ 2 - 1) ∧
        (Nat.card (ConjClasses.mk y).carrier : ℤ) = D ∧
        (∀ z : N, Odd (orderOf z) →
          ∑ ψ ∈ B₀N, ((basisN.representation ψ).character xN +
              D * (basisN.representation ψ).character y) ^ 2 *
            (basisN.representation ψ).character (xN * z) / (basisN.representation ψ).character 1 =
            (m : ℂ) * D ^ 2 / (q * (q + ε)) *
              (q * (q + ε * (m - 1)) + (q * (m - 1) + ε) * ΦN z)) ∧
        (∀ z : N, Odd (orderOf z) →
          (Nat.card G : ℂ) * ∑ χ ∈ B₀, (basisG.representation χ).character x ^ 2 *
            (basisG.representation χ).character (x * z) / (basisG.representation χ).character 1 =
            (c : ℂ) * m * D ^ 2 / (q * (q + ε)) *
              (q * (q + ε * (m - 1)) + (q * (m - 1) + ε) * ΦN z)) ∧
        (Nat.card G : ℂ) * ∑ χ ∈ B₀, (basisG.representation χ).character x ^ 3 /
          (basisG.representation χ).character 1 = (c : ℂ) * m ^ 2 * D ^ 2 := by
  refine ⟨hloc.modelData,
    ?_⟩
  intro F _ _ Sigma b hSigma ρ Ψ hdata m q d N R π x xN ι u xK yK ε ΦH ΦN B₀ B₀N
  have hb := hdata.nonsquare
  have hd := hdata.sigma_odd
  have hpo : Odd p := hp.odd_of_ne_two hpodd
  have hm4 : 4 ∣ m := ⟨2 ^ (n - 2), by
    simp only [m]
    rw [show (4 : ℕ) = 2 ^ 2 by norm_num, ← pow_add]
    congr 1
    omega⟩
  have hq3 : 3 ≤ Nat.card F := three_le_card hb
  have hSL := semilinear_involution_classes_and_augmentation_values hp hpo hf hdata.card b hb m
    (wreathModulus_pos n) (wreathModulus_even hn) hm4 Sigma hSigma hd
  obtain ⟨-, -, -, hιy₀ord, hinvH, -, -, -, -, hclassH, -, -, -, -, hchar⟩ := hSL
  have hx2 : orderOf x = 2 := by
    have ha : orderOf (wreathModelHom S e (Original.a (2 ^ n))) = 2 ^ n :=
      orderOf_wreathModelHom_a n S e
    obtain ⟨k, hk⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
    have hhalf : 2 ^ n / 2 = 2 ^ k := by
      rw [hk, pow_succ, Nat.mul_div_cancel _ (by norm_num)]
    have hdvd : 2 ^ k ∣ orderOf (wreathModelHom S e (Original.a (2 ^ n))) := by
      rw [ha, hk]
      exact pow_dvd_pow 2 k.le_succ
    change orderOf (wreathModelHom S e (Original.x (2 ^ n))) = 2
    rw [wreathModelHom_x_eq, hhalf, orderOf_pow_of_dvd (by positivity) hdvd, ha, hk, pow_succ,
      Nat.mul_div_cancel_left _ (by positivity)]
  have hx2N : orderOf xN = 2 := by rw [← Subgroup.orderOf_coe]; exact hx2
  have hxc : xN ∈ Subgroup.center N := Subgroup.mem_center_iff.mpr fun g => Subtype.ext
    (Subgroup.mem_centralizer_singleton_iff.mp g.2)
  have hR : Odd (Nat.card R) := centralizerOddCore_card_odd n S e
  have hxK : Ψ (ι xK) = π xN := by
    set t := Ψ.symm (π xN) with ht
    have ht2 : orderOf t = 2 := by
      rw [ht, MulEquiv.orderOf_eq]
      exact InvolutionInducedCharacters.orderOf_mk_eq_two R hR hx2N
    have htc : ∀ w, w * t = t * w := by
      intro w
      apply Ψ.injective
      rw [map_mul, map_mul, ht, MulEquiv.apply_symm_apply]
      obtain ⟨g, hg⟩ := centralizerOddCoreMap_surjective n S e (Ψ w)
      rw [← hg, ← map_mul, ← map_mul, (Subgroup.mem_center_iff.mp hxc g)]
    rcases (hinvH t).mp ht2 with h | h
    · rw [← h, ht, MulEquiv.apply_symm_apply]
    · exfalso
      obtain ⟨c, hcy⟩ := isConj_iff.mp h
      have hyt : ι yK = t := by
        have h1 : ι yK = c⁻¹ * (c * ι yK * c⁻¹) * c := by group
        rw [h1, hcy, mul_assoc, ← htc c, inv_mul_cancel_left]
      have hcen : ∀ w, IsConj (ι yK) w ↔ w = ι yK := by
        intro w
        constructor
        · intro hw
          obtain ⟨c', hc'⟩ := isConj_iff.mp hw
          rw [← hc', hyt, htc c', mul_inv_cancel_right]
        · rintro rfl
          exact IsConj.refl _
      have hcard1 : Nat.card {w // IsConj (ι yK) w} = 1 := by
        rw [Nat.card_eq_one_iff_unique]
        exact ⟨⟨fun a b => Subtype.ext (((hcen a.1).mp a.2).trans ((hcen b.1).mp b.2).symm)⟩,
          ⟨⟨ι yK, IsConj.refl _⟩⟩⟩
      have h1 := hclassH
      change (Nat.card {w // IsConj (ι yK) w} : ℤ) = _ at h1
      rw [hcard1] at h1
      have hε : (if Nat.card F % 4 = 1 then (1 : ℤ) else -1) = 1 ∨
          (if Nat.card F % 4 = 1 then (1 : ℤ) else -1) = -1 := by
        by_cases h' : Nat.card F % 4 = 1
        · exact Or.inl (ite_eq_left h')
        · exact Or.inr (ite_eq_right h')
      rcases hε with h' | h' <;> rw [h'] at h1 <;> push_cast at h1 <;> nlinarith
  open InvolutionInducedCharacters in
  have hII :=
    actual_centralizer_involution_induced_characters_and_principal_order_identity_of_one_class
    hloc.involutions_conj n hn S e R hR hp hpo hf hdata.card b hb Sigma hSigma hd Ψ hxK
  obtain ⟨hyex, hII⟩ := hII
  refine ⟨hxK, hyex, ?_⟩
  intro y hy2 hyΦ D c
  obtain ⟨⟨-, -, hc, -, hcls, hxyconj⟩, -, horder⟩ := hII y hy2 hyΦ
  obtain ⟨hzid, -, -, -, -⟩ := horder ideal basisG principalG hprincipalG basisN principalN
    hprincipalN
  obtain ⟨σ₀, hgen⟩ := @IsCyclic.exists_generator _ _ hdata.sigma_cyclic
  have hm0 : (2 ^ n : ℕ) ≠ 0 := (wreathModulus_pos n).ne'
  set ζm : ℂ := Complex.exp (2 * Real.pi * Complex.I / ((2 ^ n : ℕ) : ℂ)) with hζmdef
  have hζm : IsPrimitiveRoot ζm (2 ^ n) := Complex.isPrimitiveRoot_exp _ hm0
  have hd0 : Nat.card Sigma ≠ 0 := Nat.card_pos.ne'
  set ζd : ℂ := Complex.exp (2 * Real.pi * Complex.I / (Nat.card Sigma : ℂ)) with hζddef
  have hζd : IsPrimitiveRoot ζd (Nat.card Sigma) := Complex.isPrimitiveRoot_exp _ hd0
  obtain ⟨E, _, _, basis, y₁, hy₁⟩ := exists_cuspidal_data (F := F) hb
  obtain ⟨z₀, hz₀⟩ := exists_norm_eq F E basis b
  obtain ⟨ψ, hψ⟩ := exists_addChar_ne_one (F := F)
  have hprev := (conditional_actual_principal_series_membership_and_cuspidal_Gram_of_localHyp.{0} n
    hn S e p f hp hpodd hf hloc ideal basisH principalH hprincipalH basisN principalN
    hprincipalN).2 F Sigma b hSigma ρ Ψ hdata σ₀ hgen ζm hζm
  obtain ⟨-, -, -, hPH1, -, hκ1, hκ2, hDH, -, hTNcorr, -⟩ := hprev
  have hsel :=
    (conditional_actual_principal_cuspidal_selection_and_full_degree_counts_of_localHyp.{0} n hn S
      e p f hp hpodd hf hloc ideal basisH principalH hprincipalH basisN principalN
    hprincipalN).2 F Sigma b hSigma ρ Ψ hdata σ₀ hgen ζm hζm E basis z₀ y₁ hz₀ hy₁ ψ hψ
  obtain ⟨-, -, -, -, -, -, -, -, -, hC7, hbij, -, -, -, -, -, -, hB0H, -, hκm2, -, -, -⟩ := hsel
  have hprev2 :=
    conditional_actual_principal_linear_augmentation_twists_and_residual_torus_Gram_of_localHyp.{0}
      n hn S e p f hp hpodd hf hloc ideal basisH principalH hprincipalH basisN principalN
      hprincipalN |>.2 F Sigma b hSigma ρ Ψ hdata σ₀ hgen ζm ζd hζm hζd
  obtain ⟨-, -, -, -, hDataH, -, -, -⟩ := hprev2
  have hΦ : ∀ h, ΦH h = (Nat.card {w : Omega F // ((ρ (centralizerFullQuotientMap n hn S e h) :
      coordinateE F) : Equiv.Perm (Omega F)) w = w} : ℂ) - 1 := fun _ => rfl
  have hε : ε = 1 ∨ ε = -1 := by
    by_cases h : Nat.card F % 4 = 1
    · exact Or.inl (ite_eq_left h)
    · exact Or.inr (ite_eq_right h)
  have hεsq : (ε : ℂ) ^ 2 = 1 := by rcases hε with h | h <;> rw [h] <;> norm_num
  have hqodd : Nat.card F % 2 = 1 := by
    rw [hdata.card]
    exact Nat.odd_iff.mp hpo.pow
  have hsq : IsSquare (-1 : F) ↔ ε = 1 := by
    rw [FiniteField.isSquare_neg_one_iff, ← Nat.card_eq_fintype_card]
    constructor
    · intro h
      exact ite_eq_left (by omega)
    · intro h h3
      have : ε = -1 := ite_eq_right (by omega)
      rw [this] at h
      norm_num at h
  set ℓ : Fin (2 ^ n) → centralizerOddCoreQuotient n S e → ℂ := fun r h =>
    (CentralSL2Abelianization.rootCharacter (2 ^ n) (wreathModulus_pos n) ζm hζm r.val
      (CentralSL2Abelianization.psi F b (2 ^ n) (wreathModulus_pos n) (wreathModulus_even hn)
        Sigma hSigma (Ψ.symm h)).1 : ℂ) with hℓdef
  have hℓ : ∀ (r : Fin (2 ^ n)) (h : centralizerOddCoreQuotient n S e),
      (CentralSL2Abelianization.linearCharacter F b (2 ^ n) (wreathModulus_pos n)
        (wreathModulus_even hn) Sigma hSigma σ₀ hgen ζm ζd hζm hζd r 0 (Ψ.symm h) : ℂ) =
        ℓ r h := by
    intro r h
    simp only [hℓdef, CentralSL2Abelianization.linearCharacter,
      CentralSL2Abelianization.quotientLinearCharacter, MonoidHom.comp_apply,
      MonoidHom.mul_apply, MonoidHom.coe_fst, MonoidHom.coe_snd, Fin.val_zero]
    have h0 : ∀ x, CentralSL2Abelianization.rootCharacter (Nat.card Sigma) Nat.card_pos ζd hζd
        0 x = 1 := by
      intro x
      simp [CentralSL2Abelianization.rootCharacter, CentralSL2Abelianization.scalarResidueHom]
    rw [h0, mul_one]
  obtain ⟨-, -, -, hval, -⟩ := hchar σ₀ hgen ζm ζd hζm hζd
  set Y := Ψ (ι yK) with hY
  have hℓY : ∀ r, ℓ r Y = (-1) ^ r.val := by
    intro r
    rw [← hℓ, hY, MulEquiv.symm_apply_apply]
    exact (hval r 0).2.1
  have hΦY : ΦH Y = ε := by
    rw [hY, compatibleModel_augmentation hn hdata hΦ]
    have h := (hval ⟨0, wreathModulus_pos n⟩ ⟨0, Nat.card_pos⟩).2.2.2
    have h' := (hval ⟨0, wreathModulus_pos n⟩ ⟨0, Nat.card_pos⟩).2.1
    simp only [pow_zero, mul_one] at h h'
    rw [h', one_mul] at h
    exact h
  have hlab₁ : ∀ r : Fin (2 ^ n), ∃ l ∈ coefficientBlock basisH
      (localizedComplexIntegerRing ideal) principalH, (basisH.representation l).character = ℓ r :=
    fun r => by
      obtain ⟨l, hl, hlc⟩ := (hDataH.lam_principal r 0).mpr rfl
      exact ⟨l, hl, hlc.trans (funext fun h => hℓ r h)⟩
  have hlab₂ : ∀ r : Fin (2 ^ n), ∃ l ∈ coefficientBlock basisH
      (localizedComplexIntegerRing ideal) principalH,
      (basisH.representation l).character = fun h => ℓ r h * ΦH h := fun r => by
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
  have hFHeq : linearAugmentationLabels basisH (MonoidHom.id _) ℓ ΦH =
      Finset.univ.image lbl₁ ∪ Finset.univ.image lbl₂ := by
    ext l
    simp only [linearAugmentationLabels, Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_union, Finset.mem_image]
    constructor
    · rintro ⟨r, hr | hr⟩
      · exact Or.inl ⟨r, basisH.distinct ((hlbl₁ r).trans hr.symm)⟩
      · exact Or.inr ⟨r, basisH.distinct ((hlbl₂ r).trans hr.symm)⟩
    · rintro (⟨r, rfl⟩ | ⟨r, rfl⟩)
      · exact ⟨r, Or.inl (hlbl₁ r)⟩
      · exact ⟨r, Or.inr (hlbl₂ r)⟩
  have hℓodd : ∀ r (w : centralizerOddCoreQuotient n S e), Odd (orderOf w) → ℓ r w = 1 := by
    intro r w hw
    have h := (oddRestriction_eq_zsmul_add_iff _ _ _ _ _).mp (hDataH.lam_row r) w hw
    simp only [MonoidHom.id_apply, Pi.one_apply, Int.cast_one, Int.cast_zero, one_mul,
      zero_mul, add_zero] at h
    rw [← hℓ r w]
    exact h
  have hℓΦodd : ∀ r (w : centralizerOddCoreQuotient n S e), Odd (orderOf w) →
      ℓ r w * ΦH w = ΦH w := by
    intro r w hw
    have h := (oddRestriction_eq_zsmul_add_iff _ _ _ _ _).mp (hDataH.xi_row r) w hw
    simp only [MonoidHom.id_apply, Pi.one_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
      Int.cast_neg] at h
    rw [← hℓ r w]
    rw [h]
    linear_combination (ΦH w) * hεsq
  have hℓ1 : ∀ r, ℓ r 1 = 1 := by
    intro r
    rw [← hℓ r 1]
    simp
  have hΦ1 : ΦH 1 = q := hDataH.regular_basis.degree
  have hmomH : ∀ Z : centralizerOddCoreQuotient n S e, Odd (orderOf Z) →
      ∑ l ∈ coefficientBlock basisH (localizedComplexIntegerRing ideal) principalH,
        (basisH.representation l).character Y ^ 2 * (basisH.representation l).character Z /
          (basisH.representation l).character 1 =
        (2 ^ n : ℕ) + (2 ^ n : ℕ) * ΦH Z / q +
          (∑ l ∈ principalSeriesLabels basisH (MonoidHom.id _)
            {θ | ∃ x : (P : PrincipalSeriesParameter F b (2 ^ n)) ×
              (parameterStabilizer hSigma P →* ℂˣ), x.1.1.1 ≠ 1 ∧
              θ = (fun h => principalInduced (hm := wreathModulus_pos n)
                (heven := wreathModulus_even hn) hSigma x.1 x.2 (Ψ.symm h)) ∧
              ∃ l ∈ coefficientBlock basisH (localizedComplexIntegerRing ideal) principalH,
                (basisH.representation l).character = θ},
            (basisH.representation l).character Y ^ 2) * (1 + ΦH Z) / (q + 1) +
          (∑ l ∈ cuspidalLabels basisH ideal principalH (MonoidHom.id _) ℓ ΦH
            {θ | ∃ x : (P : PrincipalSeriesParameter F b (2 ^ n)) ×
              (parameterStabilizer hSigma P →* ℂˣ), x.1.1.1 ≠ 1 ∧
              θ = (fun h => principalInduced (hm := wreathModulus_pos n)
                (heven := wreathModulus_even hn) hSigma x.1 x.2 (Ψ.symm h)) ∧
              ∃ l ∈ coefficientBlock basisH (localizedComplexIntegerRing ideal) principalH,
                (basisH.representation l).character = θ},
            (basisH.representation l).character Y ^ 2) * (ΦH Z - 1) / (q - 1) := by
    intro Z hZ
    apply sum_moment_of_families basisH _ _ _ lbl₁ lbl₂ _ hlbl₁inj hlbl₂inj Y Z q hq3 (ΦH Z)
    · intro r
      rw [hlbl₁ r, hℓY, hℓodd r Z hZ, hℓ1]
      refine ⟨?_, rfl, rfl⟩
      rw [← pow_mul, mul_comm, pow_mul, neg_one_sq, one_pow]
    · intro r
      rw [hlbl₂ r]
      refine ⟨?_, hℓΦodd r Z hZ, ?_⟩
      · dsimp only
        rw [hℓY, hΦY, mul_pow, ← pow_mul, mul_comm r.val, pow_mul, neg_one_sq, one_pow, one_mul,
          hεsq]
      · dsimp only
        rw [hℓ1, hΦ1, one_mul]
    · intro l hl
      refine ⟨hDH.series_odd l hl Z hZ, ?_⟩
      simp only [principalSeriesLabels, Finset.mem_filter, Finset.mem_univ, true_and] at hl
      obtain ⟨θ, hθ, hlθ⟩ := hl
      rw [hlθ]
      exact hPH1 θ hθ
    · intro l hl
      obtain ⟨-, h1, -, hodd⟩ := hC7 l hl
      exact ⟨hodd Z hZ, h1⟩
    · refine hB0H.trans ?_
      rw [hFHeq]
  have : Fact p.Prime := ⟨hp⟩
  have : CharP F p :=
    CFSG.Semidihedral.FixedFieldData.characteristic_of_prime_power_card F hp hdata.card
  have h2 : (2 : F) ≠ 0 := two_ne_zero_of_not_isSquare hb
  have hfinPS : Finite (PrincipalSeriesParameter F b (2 ^ n)) :=
    Nat.finite_of_card_ne_zero (by
      rw [card_principalSeriesParameter F b (2 ^ n) (wreathModulus_pos n)]
      exact Nat.mul_ne_zero (by omega) hm0)
  have : Fintype (PrincipalSeriesParameter F b (2 ^ n)) := Fintype.ofFinite _
  have hfinNS : Finite (NonsplitParameter F E b (2 ^ n) h2 z₀ hz₀) :=
    Nat.finite_of_card_ne_zero (by
      rw [card_nonsplitParameter F b (2 ^ n) (wreathModulus_pos n) E basis h2 z₀ hz₀]
      exact Nat.mul_ne_zero (by omega) hm0)
  have : Fintype (NonsplitParameter F E b (2 ^ n) h2 z₀ hz₀) := Fintype.ofFinite _
  have hPHeq := principalSeriesSet_eq_image hn hp hpodd hdata hΦ ideal basisH principalH
    hprincipalH hDataH.regular_basis
  have hUP := sum_principalSeriesLabels_sq hb hd Ψ basisH
    (principalSeriesLabels basisH (MonoidHom.id _)
      {θ | ∃ x : (P : PrincipalSeriesParameter F b (2 ^ n)) ×
        (parameterStabilizer hSigma P →* ℂˣ), x.1.1.1 ≠ 1 ∧
        θ = (fun h => principalInduced (hm := wreathModulus_pos n)
          (heven := wreathModulus_even hn) hSigma x.1 x.2 (Ψ.symm h)) ∧
        ∃ l ∈ coefficientBlock basisH (localizedComplexIntegerRing ideal) principalH,
          (basisH.representation l).character = θ})
    (fun l => by
      simp only [principalSeriesLabels, Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · rintro ⟨θ, hθ, hlθ⟩
        rw [hlθ]
        exact hθ
      · intro h
        exact ⟨_, h, rfl⟩)
    (fun θ hθ => by
      obtain ⟨-, -, -, l, -, hl⟩ := hθ
      exact ⟨l, hl⟩)
    hPHeq yK
  have hUC := sum_cuspidalLabels_sq hpo hb h2 z₀ hz₀ y₁ hy₁ hψ Ψ basisH _ hbij yK
  have hyKdef : yK = involutionY F b (2 ^ n) (wreathModulus_pos n) (wreathModulus_even hn) := rfl
  have hUPv : (∑ l ∈ principalSeriesLabels basisH (MonoidHom.id _)
      {θ | ∃ x : (P : PrincipalSeriesParameter F b (2 ^ n)) ×
        (parameterStabilizer hSigma P →* ℂˣ), x.1.1.1 ≠ 1 ∧
        θ = (fun h => principalInduced (hm := wreathModulus_pos n)
          (heven := wreathModulus_even hn) hSigma x.1 x.2 (Ψ.symm h)) ∧
        ∃ l ∈ coefficientBlock basisH (localizedComplexIntegerRing ideal) principalH,
          (basisH.representation l).character = θ},
      (basisH.representation l).character Y ^ 2) =
      if ε = 1 then ((2 ^ n : ℕ) : ℂ) * (((2 ^ n : ℕ) : ℂ) - 2) else 0 := by
    rw [hY, hUP, hyKdef]
    by_cases h1 : ε = 1
    · rw [ite_eq_left h1, sum_principalSeries_involutionY_sq hb (hsq.mpr h1) rfl hm4,
        hκ1 h1]
      ring
    · rw [ite_eq_right h1, Finset.sum_eq_zero fun P _ => by
        rw [principalSeries_involutionY_eq_zero hb (fun h' => h1 (hsq.mp h')),
          zero_pow two_ne_zero],
        zero_div]
  have hUCv : (∑ l ∈ cuspidalLabels basisH ideal principalH (MonoidHom.id _) ℓ ΦH
      {θ | ∃ x : (P : PrincipalSeriesParameter F b (2 ^ n)) ×
        (parameterStabilizer hSigma P →* ℂˣ), x.1.1.1 ≠ 1 ∧
        θ = (fun h => principalInduced (hm := wreathModulus_pos n)
          (heven := wreathModulus_even hn) hSigma x.1 x.2 (Ψ.symm h)) ∧
        ∃ l ∈ coefficientBlock basisH (localizedComplexIntegerRing ideal) principalH,
          (basisH.representation l).character = θ},
      (basisH.representation l).character Y ^ 2) =
      if ε = 1 then 0 else ((2 ^ n : ℕ) : ℂ) * (((2 ^ n : ℕ) : ℂ) - 2) := by
    rw [hY, hUC, hyKdef]
    by_cases h1 : ε = 1
    · rw [ite_eq_left h1, Finset.sum_eq_zero fun P _ => by
        rw [cuspidalCharacter_involutionY_eq_zero hb (hsq.mpr h1), zero_pow two_ne_zero],
        zero_div]
    · have hε2 : ε = -1 := hε.resolve_left h1
      rw [ite_eq_right h1, sum_cuspidalCharacter_involutionY_sq hb (fun h' => h1 (hsq.mp h')) rfl
        hm4 h2 z₀ hz₀ y₁ hy₁ ψ, hκm2 hε2]
      ring
  have hq0 : (q : ℂ) ≠ 0 := by exact_mod_cast (show q ≠ 0 by omega)
  have hqp : (q : ℂ) + 1 ≠ 0 := by exact_mod_cast (show q + 1 ≠ 0 by omega)
  have hqm : (q : ℂ) - 1 ≠ 0 := by
    rw [sub_ne_zero, ← Nat.cast_one, Ne, Nat.cast_inj]
    omega
  have hQH : ∀ Z : centralizerOddCoreQuotient n S e, Odd (orderOf Z) →
      ∑ l ∈ coefficientBlock basisH (localizedComplexIntegerRing ideal) principalH,
        (basisH.representation l).character Y ^ 2 * (basisH.representation l).character Z /
          (basisH.representation l).character 1 =
        (m : ℂ) / (q * (q + ε)) * (q * (q + ε * (m - 1)) + (q * (m - 1) + ε) * ΦH Z) := by
    intro Z hZ
    rw [hmomH Z hZ, hUPv, hUCv]
    apply four_family_moment_eq hq0 hqp hqm
    rcases hε with h1 | h1
    · left
      refine ⟨by rw [h1]; norm_num, ?_, ?_⟩
      · rw [ite_eq_left h1]
      · rw [ite_eq_left h1]
    · right
      have hne : ε ≠ 1 := by rw [h1]; norm_num
      refine ⟨by rw [h1]; norm_num, ?_, ?_⟩
      · rw [ite_eq_right hne]
      · rw [ite_eq_right hne]
  obtain ⟨τ, hτchar, -, -, -, -⟩ := hTNcorr
  have hloc : ∀ z : N, Odd (orderOf z) →
      ∑ ψ ∈ B₀N, ((basisN.representation ψ).character xN +
          D * (basisN.representation ψ).character y) ^ 2 *
        (basisN.representation ψ).character (xN * z) / (basisN.representation ψ).character 1 =
        (m : ℂ) * D ^ 2 / (q * (q + ε)) * (q * (q + ε * (m - 1)) + (q * (m - 1) + ε) * ΦN z) := by
    intro z hz
    rw [sum_involution_moment_eq basisN ideal principalN hxc hx2N hy2 hxyconj (D : ℂ) hz]
    have htr := sum_coefficientBlock_comp_eq basisH basisN _ _ π τ hτchar
      (fun φ => φ y ^ 2 * φ z / φ 1)
    simp only [Function.comp_apply, map_one] at htr
    rw [htr, hyΦ]
    have hπz : Odd (orderOf (π z)) := hz.of_dvd_nat (orderOf_map_dvd π z)
    rw [hQH (π z) hπz]
    ring
  refine ⟨hc, hcls, hloc, fun z hz => ?_, ?_⟩
  · rw [hzid z hz]
    change (c : ℂ) * _ = _
    rw [hloc z hz]
    ring
  · have h1 := hzid 1 (by rw [orderOf_one]; exact odd_one)
    have hlhs : ∑ χ ∈ B₀, (basisG.representation χ).character x ^ 3 /
        (basisG.representation χ).character 1 =
        ∑ χ ∈ B₀, (basisG.representation χ).character x ^ 2 *
          (basisG.representation χ).character (x * ((1 : N) : G)) /
            (basisG.representation χ).character 1 :=
      Finset.sum_congr rfl fun χ _ => by rw [Subgroup.coe_one, mul_one]; ring
    rw [hlhs, h1]
    change (c : ℂ) * _ = _
    rw [hloc 1 (by rw [orderOf_one]; exact odd_one)]
    have hΦN1 : ΦN 1 = q := by
      change ΦH (π 1) = q
      rw [map_one, hΦ1]
    rw [hΦN1]
    have hqε : (q : ℂ) + ε ≠ 0 := by
      rcases hε with h | h <;> rw [h]
      · exact_mod_cast (show q + 1 ≠ 0 by omega)
      · push_cast
        rw [← sub_eq_add_neg]
        exact hqm
    field_simp
    ring

theorem conditional_explicit_global_principal_order_identity
    (hnonab : ∃ a b : G, a * b ≠ b * a)
    (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n))
    (hfour : ¬ Nonempty (centralizerFullQuotient n hn S e ≃* Equiv.Perm (Fin 4)))
    (p f : ℕ) (hp : p.Prime) (hpodd : p ≠ 2) (hf : 1 ≤ f)
    (hmodel : PSLTwoClassicalModel (centralizerSimpleLayer n hn S e) p f)
    [Fintype (centralizerOddCoreQuotient n S e)] (ideal : Ideal ComplexAlgebraicIntegers)
    [ideal.IsMaximal] [CharP (ComplexAlgebraicIntegers ⧸ ideal) 2]
    (basisG : FiniteIrreducibleCharacterBasis G) (principalG : basisG.index)
    (hprincipalG : (basisG.representation principalG).character = 1)
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
      let m := 2 ^ n
      let q := Nat.card F
      let d := Nat.card Sigma
      let N := involutionCentralizer n S e
      let R := centralizerOddCore n S e
      let π := centralizerOddCoreMap n S e
      let x : G := wreathModelHom S e (Original.x m)
      let xN : N := ⟨x, Subgroup.mem_centralizer_singleton_iff.mpr rfl⟩
      let ι : CentralExtension F b m (wreathModulus_pos n) (wreathModulus_even hn) →*
          SemilinearExtension F b m (wreathModulus_pos n) (wreathModulus_even hn) Sigma hSigma :=
        SemidirectProduct.inl
      let u := cyclicGenerator F b m (wreathModulus_pos n) (wreathModulus_even hn)
      let xK := u ^ m
      let yK := (u ^ 2) ^ (m / 4) *
        specialInclusion F b m (wreathModulus_pos n) (wreathModulus_even hn) (weyl F)
      let ε : ℤ := if q % 4 = 1 then 1 else -1
      let ΦH : centralizerOddCoreQuotient n S e → ℂ := fun h =>
        (Nat.card {w : Omega F // ((ρ (centralizerFullQuotientMap n hn S e h) :
          coordinateE F) : Equiv.Perm (Omega F)) w = w} : ℂ) - 1
      let ΦN : N → ℂ := fun g => ΦH (π g)
      let B₀ := coefficientBlock basisG (localizedComplexIntegerRing ideal) principalG
      let B₀N := coefficientBlock basisN (localizedComplexIntegerRing ideal) principalN
      Ψ (ι xK) = π xN ∧ (∃ y : N, orderOf y = 2 ∧ π y = Ψ (ι yK)) ∧
      ∀ y : N, orderOf y = 2 → π y = Ψ (ι yK) →
        let D : ℤ := (kernelCentralizer R y).index * q * (q + ε)
        let c : ℕ := Nat.card N
        c = Nat.card R * m * d * q * (q ^ 2 - 1) ∧
        (Nat.card (ConjClasses.mk y).carrier : ℤ) = D ∧
        (∀ z : N, Odd (orderOf z) →
          ∑ ψ ∈ B₀N, ((basisN.representation ψ).character xN +
              D * (basisN.representation ψ).character y) ^ 2 *
            (basisN.representation ψ).character (xN * z) / (basisN.representation ψ).character 1 =
            (m : ℂ) * D ^ 2 / (q * (q + ε)) *
              (q * (q + ε * (m - 1)) + (q * (m - 1) + ε) * ΦN z)) ∧
        (∀ z : N, Odd (orderOf z) →
          (Nat.card G : ℂ) * ∑ χ ∈ B₀, (basisG.representation χ).character x ^ 2 *
            (basisG.representation χ).character (x * z) / (basisG.representation χ).character 1 =
            (c : ℂ) * m * D ^ 2 / (q * (q + ε)) *
              (q * (q + ε * (m - 1)) + (q * (m - 1) + ε) * ΦN z)) ∧
        (Nat.card G : ℂ) * ∑ χ ∈ B₀, (basisG.representation χ).character x ^ 3 /
          (basisG.representation χ).character 1 = (c : ℂ) * m ^ 2 * D ^ 2 :=
  conditional_explicit_global_principal_order_identity_of_localHyp n hn S e p f hp hpodd hf
    (ConditionalLocalHyp.of_isSimpleGroup hnonab n hn S e hfour p f hp hpodd hf hmodel)
    ideal basisG principalG hprincipalG basisH principalH hprincipalH basisN principalN
    hprincipalN

end Assembly

end CFSG.Wreathed

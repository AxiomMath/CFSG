module

public import CFSG.CharacterTheory.Wreathed.ConditionalGeneralBaseAssembly
public import CFSG.CharacterTheory.Wreathed.ConditionalGeneralBaseRowOrthogonality
public import CFSG.CharacterTheory.Wreathed.ConditionalSquareRoot
public import CFSG.CharacterTheory.Wreathed.TwoPartArithmetic
public import CFSG.CharacterTheory.Wreathed.ConditionalGeneralBaseGenericColumns

public section

open scoped BigOperators Classical ComplexConjugate

namespace CFSG.Wreathed.ConditionalGeneralBase

open CFSG.TwoRankLowerBound.Helpers CFSG.Semidihedral.Principal
  CFSG.ComponentClassification.CatalogueSchreierLinearTwo
  CFSG.Semidihedral.SemilinearOddExtensions CFSG.Wreathed.ActualProjectiveLayer
  CFSG.Wreathed.CyclicCentralSL2Extension CFSG.Wreathed.ConditionalFourier
  CFSG.Wreathed.AdaptedBaseFusion

theorem dvd_eps_mul_sub_one {q n : ℕ} (hq3 : 3 ≤ q) (hqodd : q % 2 = 1)
    (hpart : 2 ^ (q ^ 2 - 1).factorization 2 = 2 * 2 ^ n) :
    ((2 ^ n : ℕ) : ℤ) ∣ (if q % 4 = 1 then (1 : ℤ) else -1) * q - 1 := by
  by_cases hq4 : q % 4 = 1
  · rw [ite_eq_left hq4, one_mul]
    have hfac := two_part_square_sub_one_split q n hq3 hq4 hpart
    have hd : 2 ^ n ∣ q - 1 := by
      rw [← hfac]
      exact Nat.ordProj_dvd _ _
    have h := Int.natCast_dvd_natCast.mpr hd
    rwa [Nat.cast_sub (by omega), Nat.cast_one] at h
  · rw [ite_eq_right hq4]
    have hq4' : q % 4 = 3 := by omega
    have hqm : q - 1 ≠ 0 := by omega
    have hqp : q + 1 ≠ 0 := by omega
    have hlow := two_factorization_eq_one_of_mod_four (q - 1) (by omega)
    have hfac : (q ^ 2 - 1).factorization 2 = (q + 1).factorization 2 + 1 := by
      rw [show q ^ 2 - 1 = (q + 1) * (q - 1) by simpa using Nat.sq_sub_sq q 1,
        Nat.factorization_mul hqp hqm]
      simp only [Finsupp.add_apply, hlow]
    have hexp : (q ^ 2 - 1).factorization 2 = n + 1 := by
      have h2 := hpart
      rw [show 2 * 2 ^ n = 2 ^ (n + 1) by ring] at h2
      exact Nat.pow_right_injective (le_refl 2) h2
    have hd : 2 ^ n ∣ q + 1 := by
      have : (q + 1).factorization 2 = n := by omega
      rw [← this]
      exact Nat.ordProj_dvd _ _
    have h := Int.natCast_dvd_natCast.mpr hd
    push_cast at h
    have h' : (((2 ^ n : ℕ) : ℤ)) ∣ -((q : ℤ) + 1) := by
      push_cast
      exact (dvd_neg).mpr h
    convert h' using 1
    ring

theorem general_base_core_of_localHyp
    {G : Type} [Group G] [Fintype G]
    (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G)
    (e : S ≃* Wreath (2 ^ n))
    (p f : ℕ) (hp : p.Prime) (hpodd : p ≠ 2) (hf : 1 ≤ f)
    (hloc : ConditionalLocalHyp n hn S e p f)
    [Fintype (centralizerOddCoreQuotient n S e)]
    (ideal : Ideal ComplexAlgebraicIntegers) [ideal.IsMaximal]
    [CharP (ComplexAlgebraicIntegers ⧸ ideal) 2]
    (basis : FiniteIrreducibleCharacterBasis G) (principal : basis.index)
    (hprincipal : (basis.representation principal).character = 1)
    (F : Type) [Field F] [Finite F] (Sigma : Subgroup (F ≃+* F)) (b : Fˣ)
    (hSigma : ∀ σ ∈ Sigma, σ (b : F) = b)
    (ρ : centralizerFullQuotient n hn S e →* coordinateE F)
    (Ψ : SemilinearExtension F b (2 ^ n) (wreathModulus_pos n) (wreathModulus_even hn) Sigma
      hSigma ≃* centralizerOddCoreQuotient n S e)
    (hdata : ConditionalCompatibleModelData n hn S e p f F Sigma b hSigma ρ Ψ)
    (U : Subgroup G) (hU : U = modelBase S e) :
      let m : ℕ := 2 ^ n
      let M : ℕ := m / 2
      let w : G := wreathModelHom S e (Original.z m)
      let a : G := wreathModelHom S e (Original.a m)
      let y : G := wreathModelHom S e (Original.s m * Original.z m)
      let ΦH : centralizerOddCoreQuotient n S e → ℂ := fun h =>
        (Nat.card {x : Omega F // ((ρ (centralizerFullQuotientMap n hn S e h) : coordinateE F) :
          Equiv.Perm (Omega F)) x = x} : ℂ) - 1
      let ΦN : G → ℂ := fun g => if hg : g ∈ involutionCentralizer n S e then
        ΦH (centralizerOddCoreMap n S e ⟨g, hg⟩) else 0
      let ε : ℤ := if Nat.card F % 4 = 1 then 1 else -1
      let q : ℕ := Nat.card F
      let q₀ : ℤ := (ε * q - 1) / m
      let B₀ := coefficientBlock basis (localizedComplexIntegerRing ideal) principal
      let K := dualGroup m
      (m : ℤ) ∣ ε * q - 1 ∧
      MulAction.orbit K ((0 : ZMod m), (0 : ZMod m)) = {(0, 0)} ∧
      (∀ r : ZMod m, r ≠ 0 → (MulAction.orbit K (r, r)).ncard = 3) ∧
      Set.InjOn (fun r : ZMod m => MulAction.orbit K (r, r)) {r | r ≠ 0} ∧
      (∀ I : ZMod m × ZMod m, MulAction.orbit K I = {(0, 0)} ∨
        (∃ r : ZMod m, r ≠ 0 ∧ MulAction.orbit K I = MulAction.orbit K (r, r)) ∨
        (MulAction.orbit K I).ncard = 6) ∧
      ((fun I : ZMod m × ZMod m => MulAction.orbit K I) ''
        {I | (MulAction.orbit K I).ncard = 3}).ncard = m - 1 ∧
      ((fun I : ZMod m × ZMod m => MulAction.orbit K I) ''
        {I | (MulAction.orbit K I).ncard = 6}).ncard = (m - 1) * (m - 2) / 6 ∧
      (∃ σ υ g : G, IsAdaptedBase U a w σ υ g) ∧
      ∀ ζ : ℂ, IsPrimitiveRoot ζ m → ∀ θ : ℂ, IsPrimitiveRoot θ (2 * m) → θ ^ 2 = ζ →
      let ν : basis.index → ℕ → ℕ := fun χ t' =>
        Module.finrank ℂ (Module.End.eigenspace ((basis.representation χ).representation y)
          (θ ^ t'))
      let Y : ℕ → basis.index → ℤ := fun r χ => (ν χ (2 * r) : ℤ) - ν χ (2 * r + m)
      (∃ v : basis.index → ℕ → Fin 2 → ℂ, IsCentralSectionRows basis ideal principal a m
        (fun k => centralSylowPowerCentralizer n S e k) ΦN ε v) ∧
      ∀ v : basis.index → ℕ → Fin 2 → ℂ, IsCentralSectionRows basis ideal principal a m
        (fun k => centralSylowPowerCentralizer n S e k) ΦN ε v →
      let X : ZMod m → basis.index → ℂ := fun j χ =>
        fourierTransform m ζ (fun k => v χ k 0) j.val
      let Fs : ZMod m → basis.index → ℂ := fun j χ =>
        fourierTransform m ζ (fun k => v χ k 1) j.val
      ∀ (σ υ : U) (g : G), IsAdaptedBase U a w σ υ g →
      (∃ lam : ZMod m → ZMod m → U →* ℂ,
        ∀ i j, lam i j σ = ζ ^ i.val ∧ lam i j υ = ζ ^ j.val) ∧
      ∀ lam : ZMod m → ZMod m → U →* ℂ,
        (∀ i j, lam i j σ = ζ ^ i.val ∧ lam i j υ = ζ ^ j.val) →
      let tm : ZMod m → ZMod m → basis.index → ℂ := fun i j χ =>
        (Nat.card U : ℂ)⁻¹ * ∑ u : U, (basis.representation χ).character u * conj (lam i j u)
      let c : ZMod m → ZMod m → basis.index → ℂ := fun i j χ =>
        tm 0 0 χ - tm i j χ + q₀ * (Fs i χ + Fs j χ + Fs (-i - j) χ)
      let Cl : ZMod m → basis.index → ℂ := fun l χ => ∑ i : ZMod m, c i (l - i) χ
      (∀ i j χ, ∃ k : ℕ, tm i j χ = k) ∧
      (∀ i j, ∀ χ ∈ B₀, ∃ z : ℤ, c i j χ = z) ∧
      (∀ χ, c 0 0 χ = 0) ∧
      (∀ i j χ, c i j χ = c j i χ ∧ c i j χ = c j (-i - j) χ) ∧
      (∀ i j, (i, j) ≠ (0, 0) → c i j principal = 1) ∧
      (∀ V : Finset (ZMod m × ZMod m), (∀ I ∈ V, (MulAction.orbit K I).ncard = 6) →
        (∀ I, (MulAction.orbit K I).ncard = 6 → ∃! J, J ∈ V ∧ J ∈ MulAction.orbit K I) →
        (∀ r : ZMod m, r ≠ 0 → ∑ χ ∈ B₀, c r r χ * conj (c r r χ) = 8) ∧
        (∀ I ∈ V, ∑ χ ∈ B₀, c I.1 I.2 χ * conj (c I.1 I.2 χ) = 7) ∧
        (∀ r r' : ZMod m, r ≠ 0 → r' ≠ 0 → r ≠ r' →
          ∑ χ ∈ B₀, c r r χ * conj (c r' r' χ) = 6) ∧
        (∀ r : ZMod m, r ≠ 0 → ∀ I ∈ V,
          ∑ χ ∈ B₀, c r r χ * conj (c I.1 I.2 χ) = 6 ∧
            ∑ χ ∈ B₀, c I.1 I.2 χ * conj (c r r χ) = 6) ∧
        ∀ I ∈ V, ∀ J ∈ V, I ≠ J → ∑ χ ∈ B₀, c I.1 I.2 χ * conj (c J.1 J.2 χ) = 6) ∧
      (∀ i j, ∀ j' ∈ Finset.Ico 1 m, ∑ χ ∈ B₀, c i j χ * conj (X j' χ) = 0) ∧
      (∀ i j, ∀ r < M, ∑ χ ∈ B₀, c i j χ * (Y r χ : ℂ) = 0) ∧
      (∀ i j, ∀ z : G, Odd (orderOf z) →
        ∑ χ ∈ B₀, c i j χ * conj ((basis.representation χ).character z) = 0) ∧
      (∀ i j, ∑ χ ∈ B₀, c i j χ * (basis.representation χ).character 1 = 0) ∧
      (∀ j : ZMod m, ∀ χ ∈ B₀, X j χ + 2 * Fs j χ = Cl 0 χ - Cl (-j) χ) ∧
      (∀ χ ∈ B₀, ∀ k ∈ Finset.Ico 1 m, v χ k 1 = (1 / 2) * ∑ j ∈ Finset.Ico 1 m,
        ζ ^ (-((j : ℤ) * k)) * (Cl 0 χ - Cl (-(j : ZMod m)) χ - X j χ)) ∧
      (∀ χ ∈ B₀, ∀ k ∈ Finset.Ico 1 m, ∀ z ∈ Subgroup.centralizer {a ^ k}, Odd (orderOf z) →
        2 * (basis.representation χ).character (a ^ k * z) =
          (1 - ε * ΦN z) * ∑ j ∈ Finset.Ico 1 m, ζ ^ (-((j : ℤ) * k)) * X j χ +
          (1 + ε * ΦN z) * ∑ j ∈ Finset.Ico 1 m,
            ζ ^ (-((j : ℤ) * k)) * (Cl 0 χ - Cl (-(j : ZMod m)) χ)) ∧
      (∀ j ∈ Finset.Ico 1 m, Odd j → ∀ χ ∈ B₀, ∃ k : ℤ, X j χ - c M M χ = 2 * k) ∧
      (∀ j ∈ Finset.Ico 1 m, Even j → ∀ r : ZMod m, 2 * r = -(j : ZMod m) → ∀ χ ∈ B₀,
        ∃ k : ℤ, X j χ - (c M M χ + c r r χ + c (r + M) (r + M) χ) = 2 * k) ∧
      (∀ χ ∈ B₀, ∃ k : ℤ, c M M χ - Y 0 χ = 2 * k) := by
  intro m M w a y ΦH ΦN ε q q₀ B₀ K
  subst hU
  have hm4 : 4 ≤ m := by
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  have hb := hdata.nonsquare
  have hq3 : 3 ≤ Nat.card F := CFSG.Wreathed.CentralSL2.three_le_card hb
  have hpart : 2 ^ (Nat.card F ^ 2 - 1).factorization 2 = 2 * 2 ^ n := by
    rw [hdata.card]
    exact hloc.qTwoPart
  have hqodd : Nat.card F % 2 = 1 := by
    rw [hdata.card]
    exact Nat.odd_iff.mp ((hp.odd_of_ne_two hpodd).pow)
  have hdvd : (m : ℤ) ∣ ε * q - 1 := dvd_eps_mul_sub_one hq3 hqodd hpart
  have hq₀ : (m : ℤ) * q₀ = ε * q - 1 := Int.mul_ediv_cancel' hdvd
  refine ⟨hdvd, orbit_zero, fun r hr => ncard_orbit_diag r hr, orbit_diag_injOn,
    orbit_trichotomy, ncard_orbits_three, ncard_orbits_six,
    hloc.adaptedBase, ?_⟩
  intro ζ hζ θ hθ hθζ ν Y
  have hm0 : (m : ℂ) ≠ 0 := by exact_mod_cast (show m ≠ 0 by omega)
  have ha : orderOf a = m := orderOf_wreathModelHom_a n S e
  obtain ⟨v₀, -, hv₀row, hv₀uniq, hv₀gram, hv₀deg, hv₀int, -, -, hv₀prin, hv₀inv, -, -⟩ :=
    (conditional_global_central_section_integral_fourier_columns_of_localHyp n hn S e p f hp hpodd
      hf hloc ideal basis principal hprincipal).2 F Sigma b hSigma ρ Ψ hdata ζ hζ
  open ConditionalSquareRoot in
  have hSq :=
    (conditional_square_root_cyclic_section_fourier_columns_and_parity_of_localHyp n hn S e p f
      hp hpodd hf hloc ideal basis principal hprincipal).2 F Sigma b hSigma ρ Ψ hdata
  obtain ⟨hyord, -, -, -, -, -, -, hSqζ⟩ := hSq
  obtain ⟨-, hYinv, -, -, -, -, -, -, -, hYrows⟩ := hSqζ ζ hζ θ hθ hθζ
  refine ⟨⟨v₀, hv₀row⟩, ?_⟩
  intro v hv X Fs
  have hveq : ∀ χ ∈ B₀, ∀ k ∈ Finset.Ico 1 m, v χ k = v₀ χ k := fun χ hχ k hk =>
    hv₀uniq χ hχ k hk (v χ k) (fun r hr hodd => hv χ hχ k hk r hr hodd)
  have hfeq : ∀ χ ∈ B₀, ∀ (ℓ : Fin 2) (j : ℕ), fourierTransform m ζ (fun k => v χ k ℓ) j =
      fourierTransform m ζ (fun k => v₀ χ k ℓ) j := fun χ hχ ℓ j =>
    fourierTransform_congr (fun k hk => by rw [hveq χ hχ k hk]) j
  have hvgram : ∀ k ∈ Finset.Ico 1 m, ∀ h ∈ Finset.Ico 1 m, ∀ ℓ t,
      ∑ χ ∈ B₀, conj (v χ k ℓ) * v χ h t =
        if k = h then (((m : ℤ) • !![4, -2; -2, ((m / 2 + 1 : ℕ) : ℤ)]) ℓ t : ℂ) else 0 := by
    intro k hk h hh ℓ t
    rw [← hv₀gram k hk h hh ℓ t]
    refine Finset.sum_congr rfl fun χ hχ => ?_
    rw [hveq χ hχ k hk, hveq χ hχ h hh]
  have hFint : ∀ χ ∈ B₀, ∀ (ℓ : Fin 2) (j : ZMod m),
      ∃ z : ℤ, fourierTransform m ζ (fun k => v χ k ℓ) j.val = z := by
    intro χ hχ ℓ j
    rcases Nat.eq_zero_or_pos j.val with h0 | hpos
    · refine ⟨0, ?_⟩
      rw [h0]
      simp [fourierTransform]
    · rw [hfeq χ hχ]
      exact hv₀int χ hχ j.val (Finset.mem_Ico.mpr ⟨hpos, ZMod.val_lt j⟩) ℓ
  have hprin1 : ∀ j : ZMod m, fourierTransform m ζ (fun k => v principal k 1) j.val = 0 := by
    intro j
    have hP : principal ∈ B₀ := coefficientBlock_self_mem basis _ principal
    rcases Nat.eq_zero_or_pos j.val with h0 | hpos
    · rw [h0]
      simp [fourierTransform]
    · rw [hfeq principal hP]
      exact (hv₀prin j.val (Finset.mem_Ico.mpr ⟨hpos, ZMod.val_lt j⟩)).2
  have hvinv : ∀ χ ∈ B₀, ∀ k ∈ Finset.Ico 1 m, ∀ ℓ, v χ k ℓ = ∑ j ∈ Finset.Ico 1 m,
      ζ ^ (-((j : ℤ) * k)) * fourierTransform m ζ (fun k => v χ k ℓ) j := by
    intro χ hχ k hk ℓ
    rw [hveq χ hχ k hk, hv₀inv χ hχ k hk ℓ]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [hfeq χ hχ]
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
          (Nat.card F) ((m : ℤ) • !![4, -2; -2, ((m / 2 + 1 : ℕ) : ℤ)]) := by
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
  have hΦ1 : ΦN 1 = (q : ℂ) := by
    obtain ⟨lb₁⟩ := finiteIrreducibleCharacterBasis_exists
      (G := centralSylowPowerCentralizer n S e (1 : ℕ))
    obtain ⟨l₁, hl₁⟩ := finiteIrreducibleCharacterBasis_contains_irreducible lb₁
      (principalFiniteComplexRepresentation _)
      (principalFiniteComplexRepresentation_isIrreducible _)
    rw [principalFiniteComplexRepresentation_character] at hl₁
    exact (hdataK 1 (Finset.mem_Ico.mpr ⟨le_rfl, by omega⟩) lb₁ l₁ hl₁).degree
  intro σ υ g hA
  have hc : Commute σ υ := commute_left_right hA
  have hgen : Subgroup.closure ({σ, υ} : Set (modelBase S e)) = ⊤ := hA.closure_eq_top
  have hσ : orderOf σ = m := orderOf_left' hA
  have hυ : orderOf υ = m := orderOf_right' hA
  have hint : Subgroup.zpowers σ ⊓ Subgroup.zpowers υ = ⊥ := zpowers_left_inf_right' hA
  have hσυ : ((σ * υ : modelBase S e) : G) = a := hA.mul_eq
  have : NeZero m := ⟨by omega⟩
  refine ⟨exists_linearCharacters hc hgen hσ hυ hint hζ, ?_⟩
  intro lam hlam tm c Cl
  have hcardU : (Fintype.card (modelBase S e) : ℂ) = (m : ℂ) ^ 2 := by
    rw [card_eq_sq hc hgen hσ hυ hint hζ lam hlam]
    push_cast
    ring
  set χres : basis.index → modelBase S e → ℂ := fun χ u => (basis.representation χ).character u
    with hχres
  have hcbase : ∀ i j χ, c i j χ = baseColumn lam (χres χ) ζ (v χ) (q₀ : ℂ) i j := by
    intro i j χ
    simp only [c, tm, Fs, baseColumn, baseMultiplicity, zmodFourier, hχres,
      Nat.card_eq_fintype_card]
  have hClbase : ∀ l χ, Cl l χ = baseColumnSum lam (χres χ) ζ (v χ) (q₀ : ℂ) l := by
    intro l χ
    simp only [Cl, baseColumnSum, hcbase]
  have hpowcoe : ∀ k : ℕ, (((σ * υ) ^ k : modelBase S e) : G) = a ^ k := by
    intro k
    rw [Subgroup.coe_pow, hσυ]
  have hval : ∀ χ ∈ B₀, ∀ k ∈ Finset.Ico 1 m,
      χres χ ((σ * υ) ^ k) = v χ k 0 + (2 + m * (q₀ : ℂ)) * v χ k 1 := by
    intro χ hχ k hk
    have h := hv χ hχ k hk 1 (Subgroup.one_mem _) (by rw [orderOf_one]; exact odd_one)
    rw [mul_one, hΦ1] at h
    simp only [hχres, hpowcoe, h]
    have hq₀' : (m : ℂ) * q₀ = ε * q - 1 := by exact_mod_cast hq₀
    rw [show (2 : ℂ) + m * q₀ = 1 + ε * q by rw [hq₀']; ring]
    ring
  set h6 := sixAut hA with hh6
  have h6σ : ∀ k, h6 k σ = ![σ, υ, υ, (σ * υ)⁻¹, σ, (σ * υ)⁻¹] k := sixAut_left hA
  have h6υ : ∀ k, h6 k υ = ![υ, σ, (σ * υ)⁻¹, σ, (σ * υ)⁻¹, υ] k := sixAut_right hA
  have hcharconj : ∀ (χ : basis.index) {x y : G}, IsConj x y →
      (basis.representation χ).character x = (basis.representation χ).character y := by
    intro χ x y hxy
    obtain ⟨c', rfl⟩ := isConj_iff.mp hxy
    exact (Representation.char_conj _ x c').symm
  have hχconj : ∀ χ k u, χres χ (h6 k u) = χres χ u := fun χ k u =>
    (hcharconj χ ((isConj_iff_exists_sixAut hA hn u _).mpr ⟨k, rfl⟩)).symm
  set P := Finset.univ.filter (fun x : modelBase S e => x ∉ hA.exc) with hP
  have hsplit : ∀ F' : modelBase S e → ℂ, ∑ x, F' x = F' 1 + ∑ k ∈ Finset.Ico 1 m,
      (F' ((σ * υ) ^ k) + F' (σ ^ k)⁻¹ + F' (υ ^ k)⁻¹) + ∑ x ∈ P, F' x := sum_split_exc hA
  have hPmem : ∀ u ∈ P, ∀ k, h6 k u ∈ P := by
    intro u hu k
    rw [hP, Finset.mem_filter] at hu ⊢
    refine ⟨Finset.mem_univ _, fun hmem => hu.2 ?_⟩
    have h1 := mem_exc_of_mem_closure hA (Subgroup.inv_mem _ (sixAut_mem hA k)) hmem
    rwa [MulAut.inv_apply_self] at h1
  have hPinj : ∀ u ∈ P, Function.Injective (fun k => h6 k u) := by
    intro u hu
    rw [hP, Finset.mem_filter] at hu
    exact sixAut_apply_injective hA hn hu.2
  have htriple : ∀ χ, ∀ k ∈ Finset.Ico 1 m, χres χ (σ ^ k)⁻¹ = χres χ ((σ * υ) ^ k) ∧
      χres χ (υ ^ k)⁻¹ = χres χ ((σ * υ) ^ k) := by
    intro χ k _
    have h1 := isConj_mul_zpow_left hA (k : ℤ)
    have h2 := isConj_mul_zpow_right hA (k : ℤ)
    rw [zpow_neg, zpow_natCast, zpow_natCast] at h1 h2
    exact ⟨(hcharconj χ h1).symm, (hcharconj χ h2).symm⟩
  have hnorm : ∀ i j, ∀ χ ∈ B₀, (m : ℂ) ^ 2 * c i j χ =
      ∑ k ∈ Finset.Ico 1 m, ((1 - conj (lam i j ((σ * υ) ^ k))) +
        (1 - conj (lam i j (σ ^ k)⁻¹)) + (1 - conj (lam i j (υ ^ k)⁻¹))) *
          (v χ k 0 + 2 * v χ k 1) +
      ∑ x ∈ P, (1 - conj (lam i j x)) * χres χ x := by
    intro i j χ hχ
    rw [hcbase, ← hcardU]
    exact card_mul_column_eq hc hgen hσ hυ hint hζ lam hlam P hsplit (χres χ) (v χ) q₀
      (htriple χ) (hval χ hχ) i j
  have hm2 : 2 ∣ m := ⟨2 ^ (n - 1), by
    simp only [m]
    rw [← pow_succ']
    congr 1
    omega⟩
  have hZZ : ∀ k ∈ Finset.Ico 1 m, ∀ l ∈ Finset.Ico 1 m,
      ∑ χ ∈ B₀, (v χ k 0 + 2 * v χ k 1) * conj (v χ l 0 + 2 * v χ l 1) =
        if k = l then 2 * (m : ℂ) ^ 2 else 0 := fun k hk l hl =>
    (central_combination_gram B₀ hm2 v hvgram hk hl).1
  have hZX : ∀ k ∈ Finset.Ico 1 m, ∀ l ∈ Finset.Ico 1 m,
      ∑ χ ∈ B₀, (v χ k 0 + 2 * v χ k 1) * conj (v χ l 0) = 0 := fun k hk l hl =>
    (central_combination_gram B₀ hm2 v hvgram hk hl).2
  have hPne : ∀ u ∈ P, u ∉ hA.exc := fun u hu => (Finset.mem_filter.mp hu).2
  have hWv : ∀ u ∈ P, ∀ k ∈ Finset.Ico 1 m, ∀ ℓ : Fin 2,
      ∑ χ ∈ B₀, χres χ u * conj (v χ k ℓ) = 0 := by
    intro u hu k hk ℓ
    exact rows_orthogonal_of_section basis ideal principal a m
      (fun k => centralSylowPowerCentralizer n S e k) ΦN hΦreal ε (Nat.card F) _ hdataK v hv
      (fun χ => χres χ u) hk (fun r hr hrodd => generic_column_central_section hA hn basis
        ideal principal hprincipal (hPne u hu) k (by rw [← hCk]; exact hr) hrodd) ℓ
  have hZW : ∀ k ∈ Finset.Ico 1 m, ∀ u ∈ P,
      ∑ χ ∈ B₀, (v χ k 0 + 2 * v χ k 1) * conj (χres χ u) = 0 := by
    intro k hk u hu
    have h0 := hWv u hu k hk 0
    have h1 := hWv u hu k hk 1
    have h : conj (∑ χ ∈ B₀, χres χ u * conj (v χ k 0 + 2 * v χ k 1)) = 0 := by
      rw [show ∑ χ ∈ B₀, χres χ u * conj (v χ k 0 + 2 * v χ k 1) =
          ∑ χ ∈ B₀, χres χ u * conj (v χ k 0) + 2 * ∑ χ ∈ B₀, χres χ u * conj (v χ k 1) by
        rw [Finset.mul_sum, ← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun χ _ => ?_
        rw [map_add, map_mul, map_ofNat]
        ring, h0, h1]
      simp
    rw [map_sum] at h
    rw [← h]
    refine Finset.sum_congr rfl fun χ _ => ?_
    rw [map_mul, Complex.conj_conj, mul_comm]
  have hWW : ∀ u ∈ P, ∀ u' ∈ P, ∑ χ ∈ B₀, χres χ u * conj (χres χ u') =
      if ∃ k, h6 k u = u' then (m : ℂ) ^ 2 else 0 := by
    intro u hu u' _
    rw [generic_column_generic hA hn basis ideal principal hprincipal (hPne u hu) u']
    by_cases hcj : IsConj (u : G) (u' : G)
    · rw [ite_eq_left hcj, ite_eq_left ((isConj_iff_exists_sixAut hA hn u u').mp hcj)]
    · rw [ite_eq_right hcj, ite_eq_right (mt (isConj_iff_exists_sixAut hA hn u u').mpr hcj)]
  have hgram := gram_of_normalized_columns hc hgen hσ hυ hint hζ lam hlam h6 h6σ h6υ P hsplit
    hPmem hPinj B₀ (fun χ k => v χ k 0 + 2 * v χ k 1) χres hZZ hZW
    (fun u hu u' hu' => by convert hWW u hu u' hu' using 2) c hnorm
  have hfourier_orth : ∀ (T' : basis.index → ℂ),
      (∀ h ∈ Finset.Ico 1 m, ∑ χ ∈ B₀, T' χ * conj (v χ h 0) = 0) → ∀ j : ZMod m,
      ∑ χ ∈ B₀, T' χ * conj (X j χ) = 0 := by
    intro T' hT' j
    simp only [X, fourierTransform, map_mul, map_inv₀, map_natCast, map_sum]
    have h : ∀ χ, T' χ * ((m : ℂ)⁻¹ * ∑ k ∈ Finset.Ico 1 m,
        conj (ζ ^ (j.val * k) - 1) * conj (v χ k 0)) =
        (m : ℂ)⁻¹ * ∑ k ∈ Finset.Ico 1 m, conj (ζ ^ (j.val * k) - 1) *
          (T' χ * conj (v χ k 0)) := by
      intro χ
      rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      ring
    rw [Finset.sum_congr rfl fun χ _ => h χ, ← Finset.mul_sum, Finset.sum_comm]
    rw [Finset.sum_eq_zero fun k hk => by rw [← Finset.mul_sum, hT' k hk, mul_zero], mul_zero]
  have hoddZ : ∀ k ∈ Finset.Ico 1 m, ∀ z : G, Odd (orderOf z) →
      ∑ χ ∈ B₀, (v χ k 0 + 2 * v χ k 1) * conj ((basis.representation χ).character z) = 0 := by
    intro k hk z hz
    have hz0 := odd_column_rows_orthogonal basis ideal principal a m ha ⟨n, rfl⟩
      (fun k => centralSylowPowerCentralizer n S e k) hCk ΦN hΦreal ε (Nat.card F) _ hdataK v hv
      hz hk 0
    have hz1 := odd_column_rows_orthogonal basis ideal principal a m ha ⟨n, rfl⟩
      (fun k => centralSylowPowerCentralizer n S e k) hCk ΦN hΦreal ε (Nat.card F) _ hdataK v hv
      hz hk 1
    have h : conj (∑ χ ∈ B₀, (basis.representation χ).character z *
        conj (v χ k 0 + 2 * v χ k 1)) = 0 := by
      rw [show ∑ χ ∈ B₀, (basis.representation χ).character z * conj (v χ k 0 + 2 * v χ k 1) =
          ∑ χ ∈ B₀, (basis.representation χ).character z * conj (v χ k 0) +
            2 * ∑ χ ∈ B₀, (basis.representation χ).character z * conj (v χ k 1) by
        rw [Finset.mul_sum, ← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun χ _ => ?_
        rw [map_add, map_mul, map_ofNat]
        ring, hz0, hz1]
      simp
    rw [map_sum] at h
    rw [← h]
    refine Finset.sum_congr rfl fun χ _ => ?_
    rw [map_mul, Complex.conj_conj, mul_comm]
  obtain ⟨Fc, hFc, hFcY, hFcpar, -⟩ := hYrows v hv
  have hYZ : ∀ k ∈ Finset.Ico 1 m, ∀ r < M,
      ∑ χ ∈ B₀, (v χ k 0 + 2 * v χ k 1) * conj ((Y r χ : ℤ) : ℂ) = 0 := by
    intro k hk r hr
    have hexp : ∀ χ ∈ B₀, (v χ k 0 + 2 * v χ k 1) * conj ((Y r χ : ℤ) : ℂ) =
        ∑ j ∈ Finset.Ico 1 m, ζ ^ (-((j : ℤ) * k)) *
          (((Y r χ * Fc χ j 0 : ℤ) : ℂ) + 2 * ((Y r χ * Fc χ j 1 : ℤ) : ℂ)) := by
      intro χ hχ
      rw [map_intCast, hvinv χ hχ k hk 0, hvinv χ hχ k hk 1, Finset.mul_sum,
        ← Finset.sum_add_distrib, Finset.sum_mul]
      refine Finset.sum_congr rfl fun j hj => ?_
      rw [← hFc χ hχ j hj 0, ← hFc χ hχ j hj 1]
      push_cast
      ring
    rw [Finset.sum_congr rfl hexp, Finset.sum_comm]
    refine Finset.sum_eq_zero fun j hj => ?_
    rw [← Finset.mul_sum, Finset.sum_add_distrib, ← Finset.mul_sum]
    have h0 : ∑ χ ∈ B₀, Y r χ * Fc χ j 0 = 0 := hFcY r hr j hj 0
    have h1 : ∑ χ ∈ B₀, Y r χ * Fc χ j 1 = 0 := hFcY r hr j hj 1
    have hc0 : ∑ χ ∈ B₀, ((Y r χ * Fc χ j 0 : ℤ) : ℂ) = 0 := by
      rw [← Int.cast_sum, h0, Int.cast_zero]
    have hc1 : ∑ χ ∈ B₀, ((Y r χ * Fc χ j 1 : ℤ) : ℂ) = 0 := by
      rw [← Int.cast_sum, h1, Int.cast_zero]
    rw [hc0, hc1, mul_zero, add_zero, mul_zero]
  have hnat : ∀ i j χ, ∃ k : ℕ, tm i j χ = k := fun i j χ =>
    restriction_linear_pairing_nat basis (modelBase S e) (lam i j) χ
  have hcint : ∀ i j, ∀ χ ∈ B₀, ∃ z : ℤ, c i j χ = z := by
    intro i j χ hχ
    obtain ⟨k0, hk0⟩ := hnat 0 0 χ
    obtain ⟨k1, hk1⟩ := hnat i j χ
    obtain ⟨f1, hf1⟩ := hFint χ hχ 1 i
    obtain ⟨f2, hf2⟩ := hFint χ hχ 1 j
    obtain ⟨f3, hf3⟩ := hFint χ hχ 1 (-i - j)
    refine ⟨k0 - k1 + q₀ * (f1 + f2 + f3), ?_⟩
    simp only [c, Fs, hk0, hk1, hf1, hf2, hf3]
    push_cast
    ring
  have hcsym : ∀ i j χ, c i j χ = c j i χ ∧ c i j χ = c j (-i - j) χ := by
    intro i j χ
    rw [hcbase, hcbase, hcbase]
    exact baseColumn_symm hc hgen hζ lam hlam h6 h6σ h6υ (χres χ) (hχconj χ) (v χ) q₀ i j
  have hhalf : ∀ x : ZMod m, x ≠ 0 → (x, x) ≠ ((0 : ZMod m), (0 : ZMod m)) := fun x hx h =>
    hx (Prod.ext_iff.mp h).1
  have hne6 : ∀ I : ZMod m × ZMod m, (MulAction.orbit K I).ncard = 6 → I ≠ 0 := by
    intro I hI h0
    rw [h0, show (0 : ZMod m × ZMod m) = ((0 : ZMod m), (0 : ZMod m)) from rfl, orbit_zero,
      Set.ncard_singleton] at hI
    omega
  refine ⟨hnat, hcint, fun χ => by rw [hcbase]; exact baseColumn_zero lam (χres χ) (v χ) q₀,
    hcsym, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  ·
    intro i j hij
    rw [hcbase]
    have h1 : χres principal = fun _ => 1 := by
      funext u
      simp only [hχres, hprincipal, Pi.one_apply]
    rw [h1]
    exact baseColumn_principal hc hgen hζ lam hlam (v principal) q₀ hprin1 hij
  ·
    intro V hV6 hVuniq
    have hrr : ∀ r : ZMod m, r ≠ 0 → (r, r) ≠ 0 := fun r hr => hhalf r hr
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · intro r hr
      have h := hgram (r, r) (r, r) (hrr r hr) (hrr r hr)
      rw [card_dualSixFun_diag (three_mul_ne_zero hr)] at h
      rw [h]
      norm_num
    · intro I hI
      have h := hgram I I (hne6 I (hV6 I hI)) (hne6 I (hV6 I hI))
      rw [card_dualSixFun_self ((ncard_orbit_eq_six_iff I).mp (hV6 I hI))] at h
      rw [h]
      norm_num
    · intro r r' hr hr' hrr'
      have hnot : (r, r) ∉ MulAction.orbit (dualGroup m) (r', r') := by
        intro hmem
        have horb := MulAction.orbit_eq_iff.mpr hmem
        exact hrr' (orbit_diag_injOn hr hr' horb)
      have h := hgram (r, r) (r', r') (hrr r hr) (hrr r' hr')
      rw [card_dualSixFun_eq_zero hnot] at h
      rw [h]
      norm_num
    · intro r hr I hI
      have h3 : (MulAction.orbit (dualGroup m) (r, r)).ncard = 3 := ncard_orbit_diag r hr
      have hnot1 : (r, r) ∉ MulAction.orbit (dualGroup m) I := by
        intro hmem
        have horb := MulAction.orbit_eq_iff.mpr hmem
        have := hV6 I hI
        rw [← horb, h3] at this
        omega
      have hnot2 : I ∉ MulAction.orbit (dualGroup m) (r, r) := by
        intro hmem
        have horb := MulAction.orbit_eq_iff.mpr hmem
        have := hV6 I hI
        rw [horb, h3] at this
        omega
      have h1 := hgram (r, r) I (hrr r hr) (hne6 I (hV6 I hI))
      have h2 := hgram I (r, r) (hne6 I (hV6 I hI)) (hrr r hr)
      rw [card_dualSixFun_eq_zero hnot1] at h1
      rw [card_dualSixFun_eq_zero hnot2] at h2
      refine ⟨?_, ?_⟩
      · rw [h1]
        norm_num
      · rw [h2]
        norm_num
    · intro I hI J hJ hIJ
      have hnot : I ∉ MulAction.orbit (dualGroup m) J := by
        intro hmem
        obtain ⟨K', -, huniq⟩ := hVuniq J (hV6 J hJ)
        have e1 := huniq I ⟨hI, hmem⟩
        have e2 := huniq J ⟨hJ, MulAction.mem_orbit_self J⟩
        exact hIJ (e1.trans e2.symm)
      have h := hgram I J (hne6 I (hV6 I hI)) (hne6 J (hV6 J hJ))
      rw [card_dualSixFun_eq_zero hnot] at h
      rw [h]
      norm_num
  ·
    intro i j j' _
    exact column_orthogonal B₀ P (fun χ k => v χ k 0 + 2 * v χ k 1) χres (c i j) _ _
      (hnorm i j) (X j') (fun k hk => hfourier_orth _ (hZX k hk) j')
      (fun x hx => hfourier_orth _ (fun h hh => hWv x hx h hh 0) j')
  ·
    intro i j r hr
    have h := column_orthogonal B₀ P (fun χ k => v χ k 0 + 2 * v χ k 1) χres (c i j) _ _
      (hnorm i j) (fun χ => ((Y r χ : ℤ) : ℂ)) (fun k hk => hYZ k hk r hr) (fun x hx => by
        have hW := column_orthogonal_signed_even basis B₀ (fun χ => χres χ x) y ζ M
          (fun χ r => Y r χ) (fun h' hh' => generic_column_odd_power hA hn basis ideal principal
            hprincipal (hPne x hx) hyord hh') hYinv hr
        rw [← hW]
        refine Finset.sum_congr rfl fun χ _ => ?_
        rw [map_intCast])
    rw [← h]
    refine Finset.sum_congr rfl fun χ _ => ?_
    rw [map_intCast]
  ·
    intro i j z hz
    exact column_orthogonal B₀ P (fun χ k => v χ k 0 + 2 * v χ k 1) χres (c i j) _ _
      (hnorm i j) (fun χ => (basis.representation χ).character z) (fun k hk => hoddZ k hk z hz)
      (fun x hx => generic_column_odd_order hA hn basis ideal principal hprincipal (hPne x hx) hz)
  ·
    intro i j
    have h := column_orthogonal B₀ P (fun χ k => v χ k 0 + 2 * v χ k 1) χres (c i j) _ _
      (hnorm i j) (fun χ => (basis.representation χ).character 1)
      (fun k hk => hoddZ k hk 1 (by rw [orderOf_one]; exact odd_one))
      (fun x hx => generic_column_odd_order hA hn basis ideal principal hprincipal (hPne x hx)
        (by rw [orderOf_one]; exact odd_one))
    rw [← h]
    refine Finset.sum_congr rfl fun χ _ => ?_
    rw [FiniteComplexRepresentation.character, Representation.char_one, Complex.conj_natCast]
  ·
    intro j χ hχ
    rw [hClbase, hClbase]
    exact second_row_identity hc hgen hσ hυ hint hζ hlam (χres χ) (v χ) q₀ (hval χ hχ) j
  ·
    intro χ hχ k hk
    have h := second_row_reconstruction hc hgen hσ hυ hint hζ hlam (χres χ) (v χ) q₀
      (hval χ hχ) hk
    rw [h]
    congr 1
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [hClbase, hClbase]
    rfl
  ·
    intro χ hχ k hk z hz hzodd
    have hw := hv χ hχ k hk z (by
      show z ∈ centralSylowPowerCentralizer n S e (k : ℕ)
      rw [hCk]
      exact hz) hzodd
    have h := two_mul_row_value hc hgen hσ hυ hint hζ hlam (χres χ) (v χ) q₀ (hval χ hχ) hk
      (ε * ΦN z) _ hw
    rw [h]
    congr 2
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [hClbase, hClbase]
  ·
    intro j hj hjodd χ hχ
    have hpar := base_column_parity hc hgen hσ hυ hint hζ hlam (χres χ) (v χ) q₀ (hval χ hχ)
      ⟨2 ^ (n - 1), by
        simp only [m]
        rw [← two_mul, ← pow_succ']
        congr 1
        omega⟩
      (fun i j => by rw [← hcbase]; exact hcint i j χ hχ)
      (fun i j => by rw [← hcbase, ← hcbase]; exact (hcsym i j χ).1)
      (fun j => hFint χ hχ 1 j) (fun j => hFint χ hχ 0 j)
    obtain ⟨k, hk⟩ := hpar.1 j hj hjodd
    exact ⟨k, by rw [hcbase]; exact hk⟩
  ·
    intro j hj hjeven r hr χ hχ
    have hpar := base_column_parity hc hgen hσ hυ hint hζ hlam (χres χ) (v χ) q₀ (hval χ hχ)
      ⟨2 ^ (n - 1), by
        simp only [m]
        rw [← two_mul, ← pow_succ']
        congr 1
        omega⟩
      (fun i j => by rw [← hcbase]; exact hcint i j χ hχ)
      (fun i j => by rw [← hcbase, ← hcbase]; exact (hcsym i j χ).1)
      (fun j => hFint χ hχ 1 j) (fun j => hFint χ hχ 0 j)
    obtain ⟨k, hk⟩ := hpar.2 j hj hjeven r hr
    exact ⟨k, by rw [hcbase, hcbase, hcbase]; exact hk⟩
  ·
    intro χ hχ
    have hpar := base_column_parity hc hgen hσ hυ hint hζ hlam (χres χ) (v χ) q₀ (hval χ hχ)
      ⟨2 ^ (n - 1), by
        simp only [m]
        rw [← two_mul, ← pow_succ']
        congr 1
        omega⟩
      (fun i j => by rw [← hcbase]; exact hcint i j χ hχ)
      (fun i j => by rw [← hcbase, ← hcbase]; exact (hcsym i j χ).1)
      (fun j => hFint χ hχ 1 j) (fun j => hFint χ hχ 0 j)
    have h1m : 1 ∈ Finset.Ico 1 m := Finset.mem_Ico.mpr ⟨le_rfl, by omega⟩
    obtain ⟨k₁, hk₁⟩ := hpar.1 1 h1m odd_one
    have hY := hFcpar 1 h1m odd_one χ hχ
    obtain ⟨k₂, hk₂⟩ := (Int.ModEq.dvd hY.symm)
    refine ⟨k₂ - k₁, ?_⟩
    rw [hcbase]
    have : Fact (1 < m) := ⟨by omega⟩
    have hX1 : zmodFourier ζ (fun k => v χ k 0) ((1 : ℕ) : ZMod m) = (Fc χ 1 0 : ℂ) := by
      rw [hFc χ hχ 1 h1m 0]
      simp only [zmodFourier, Nat.cast_one]
      rw [ZMod.val_one]
    rw [hX1] at hk₁
    have hk₂i : Fc χ 1 0 - Y 0 χ = 2 * k₂ := hk₂
    have hk₂' : (Fc χ 1 0 : ℂ) - ((Y 0 χ : ℤ) : ℂ) = 2 * k₂ := by exact_mod_cast hk₂i
    push_cast
    linear_combination hk₂' - hk₁


theorem general_base_core
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
    (hprincipal : (basis.representation principal).character = 1)
    (F : Type) [Field F] [Finite F] (Sigma : Subgroup (F ≃+* F)) (b : Fˣ)
    (hSigma : ∀ σ ∈ Sigma, σ (b : F) = b)
    (ρ : centralizerFullQuotient n hn S e →* coordinateE F)
    (Ψ : SemilinearExtension F b (2 ^ n) (wreathModulus_pos n) (wreathModulus_even hn) Sigma
      hSigma ≃* centralizerOddCoreQuotient n S e)
    (hdata : ConditionalCompatibleModelData n hn S e p f F Sigma b hSigma ρ Ψ)
    (U : Subgroup G) (hU : U = modelBase S e) :
      let m : ℕ := 2 ^ n
      let M : ℕ := m / 2
      let w : G := wreathModelHom S e (Original.z m)
      let a : G := wreathModelHom S e (Original.a m)
      let y : G := wreathModelHom S e (Original.s m * Original.z m)
      let ΦH : centralizerOddCoreQuotient n S e → ℂ := fun h =>
        (Nat.card {x : Omega F // ((ρ (centralizerFullQuotientMap n hn S e h) : coordinateE F) :
          Equiv.Perm (Omega F)) x = x} : ℂ) - 1
      let ΦN : G → ℂ := fun g => if hg : g ∈ involutionCentralizer n S e then
        ΦH (centralizerOddCoreMap n S e ⟨g, hg⟩) else 0
      let ε : ℤ := if Nat.card F % 4 = 1 then 1 else -1
      let q : ℕ := Nat.card F
      let q₀ : ℤ := (ε * q - 1) / m
      let B₀ := coefficientBlock basis (localizedComplexIntegerRing ideal) principal
      let K := dualGroup m
      (m : ℤ) ∣ ε * q - 1 ∧
      MulAction.orbit K ((0 : ZMod m), (0 : ZMod m)) = {(0, 0)} ∧
      (∀ r : ZMod m, r ≠ 0 → (MulAction.orbit K (r, r)).ncard = 3) ∧
      Set.InjOn (fun r : ZMod m => MulAction.orbit K (r, r)) {r | r ≠ 0} ∧
      (∀ I : ZMod m × ZMod m, MulAction.orbit K I = {(0, 0)} ∨
        (∃ r : ZMod m, r ≠ 0 ∧ MulAction.orbit K I = MulAction.orbit K (r, r)) ∨
        (MulAction.orbit K I).ncard = 6) ∧
      ((fun I : ZMod m × ZMod m => MulAction.orbit K I) ''
        {I | (MulAction.orbit K I).ncard = 3}).ncard = m - 1 ∧
      ((fun I : ZMod m × ZMod m => MulAction.orbit K I) ''
        {I | (MulAction.orbit K I).ncard = 6}).ncard = (m - 1) * (m - 2) / 6 ∧
      (∃ σ υ g : G, IsAdaptedBase U a w σ υ g) ∧
      ∀ ζ : ℂ, IsPrimitiveRoot ζ m → ∀ θ : ℂ, IsPrimitiveRoot θ (2 * m) → θ ^ 2 = ζ →
      let ν : basis.index → ℕ → ℕ := fun χ t' =>
        Module.finrank ℂ (Module.End.eigenspace ((basis.representation χ).representation y)
          (θ ^ t'))
      let Y : ℕ → basis.index → ℤ := fun r χ => (ν χ (2 * r) : ℤ) - ν χ (2 * r + m)
      (∃ v : basis.index → ℕ → Fin 2 → ℂ, IsCentralSectionRows basis ideal principal a m
        (fun k => centralSylowPowerCentralizer n S e k) ΦN ε v) ∧
      ∀ v : basis.index → ℕ → Fin 2 → ℂ, IsCentralSectionRows basis ideal principal a m
        (fun k => centralSylowPowerCentralizer n S e k) ΦN ε v →
      let X : ZMod m → basis.index → ℂ := fun j χ =>
        fourierTransform m ζ (fun k => v χ k 0) j.val
      let Fs : ZMod m → basis.index → ℂ := fun j χ =>
        fourierTransform m ζ (fun k => v χ k 1) j.val
      ∀ (σ υ : U) (g : G), IsAdaptedBase U a w σ υ g →
      (∃ lam : ZMod m → ZMod m → U →* ℂ,
        ∀ i j, lam i j σ = ζ ^ i.val ∧ lam i j υ = ζ ^ j.val) ∧
      ∀ lam : ZMod m → ZMod m → U →* ℂ,
        (∀ i j, lam i j σ = ζ ^ i.val ∧ lam i j υ = ζ ^ j.val) →
      let tm : ZMod m → ZMod m → basis.index → ℂ := fun i j χ =>
        (Nat.card U : ℂ)⁻¹ * ∑ u : U, (basis.representation χ).character u * conj (lam i j u)
      let c : ZMod m → ZMod m → basis.index → ℂ := fun i j χ =>
        tm 0 0 χ - tm i j χ + q₀ * (Fs i χ + Fs j χ + Fs (-i - j) χ)
      let Cl : ZMod m → basis.index → ℂ := fun l χ => ∑ i : ZMod m, c i (l - i) χ
      (∀ i j χ, ∃ k : ℕ, tm i j χ = k) ∧
      (∀ i j, ∀ χ ∈ B₀, ∃ z : ℤ, c i j χ = z) ∧
      (∀ χ, c 0 0 χ = 0) ∧
      (∀ i j χ, c i j χ = c j i χ ∧ c i j χ = c j (-i - j) χ) ∧
      (∀ i j, (i, j) ≠ (0, 0) → c i j principal = 1) ∧
      (∀ V : Finset (ZMod m × ZMod m), (∀ I ∈ V, (MulAction.orbit K I).ncard = 6) →
        (∀ I, (MulAction.orbit K I).ncard = 6 → ∃! J, J ∈ V ∧ J ∈ MulAction.orbit K I) →
        (∀ r : ZMod m, r ≠ 0 → ∑ χ ∈ B₀, c r r χ * conj (c r r χ) = 8) ∧
        (∀ I ∈ V, ∑ χ ∈ B₀, c I.1 I.2 χ * conj (c I.1 I.2 χ) = 7) ∧
        (∀ r r' : ZMod m, r ≠ 0 → r' ≠ 0 → r ≠ r' →
          ∑ χ ∈ B₀, c r r χ * conj (c r' r' χ) = 6) ∧
        (∀ r : ZMod m, r ≠ 0 → ∀ I ∈ V,
          ∑ χ ∈ B₀, c r r χ * conj (c I.1 I.2 χ) = 6 ∧
            ∑ χ ∈ B₀, c I.1 I.2 χ * conj (c r r χ) = 6) ∧
        ∀ I ∈ V, ∀ J ∈ V, I ≠ J → ∑ χ ∈ B₀, c I.1 I.2 χ * conj (c J.1 J.2 χ) = 6) ∧
      (∀ i j, ∀ j' ∈ Finset.Ico 1 m, ∑ χ ∈ B₀, c i j χ * conj (X j' χ) = 0) ∧
      (∀ i j, ∀ r < M, ∑ χ ∈ B₀, c i j χ * (Y r χ : ℂ) = 0) ∧
      (∀ i j, ∀ z : G, Odd (orderOf z) →
        ∑ χ ∈ B₀, c i j χ * conj ((basis.representation χ).character z) = 0) ∧
      (∀ i j, ∑ χ ∈ B₀, c i j χ * (basis.representation χ).character 1 = 0) ∧
      (∀ j : ZMod m, ∀ χ ∈ B₀, X j χ + 2 * Fs j χ = Cl 0 χ - Cl (-j) χ) ∧
      (∀ χ ∈ B₀, ∀ k ∈ Finset.Ico 1 m, v χ k 1 = (1 / 2) * ∑ j ∈ Finset.Ico 1 m,
        ζ ^ (-((j : ℤ) * k)) * (Cl 0 χ - Cl (-(j : ZMod m)) χ - X j χ)) ∧
      (∀ χ ∈ B₀, ∀ k ∈ Finset.Ico 1 m, ∀ z ∈ Subgroup.centralizer {a ^ k}, Odd (orderOf z) →
        2 * (basis.representation χ).character (a ^ k * z) =
          (1 - ε * ΦN z) * ∑ j ∈ Finset.Ico 1 m, ζ ^ (-((j : ℤ) * k)) * X j χ +
          (1 + ε * ΦN z) * ∑ j ∈ Finset.Ico 1 m,
            ζ ^ (-((j : ℤ) * k)) * (Cl 0 χ - Cl (-(j : ZMod m)) χ)) ∧
      (∀ j ∈ Finset.Ico 1 m, Odd j → ∀ χ ∈ B₀, ∃ k : ℤ, X j χ - c M M χ = 2 * k) ∧
      (∀ j ∈ Finset.Ico 1 m, Even j → ∀ r : ZMod m, 2 * r = -(j : ZMod m) → ∀ χ ∈ B₀,
        ∃ k : ℤ, X j χ - (c M M χ + c r r χ + c (r + M) (r + M) χ) = 2 * k) ∧
      (∀ χ ∈ B₀, ∃ k : ℤ, c M M χ - Y 0 χ = 2 * k) :=
  general_base_core_of_localHyp n hn S e p f hp hpodd hf
    (ConditionalLocalHyp.of_isSimpleGroup hnonab n hn S e hfour p f hp hpodd hf hmodel)
    ideal basis principal hprincipal F Sigma b hSigma ρ Ψ hdata U hU

theorem conditional_general_base_integral_columns_and_second_row_reconstruction_of_localHyp
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
      let M : ℕ := m / 2
      let s : G := wreathModelHom S e (Original.s m)
      let t : G := wreathModelHom S e (Original.t m)
      let w : G := wreathModelHom S e (Original.z m)
      let a : G := wreathModelHom S e (Original.a m)
      let y : G := wreathModelHom S e (Original.s m * Original.z m)
      let U : Subgroup G := Subgroup.closure {s, t}
      let ΦH : centralizerOddCoreQuotient n S e → ℂ := fun h =>
        (Nat.card {x : Omega F // ((ρ (centralizerFullQuotientMap n hn S e h) : coordinateE F) :
          Equiv.Perm (Omega F)) x = x} : ℂ) - 1
      let ΦN : G → ℂ := fun g => if hg : g ∈ involutionCentralizer n S e then
        ΦH (centralizerOddCoreMap n S e ⟨g, hg⟩) else 0
      let ε : ℤ := if Nat.card F % 4 = 1 then 1 else -1
      let q : ℕ := Nat.card F
      let q₀ : ℤ := (ε * q - 1) / m
      let B₀ := coefficientBlock basis (localizedComplexIntegerRing ideal) principal
      let K := dualGroup m
      (m : ℤ) ∣ ε * q - 1 ∧
      MulAction.orbit K ((0 : ZMod m), (0 : ZMod m)) = {(0, 0)} ∧
      (∀ r : ZMod m, r ≠ 0 → (MulAction.orbit K (r, r)).ncard = 3) ∧
      Set.InjOn (fun r : ZMod m => MulAction.orbit K (r, r)) {r | r ≠ 0} ∧
      (∀ I : ZMod m × ZMod m, MulAction.orbit K I = {(0, 0)} ∨
        (∃ r : ZMod m, r ≠ 0 ∧ MulAction.orbit K I = MulAction.orbit K (r, r)) ∨
        (MulAction.orbit K I).ncard = 6) ∧
      ((fun I : ZMod m × ZMod m => MulAction.orbit K I) ''
        {I | (MulAction.orbit K I).ncard = 3}).ncard = m - 1 ∧
      ((fun I : ZMod m × ZMod m => MulAction.orbit K I) ''
        {I | (MulAction.orbit K I).ncard = 6}).ncard = (m - 1) * (m - 2) / 6 ∧
      (∃ σ υ g : G, IsAdaptedBase U a w σ υ g) ∧
      ∀ ζ : ℂ, IsPrimitiveRoot ζ m → ∀ θ : ℂ, IsPrimitiveRoot θ (2 * m) → θ ^ 2 = ζ →
      let ν : basis.index → ℕ → ℕ := fun χ t' =>
        Module.finrank ℂ (Module.End.eigenspace ((basis.representation χ).representation y)
          (θ ^ t'))
      let Y : ℕ → basis.index → ℤ := fun r χ => (ν χ (2 * r) : ℤ) - ν χ (2 * r + m)
      (∃ v : basis.index → ℕ → Fin 2 → ℂ, IsCentralSectionRows basis ideal principal a m
        (fun k => centralSylowPowerCentralizer n S e k) ΦN ε v) ∧
      ∀ v : basis.index → ℕ → Fin 2 → ℂ, IsCentralSectionRows basis ideal principal a m
        (fun k => centralSylowPowerCentralizer n S e k) ΦN ε v →
      let X : ZMod m → basis.index → ℂ := fun j χ =>
        fourierTransform m ζ (fun k => v χ k 0) j.val
      let Fs : ZMod m → basis.index → ℂ := fun j χ =>
        fourierTransform m ζ (fun k => v χ k 1) j.val
      ∀ (σ υ : U) (g : G), IsAdaptedBase U a w σ υ g →
      (∃ lam : ZMod m → ZMod m → U →* ℂ,
        ∀ i j, lam i j σ = ζ ^ i.val ∧ lam i j υ = ζ ^ j.val) ∧
      ∀ lam : ZMod m → ZMod m → U →* ℂ,
        (∀ i j, lam i j σ = ζ ^ i.val ∧ lam i j υ = ζ ^ j.val) →
      let tm : ZMod m → ZMod m → basis.index → ℂ := fun i j χ =>
        (Nat.card U : ℂ)⁻¹ * ∑ u : U, (basis.representation χ).character u * conj (lam i j u)
      let c : ZMod m → ZMod m → basis.index → ℂ := fun i j χ =>
        tm 0 0 χ - tm i j χ + q₀ * (Fs i χ + Fs j χ + Fs (-i - j) χ)
      let Cl : ZMod m → basis.index → ℂ := fun l χ => ∑ i : ZMod m, c i (l - i) χ
      (∀ i j χ, ∃ k : ℕ, tm i j χ = k) ∧
      (∀ i j, ∀ χ ∈ B₀, ∃ z : ℤ, c i j χ = z) ∧
      (∀ χ, c 0 0 χ = 0) ∧
      (∀ i j χ, c i j χ = c j i χ ∧ c i j χ = c j (-i - j) χ) ∧
      (∀ i j, (i, j) ≠ (0, 0) → c i j principal = 1) ∧
      (∀ V : Finset (ZMod m × ZMod m), (∀ I ∈ V, (MulAction.orbit K I).ncard = 6) →
        (∀ I, (MulAction.orbit K I).ncard = 6 → ∃! J, J ∈ V ∧ J ∈ MulAction.orbit K I) →
        (∀ r : ZMod m, r ≠ 0 → ∑ χ ∈ B₀, c r r χ * conj (c r r χ) = 8) ∧
        (∀ I ∈ V, ∑ χ ∈ B₀, c I.1 I.2 χ * conj (c I.1 I.2 χ) = 7) ∧
        (∀ r r' : ZMod m, r ≠ 0 → r' ≠ 0 → r ≠ r' →
          ∑ χ ∈ B₀, c r r χ * conj (c r' r' χ) = 6) ∧
        (∀ r : ZMod m, r ≠ 0 → ∀ I ∈ V,
          ∑ χ ∈ B₀, c r r χ * conj (c I.1 I.2 χ) = 6 ∧
            ∑ χ ∈ B₀, c I.1 I.2 χ * conj (c r r χ) = 6) ∧
        ∀ I ∈ V, ∀ J ∈ V, I ≠ J → ∑ χ ∈ B₀, c I.1 I.2 χ * conj (c J.1 J.2 χ) = 6) ∧
      (∀ i j, ∀ j' ∈ Finset.Ico 1 m, ∑ χ ∈ B₀, c i j χ * conj (X j' χ) = 0) ∧
      (∀ i j, ∀ r < M, ∑ χ ∈ B₀, c i j χ * (Y r χ : ℂ) = 0) ∧
      (∀ i j, ∀ z : G, Odd (orderOf z) →
        ∑ χ ∈ B₀, c i j χ * conj ((basis.representation χ).character z) = 0) ∧
      (∀ i j, ∑ χ ∈ B₀, c i j χ * (basis.representation χ).character 1 = 0) ∧
      (∀ j : ZMod m, ∀ χ ∈ B₀, X j χ + 2 * Fs j χ = Cl 0 χ - Cl (-j) χ) ∧
      (∀ χ ∈ B₀, ∀ k ∈ Finset.Ico 1 m, v χ k 1 = (1 / 2) * ∑ j ∈ Finset.Ico 1 m,
        ζ ^ (-((j : ℤ) * k)) * (Cl 0 χ - Cl (-(j : ZMod m)) χ - X j χ)) ∧
      (∀ χ ∈ B₀, ∀ k ∈ Finset.Ico 1 m, ∀ z ∈ Subgroup.centralizer {a ^ k}, Odd (orderOf z) →
        2 * (basis.representation χ).character (a ^ k * z) =
          (1 - ε * ΦN z) * ∑ j ∈ Finset.Ico 1 m, ζ ^ (-((j : ℤ) * k)) * X j χ +
          (1 + ε * ΦN z) * ∑ j ∈ Finset.Ico 1 m,
            ζ ^ (-((j : ℤ) * k)) * (Cl 0 χ - Cl (-(j : ZMod m)) χ)) ∧
      (∀ j ∈ Finset.Ico 1 m, Odd j → ∀ χ ∈ B₀, ∃ k : ℤ, X j χ - c M M χ = 2 * k) ∧
      (∀ j ∈ Finset.Ico 1 m, Even j → ∀ r : ZMod m, 2 * r = -(j : ZMod m) → ∀ χ ∈ B₀,
        ∃ k : ℤ, X j χ - (c M M χ + c r r χ + c (r + M) (r + M) χ) = 2 * k) ∧
      (∀ χ ∈ B₀, ∃ k : ℤ, c M M χ - Y 0 χ = 2 * k) := by
  refine ⟨hloc.modelData,
    ?_⟩
  intro F _ _ Sigma b hSigma ρ Ψ hdata
  have hU : Subgroup.closure {wreathModelHom S e (Original.s (2 ^ n)),
      wreathModelHom S e (Original.t (2 ^ n))} = modelBase S e := by
    rw [modelBase, ← Original.U_eq, Original.U, MonoidHom.map_closure, Set.image_pair]
  exact general_base_core_of_localHyp n hn S e p f hp hpodd hf hloc ideal basis principal
    hprincipal F Sigma b hSigma ρ Ψ hdata _ hU

theorem conditional_general_base_integral_columns_and_second_row_reconstruction
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
      let M : ℕ := m / 2
      let s : G := wreathModelHom S e (Original.s m)
      let t : G := wreathModelHom S e (Original.t m)
      let w : G := wreathModelHom S e (Original.z m)
      let a : G := wreathModelHom S e (Original.a m)
      let y : G := wreathModelHom S e (Original.s m * Original.z m)
      let U : Subgroup G := Subgroup.closure {s, t}
      let ΦH : centralizerOddCoreQuotient n S e → ℂ := fun h =>
        (Nat.card {x : Omega F // ((ρ (centralizerFullQuotientMap n hn S e h) : coordinateE F) :
          Equiv.Perm (Omega F)) x = x} : ℂ) - 1
      let ΦN : G → ℂ := fun g => if hg : g ∈ involutionCentralizer n S e then
        ΦH (centralizerOddCoreMap n S e ⟨g, hg⟩) else 0
      let ε : ℤ := if Nat.card F % 4 = 1 then 1 else -1
      let q : ℕ := Nat.card F
      let q₀ : ℤ := (ε * q - 1) / m
      let B₀ := coefficientBlock basis (localizedComplexIntegerRing ideal) principal
      let K := dualGroup m
      (m : ℤ) ∣ ε * q - 1 ∧
      MulAction.orbit K ((0 : ZMod m), (0 : ZMod m)) = {(0, 0)} ∧
      (∀ r : ZMod m, r ≠ 0 → (MulAction.orbit K (r, r)).ncard = 3) ∧
      Set.InjOn (fun r : ZMod m => MulAction.orbit K (r, r)) {r | r ≠ 0} ∧
      (∀ I : ZMod m × ZMod m, MulAction.orbit K I = {(0, 0)} ∨
        (∃ r : ZMod m, r ≠ 0 ∧ MulAction.orbit K I = MulAction.orbit K (r, r)) ∨
        (MulAction.orbit K I).ncard = 6) ∧
      ((fun I : ZMod m × ZMod m => MulAction.orbit K I) ''
        {I | (MulAction.orbit K I).ncard = 3}).ncard = m - 1 ∧
      ((fun I : ZMod m × ZMod m => MulAction.orbit K I) ''
        {I | (MulAction.orbit K I).ncard = 6}).ncard = (m - 1) * (m - 2) / 6 ∧
      (∃ σ υ g : G, IsAdaptedBase U a w σ υ g) ∧
      ∀ ζ : ℂ, IsPrimitiveRoot ζ m → ∀ θ : ℂ, IsPrimitiveRoot θ (2 * m) → θ ^ 2 = ζ →
      let ν : basis.index → ℕ → ℕ := fun χ t' =>
        Module.finrank ℂ (Module.End.eigenspace ((basis.representation χ).representation y)
          (θ ^ t'))
      let Y : ℕ → basis.index → ℤ := fun r χ => (ν χ (2 * r) : ℤ) - ν χ (2 * r + m)
      (∃ v : basis.index → ℕ → Fin 2 → ℂ, IsCentralSectionRows basis ideal principal a m
        (fun k => centralSylowPowerCentralizer n S e k) ΦN ε v) ∧
      ∀ v : basis.index → ℕ → Fin 2 → ℂ, IsCentralSectionRows basis ideal principal a m
        (fun k => centralSylowPowerCentralizer n S e k) ΦN ε v →
      let X : ZMod m → basis.index → ℂ := fun j χ =>
        fourierTransform m ζ (fun k => v χ k 0) j.val
      let Fs : ZMod m → basis.index → ℂ := fun j χ =>
        fourierTransform m ζ (fun k => v χ k 1) j.val
      ∀ (σ υ : U) (g : G), IsAdaptedBase U a w σ υ g →
      (∃ lam : ZMod m → ZMod m → U →* ℂ,
        ∀ i j, lam i j σ = ζ ^ i.val ∧ lam i j υ = ζ ^ j.val) ∧
      ∀ lam : ZMod m → ZMod m → U →* ℂ,
        (∀ i j, lam i j σ = ζ ^ i.val ∧ lam i j υ = ζ ^ j.val) →
      let tm : ZMod m → ZMod m → basis.index → ℂ := fun i j χ =>
        (Nat.card U : ℂ)⁻¹ * ∑ u : U, (basis.representation χ).character u * conj (lam i j u)
      let c : ZMod m → ZMod m → basis.index → ℂ := fun i j χ =>
        tm 0 0 χ - tm i j χ + q₀ * (Fs i χ + Fs j χ + Fs (-i - j) χ)
      let Cl : ZMod m → basis.index → ℂ := fun l χ => ∑ i : ZMod m, c i (l - i) χ
      (∀ i j χ, ∃ k : ℕ, tm i j χ = k) ∧
      (∀ i j, ∀ χ ∈ B₀, ∃ z : ℤ, c i j χ = z) ∧
      (∀ χ, c 0 0 χ = 0) ∧
      (∀ i j χ, c i j χ = c j i χ ∧ c i j χ = c j (-i - j) χ) ∧
      (∀ i j, (i, j) ≠ (0, 0) → c i j principal = 1) ∧
      (∀ V : Finset (ZMod m × ZMod m), (∀ I ∈ V, (MulAction.orbit K I).ncard = 6) →
        (∀ I, (MulAction.orbit K I).ncard = 6 → ∃! J, J ∈ V ∧ J ∈ MulAction.orbit K I) →
        (∀ r : ZMod m, r ≠ 0 → ∑ χ ∈ B₀, c r r χ * conj (c r r χ) = 8) ∧
        (∀ I ∈ V, ∑ χ ∈ B₀, c I.1 I.2 χ * conj (c I.1 I.2 χ) = 7) ∧
        (∀ r r' : ZMod m, r ≠ 0 → r' ≠ 0 → r ≠ r' →
          ∑ χ ∈ B₀, c r r χ * conj (c r' r' χ) = 6) ∧
        (∀ r : ZMod m, r ≠ 0 → ∀ I ∈ V,
          ∑ χ ∈ B₀, c r r χ * conj (c I.1 I.2 χ) = 6 ∧
            ∑ χ ∈ B₀, c I.1 I.2 χ * conj (c r r χ) = 6) ∧
        ∀ I ∈ V, ∀ J ∈ V, I ≠ J → ∑ χ ∈ B₀, c I.1 I.2 χ * conj (c J.1 J.2 χ) = 6) ∧
      (∀ i j, ∀ j' ∈ Finset.Ico 1 m, ∑ χ ∈ B₀, c i j χ * conj (X j' χ) = 0) ∧
      (∀ i j, ∀ r < M, ∑ χ ∈ B₀, c i j χ * (Y r χ : ℂ) = 0) ∧
      (∀ i j, ∀ z : G, Odd (orderOf z) →
        ∑ χ ∈ B₀, c i j χ * conj ((basis.representation χ).character z) = 0) ∧
      (∀ i j, ∑ χ ∈ B₀, c i j χ * (basis.representation χ).character 1 = 0) ∧
      (∀ j : ZMod m, ∀ χ ∈ B₀, X j χ + 2 * Fs j χ = Cl 0 χ - Cl (-j) χ) ∧
      (∀ χ ∈ B₀, ∀ k ∈ Finset.Ico 1 m, v χ k 1 = (1 / 2) * ∑ j ∈ Finset.Ico 1 m,
        ζ ^ (-((j : ℤ) * k)) * (Cl 0 χ - Cl (-(j : ZMod m)) χ - X j χ)) ∧
      (∀ χ ∈ B₀, ∀ k ∈ Finset.Ico 1 m, ∀ z ∈ Subgroup.centralizer {a ^ k}, Odd (orderOf z) →
        2 * (basis.representation χ).character (a ^ k * z) =
          (1 - ε * ΦN z) * ∑ j ∈ Finset.Ico 1 m, ζ ^ (-((j : ℤ) * k)) * X j χ +
          (1 + ε * ΦN z) * ∑ j ∈ Finset.Ico 1 m,
            ζ ^ (-((j : ℤ) * k)) * (Cl 0 χ - Cl (-(j : ZMod m)) χ)) ∧
      (∀ j ∈ Finset.Ico 1 m, Odd j → ∀ χ ∈ B₀, ∃ k : ℤ, X j χ - c M M χ = 2 * k) ∧
      (∀ j ∈ Finset.Ico 1 m, Even j → ∀ r : ZMod m, 2 * r = -(j : ZMod m) → ∀ χ ∈ B₀,
        ∃ k : ℤ, X j χ - (c M M χ + c r r χ + c (r + M) (r + M) χ) = 2 * k) ∧
      (∀ χ ∈ B₀, ∃ k : ℤ, c M M χ - Y 0 χ = 2 * k) :=
  conditional_general_base_integral_columns_and_second_row_reconstruction_of_localHyp n hn S e p f
    hp hpodd hf
    (ConditionalLocalHyp.of_isSimpleGroup hnonab n hn S e hfour p f hp hpodd hf hmodel)
    ideal basis principal hprincipal

end CFSG.Wreathed.ConditionalGeneralBase

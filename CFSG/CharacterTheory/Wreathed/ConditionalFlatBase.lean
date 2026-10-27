module

public import CFSG.CharacterTheory.Wreathed.ConditionalFlatBaseColumns
public import CFSG.CharacterTheory.Wreathed.ConditionalFlatSquareRoot
public import CFSG.CharacterTheory.Wreathed.ConditionalGeneralBase

public section

open scoped BigOperators Classical ComplexConjugate

namespace CFSG.Wreathed.FlatBase

open CFSG.TwoRankLowerBound.Helpers CFSG.Semidihedral.Principal
  CFSG.ComponentClassification.CatalogueSchreierLinearTwo
  CFSG.Semidihedral.SemilinearOddExtensions CFSG.Wreathed.ActualProjectiveLayer
  CFSG.Wreathed.FullDefectLabels CFSG.Wreathed.ConditionalFourier
  CFSG.Wreathed.FlatCentralFourier CFSG.Wreathed.AdaptedBaseFusion
  CFSG.Wreathed.ConditionalGeneralBase

theorem flat_base_core
    {G : Type} [Group G] [Fintype G] [IsSimpleGroup G]
    (hnonab : ∃ a b : G, a * b ≠ b * a) (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G)
    (e : S ≃* Wreath (2 ^ n))
    (hfour : ¬ Nonempty (centralizerFullQuotient n hn S e ≃* Equiv.Perm (Fin 4)))
    (p f : ℕ) (hp : p.Prime) (hpodd : p ≠ 2) (hf : 1 ≤ f)
    (hmodel : PSLTwoClassicalModel (centralizerSimpleLayer n hn S e) p f)
    (ideal : Ideal ComplexAlgebraicIntegers) [ideal.IsMaximal]
    [CharP (ComplexAlgebraicIntegers ⧸ ideal) 2] (basis : FiniteIrreducibleCharacterBasis G)
    (B : basis.index) (hflat : FlatWreathedBlock basis ideal S e B)
    (eb : FiniteIrreducibleCharacterBasis (BaseFourCentralizerStructure.ambientOddCore
      (Subgroup.centralizer ((S : Subgroup G) : Set G)))) (θB : eb.index)
    (nb : FiniteIrreducibleCharacterBasis (Subgroup.normalizer ((S : Subgroup G) : Set G)))
    (θhat : nb.index) (hθ : InflatedLabel (oddCore_le_normalizer S) nb eb θB θhat)
    (hB : brauerNormalizerCharacterResidueHom ideal 2 (S : Subgroup G) S.isPGroup'
        (Subgroup.normalizer ((S : Subgroup G) : Set G)) (Subgroup.centralizer_le_normalizer _)
        le_rfl nb θhat = centralCharacterResidueHom basis ideal B)
    (η : G) (hη : η ∈ Subgroup.normalizer (modelBase S e : Set G))
    (hord : orderOf ((modelBase S e).normalizerMonoidHom ⟨η, hη⟩) = 3)
    (lam : involutionCentralizer n S e →* ℂˣ)
    (hlam : (∀ (v : involutionCentralizer n S e) (z : BaseFourCentralizerStructure.ambientOddCore
        (Subgroup.centralizer ((S : Subgroup G) : Set G))),
        (v : G) = z → (lam v : ℂ) = (eb.representation θB).character z) ∧
      (∀ v : involutionCentralizer n S e, (v : G) ∈ (S : Subgroup G) → lam v = 1) ∧
      ∀ c c' : involutionCentralizer n S e,
        (c : G) ∈ Subgroup.centralizer (Subgroup.closure
          {wreathModelHom S e (Original.s (2 ^ n)) ^ (2 ^ n / 2),
            wreathModelHom S e (Original.t (2 ^ n)) ^ (2 ^ n / 2)} : Set G) →
        (c' : G) = η⁻¹ * c * η → lam c' = lam c)
    (F : Type) [Field F] [Finite F] (sigmaGroup : Subgroup (F ≃+* F))
    (ρ : centralizerFullQuotient n hn S e →* coordinateE F)
    (hcard : Nat.card F = p ^ f) (hodd : Odd (Nat.card sigmaGroup)) (hρ : Function.Injective ρ)
    (hlayer : (centralizerSimpleLayer n hn S e).map ρ = specialLayer F)
    (hrange : ρ.range = CFSG.Semidihedral.OddFieldLift.Gamma F sigmaGroup)
    (U : Subgroup G) (hU : U = modelBase S e) :
      let m : ℕ := 2 ^ n
      let M : ℕ := m / 2
      let w : G := wreathModelHom S e (Original.z m)
      let a : G := wreathModelHom S e (Original.a m)
      let y : G := wreathModelHom S e (Original.s m * Original.z m)
      let ΦH : centralizerOddCoreQuotient n S e → ℂ := fun h =>
        (Nat.card {ω : Omega F // ((ρ (centralizerFullQuotientMap n hn S e h) : coordinateE F) :
          Equiv.Perm (Omega F)) ω = ω} : ℂ) - 1
      let ΦN : G → ℂ := fun g => if hg : g ∈ involutionCentralizer n S e then
        ΦH (centralizerOddCoreMap n S e ⟨g, hg⟩) else 0
      let lamN : G → ℂ := fun g => if hg : g ∈ involutionCentralizer n S e then
        (lam ⟨g, hg⟩ : ℂ) else 0
      let ε : ℤ := if Nat.card F % 4 = 1 then 1 else -1
      let q : ℕ := Nat.card F
      let q₀ : ℤ := (ε * q - 1) / m
      let BB := coefficientBlock basis (localizedComplexIntegerRing ideal) B
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
      (∃ v : basis.index → ℕ → Fin 2 → ℂ, IsTwistedCentralSectionRows basis ideal B a m
        (fun k => centralSylowPowerCentralizer n S e k) lamN ΦN ε v) ∧
      ∀ v : basis.index → ℕ → Fin 2 → ℂ, IsTwistedCentralSectionRows basis ideal B a m
        (fun k => centralSylowPowerCentralizer n S e k) lamN ΦN ε v →
      let X : ZMod m → basis.index → ℂ := fun j χ =>
        fourierTransform m ζ (fun k => v χ k 0) j.val
      let Fs : ZMod m → basis.index → ℂ := fun j χ =>
        fourierTransform m ζ (fun k => v χ k 1) j.val
      ∀ (σ υ : U) (g : G), IsAdaptedBase U a w σ υ g →
      (∃ lamU : ZMod m → ZMod m → U →* ℂ,
        ∀ i j, lamU i j σ = ζ ^ i.val ∧ lamU i j υ = ζ ^ j.val) ∧
      ∀ lamU : ZMod m → ZMod m → U →* ℂ,
        (∀ i j, lamU i j σ = ζ ^ i.val ∧ lamU i j υ = ζ ^ j.val) →
      let tm : ZMod m → ZMod m → basis.index → ℂ := fun i j χ =>
        (Nat.card U : ℂ)⁻¹ * ∑ u : U, (basis.representation χ).character u * conj (lamU i j u)
      let c : ZMod m → ZMod m → basis.index → ℂ := fun i j χ =>
        tm 0 0 χ - tm i j χ + q₀ * (Fs i χ + Fs j χ + Fs (-i - j) χ)
      let Cl : ZMod m → basis.index → ℂ := fun l χ => ∑ i : ZMod m, c i (l - i) χ
      (∀ i j χ, ∃ k : ℕ, tm i j χ = k) ∧
      (∀ i j, ∀ χ ∈ BB, ∃ z : ℤ, c i j χ = z) ∧
      (∀ χ, c 0 0 χ = 0) ∧
      (∀ i j χ, c i j χ = c j i χ ∧ c i j χ = c j (-i - j) χ) ∧
      (∀ V : Finset (ZMod m × ZMod m), (∀ I ∈ V, (MulAction.orbit K I).ncard = 6) →
        (∀ I, (MulAction.orbit K I).ncard = 6 → ∃! J, J ∈ V ∧ J ∈ MulAction.orbit K I) →
        (∀ r : ZMod m, r ≠ 0 → ∑ χ ∈ BB, c r r χ * conj (c r r χ) = 8) ∧
        (∀ I ∈ V, ∑ χ ∈ BB, c I.1 I.2 χ * conj (c I.1 I.2 χ) = 7) ∧
        (∀ r r' : ZMod m, r ≠ 0 → r' ≠ 0 → r ≠ r' →
          ∑ χ ∈ BB, c r r χ * conj (c r' r' χ) = 6) ∧
        (∀ r : ZMod m, r ≠ 0 → ∀ I ∈ V,
          ∑ χ ∈ BB, c r r χ * conj (c I.1 I.2 χ) = 6 ∧
            ∑ χ ∈ BB, c I.1 I.2 χ * conj (c r r χ) = 6) ∧
        ∀ I ∈ V, ∀ J ∈ V, I ≠ J → ∑ χ ∈ BB, c I.1 I.2 χ * conj (c J.1 J.2 χ) = 6) ∧
      (∀ i j, ∀ j' ∈ Finset.Ico 1 m, ∑ χ ∈ BB, c i j χ * conj (X j' χ) = 0) ∧
      (∀ i j, ∀ r < M, ∑ χ ∈ BB, c i j χ * (Y r χ : ℂ) = 0) ∧
      (∀ i j, ∀ z : G, Odd (orderOf z) →
        ∑ χ ∈ BB, c i j χ * conj ((basis.representation χ).character z) = 0) ∧
      (∀ i j, ∑ χ ∈ BB, c i j χ * (basis.representation χ).character 1 = 0) ∧
      (∀ j : ZMod m, ∀ χ ∈ BB, X j χ + 2 * Fs j χ = Cl 0 χ - Cl (-j) χ) ∧
      (∀ χ ∈ BB, ∀ k ∈ Finset.Ico 1 m, v χ k 1 = (1 / 2) * ∑ j ∈ Finset.Ico 1 m,
        ζ ^ (-((j : ℤ) * k)) * (Cl 0 χ - Cl (-(j : ZMod m)) χ - X j χ)) ∧
      (∀ χ ∈ BB, ∀ k ∈ Finset.Ico 1 m, ∀ z ∈ Subgroup.centralizer {a ^ k}, Odd (orderOf z) →
        2 * (basis.representation χ).character (a ^ k * z) =
          lamN z * ((1 - ε * ΦN z) * ∑ j ∈ Finset.Ico 1 m, ζ ^ (-((j : ℤ) * k)) * X j χ +
            (1 + ε * ΦN z) * ∑ j ∈ Finset.Ico 1 m,
              ζ ^ (-((j : ℤ) * k)) * (Cl 0 χ - Cl (-(j : ZMod m)) χ))) ∧
      (∀ j ∈ Finset.Ico 1 m, Odd j → ∀ χ ∈ BB, ∃ k : ℤ, X j χ - c M M χ = 2 * k) ∧
      (∀ j ∈ Finset.Ico 1 m, Even j → ∀ r : ZMod m, 2 * r = -(j : ZMod m) → ∀ χ ∈ BB,
        ∃ k : ℤ, X j χ - (c M M χ + c r r χ + c (r + M) (r + M) χ) = 2 * k) ∧
      (∀ χ ∈ BB, ∃ k : ℤ, c M M χ - Y 0 χ = 2 * k) := by
  intro m M w a y ΦH ΦN lamN ε q q₀ BB K
  subst hU
  have hm4 : 4 ≤ m := by
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  obtain ⟨-, -, hall⟩ := conditional_flat_local_twisted_regular_bases hnonab n hn S e hfour
    p f hp hpodd hf hmodel ideal basis B hflat eb θB nb θhat hθ hB η hη hord
  obtain ⟨hLoc, -, -, hDgen⟩ := hall lam hlam
  have hcentral := (conditional_flat_central_section_integral_fourier_columns hnonab n hn S e
    hfour p f hp hpodd hf hmodel ideal basis B hflat eb θB nb θhat hθ hB η hη hord).2.2 lam hlam
    F sigmaGroup ρ hcard hodd hρ hlayer hrange
  have hsqrt := (conditional_flat_square_root_columns_and_parity hnonab n hn S e hfour p f hp
    hpodd hf hmodel ideal basis B hflat eb θB nb θhat hθ hB η hη hord).2.2 lam hlam F sigmaGroup
    ρ hcard hodd hρ hlayer hrange
  have hq3 : 3 ≤ Nat.card F := by
    rw [hcard]
    have hp3 : 3 ≤ p := by
      have := hp.two_le
      omega
    calc 3 ≤ p := hp3
      _ = p ^ 1 := (pow_one p).symm
      _ ≤ p ^ f := Nat.pow_le_pow_right hp.pos hf
  obtain ⟨F', _, _, hcard', -, -, theta', rho', eta', hin', hrho', -, hdata'⟩ :=
    FullCentralizerFromProjectiveModel.actual_projective_model_determines_full_centralizer
      hnonab n hn S e hfour p f hp hpodd hf hmodel
  have hpart : 2 ^ (Nat.card F ^ 2 - 1).factorization 2 = 2 * 2 ^ n := by
    rw [hcard, ← hcard']
    exact hdata'.structural.q_two_part
  have hqodd : Nat.card F % 2 = 1 := by
    rw [hcard]
    exact Nat.odd_iff.mp ((hp.odd_of_ne_two hpodd).pow)
  have hdvd : (m : ℤ) ∣ ε * q - 1 := dvd_eps_mul_sub_one hq3 hqodd hpart
  have hq₀ : (m : ℤ) * q₀ = ε * q - 1 := Int.mul_ediv_cancel' hdvd
  refine ⟨hdvd, orbit_zero, fun r hr => ncard_orbit_diag r hr, orbit_diag_injOn,
    orbit_trichotomy, ncard_orbits_three, ncard_orbits_six,
    (adapted_base_fusion_model hnonab n hn S e).1, ?_⟩
  intro ζ hζ θ hθ hθζ ν Y
  have hm0 : (m : ℂ) ≠ 0 := by exact_mod_cast (show m ≠ 0 by omega)
  have ha : orderOf a = m := orderOf_wreathModelHom_a n S e
  obtain ⟨v₀, -, hv₀row, hv₀uniq, hv₀gram, hv₀odd, -, hv₀int, -, -, -, hv₀inv, -, -⟩ :=
    hcentral ζ hζ
  obtain ⟨hyord, -, -, -, -, hSqζ⟩ := hsqrt
  obtain ⟨-, hYinv, -, -, -, -, -, hYrows⟩ := hSqζ ζ hζ θ hθ hθζ
  refine ⟨⟨v₀, hv₀row⟩, ?_⟩
  intro v hv X Fs
  have hveq : ∀ χ ∈ BB, ∀ k ∈ Finset.Ico 1 m, v χ k = v₀ χ k := fun χ hχ k hk =>
    hv₀uniq χ hχ k hk (v χ k) (fun r hr hodd => hv χ hχ k hk r hr hodd)
  have hfeq : ∀ χ ∈ BB, ∀ (ℓ : Fin 2) (j : ℕ), fourierTransform m ζ (fun k => v χ k ℓ) j =
      fourierTransform m ζ (fun k => v₀ χ k ℓ) j := fun χ hχ ℓ j =>
    fourierTransform_congr (fun k hk => by rw [hveq χ hχ k hk]) j
  have hvgram : ∀ k ∈ Finset.Ico 1 m, ∀ h ∈ Finset.Ico 1 m, ∀ ℓ t,
      ∑ χ ∈ BB, conj (v χ k ℓ) * v χ h t =
        if k = h then (((m : ℤ) • !![4, -2; -2, ((m / 2 + 1 : ℕ) : ℤ)]) ℓ t : ℂ) else 0 := by
    intro k hk h hh ℓ t
    rw [← hv₀gram k hk h hh ℓ t]
    refine Finset.sum_congr rfl fun χ hχ => ?_
    rw [hveq χ hχ k hk, hveq χ hχ h hh]
  have hFint : ∀ χ ∈ BB, ∀ (ℓ : Fin 2) (j : ZMod m),
      ∃ z : ℤ, fourierTransform m ζ (fun k => v χ k ℓ) j.val = z := by
    intro χ hχ ℓ j
    rcases Nat.eq_zero_or_pos j.val with h0 | hpos
    · refine ⟨0, ?_⟩
      rw [h0]
      simp [fourierTransform]
    · rw [hfeq χ hχ]
      exact hv₀int χ hχ j.val (Finset.mem_Ico.mpr ⟨hpos, ZMod.val_lt j⟩) ℓ
  have hvinv : ∀ χ ∈ BB, ∀ k ∈ Finset.Ico 1 m, ∀ ℓ, v χ k ℓ = ∑ j ∈ Finset.Ico 1 m,
      ζ ^ (-((j : ℤ) * k)) * fourierTransform m ζ (fun k => v χ k ℓ) j := by
    intro χ hχ k hk ℓ
    rw [hveq χ hχ k hk, hv₀inv χ hχ k hk ℓ]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [hfeq χ hχ]
  have hvodd : ∀ k ∈ Finset.Ico 1 m, ∀ ℓ, ∀ z : G, Odd (orderOf z) →
      ∑ χ ∈ BB, v χ k ℓ * conj ((basis.representation χ).character z) = 0 := by
    intro k hk ℓ z hz
    rw [← hv₀odd k hk ℓ z hz]
    refine Finset.sum_congr rfl fun χ hχ => ?_
    rw [hveq χ hχ k hk]
  have hlamN : ∀ (g : G) (hg : g ∈ involutionCentralizer n S e), lamN g = lam ⟨g, hg⟩ :=
    fun g hg => dite_eq_left hg
  have hΦN : ∀ (g : G) (hg : g ∈ involutionCentralizer n S e),
      ΦN g = ΦH (centralizerOddCoreMap n S e ⟨g, hg⟩) := fun g hg => dite_eq_left hg
  have hlam1 : lamN 1 = 1 := by
    rw [hlamN 1 (Subgroup.one_mem _)]
    have h1 : (⟨1, Subgroup.one_mem _⟩ : involutionCentralizer n S e) = 1 := rfl
    rw [h1, map_one, Units.val_one]
  have hΦreal : ∀ g, conj (ΦN g) = ΦN g := by
    intro g
    simp only [ΦN, ΦH]
    split_ifs
    · rw [map_sub, map_one, Complex.conj_natCast]
    · rw [map_zero]
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
  have hCkN : ∀ k ∈ Finset.Ico 1 m,
      centralSylowPowerCentralizer n S e k ≤ involutionCentralizer n S e := fun k hk =>
    centralizer_zpow_le_involutionCentralizer n hn S e k (hkdvd k hk)
  have hlam0 : ∀ k ∈ Finset.Ico 1 m, ∀ c ∈ centralSylowPowerCentralizer n S e k,
      lamN c ≠ 0 := fun k hk c hc => by
    rw [hlamN c (hCkN k hk hc)]
    exact (lam ⟨c, hCkN k hk hc⟩).ne_zero
  let _ : Fintype (centralizerOddCoreQuotient n S e) := Fintype.ofFinite _
  obtain ⟨basisH⟩ := finiteIrreducibleCharacterBasis_exists (G := centralizerOddCoreQuotient n S e)
  obtain ⟨principalH, hprincipalH⟩ :=
    finiteIrreducibleCharacterBasis_exists_principal_label basisH
  obtain ⟨basisN⟩ := finiteIrreducibleCharacterBasis_exists (G := involutionCentralizer n S e)
  obtain ⟨principalN, hprincipalN⟩ :=
    finiteIrreducibleCharacterBasis_exists_principal_label basisN
  obtain ⟨-, -, -, hpow⟩ :=
    (conditional_actual_central_power_principal_regular_integral_bases.{0} hnonab n hn S e
      hfour p f hp hpodd hf hmodel ideal basisH principalH hprincipalH basisN principalN
      hprincipalN).2 F sigmaGroup ρ hcard hodd hρ hlayer hrange
  have h1m : 1 ∈ Finset.Ico 1 m := Finset.mem_Ico.mpr ⟨le_rfl, by omega⟩
  obtain ⟨lb₁⟩ := finiteIrreducibleCharacterBasis_exists
    (G := centralSylowPowerCentralizer n S e (1 : ℕ))
  obtain ⟨l₁, hl₁⟩ := finiteIrreducibleCharacterBasis_exists_principal_label lb₁
  obtain ⟨-, hP₁, -⟩ := hpow (1 : ℕ) (hkdvd 1 h1m) lb₁ l₁ hl₁
  have hΦ1 : ΦN 1 = (q : ℂ) := by
    have h := hP₁.degree
    rw [hΦN 1 (Subgroup.one_mem _)]
    exact h
  have hC₁k : ∀ k : ℕ, ∀ y' ∈ centralSylowPowerCentralizer n S e (1 : ℕ),
      y' ∈ centralSylowPowerCentralizer n S e k := by
    intro k y' hy'
    rw [hCk 1, pow_one, Subgroup.mem_centralizer_singleton_iff] at hy'
    rw [hCk k, Subgroup.mem_centralizer_singleton_iff]
    exact ((Commute.pow_left (show Commute a y' from hy'.symm) k).eq).symm
  have hindep : ∀ k ∈ Finset.Ico 1 m, ∀ α β : ℂ,
      (∀ y' ∈ centralSylowPowerCentralizer n S e k, Odd (orderOf y') →
        α + β * (1 + ε * ΦN y') = 0) → α = 0 ∧ β = 0 := by
    intro k _ α β hαβ
    refine eq_zero_of_odd_combination _ ε _ hP₁.degree hP₁.linearIndependent (fun y' hy' => ?_)
    have h := hαβ y' (hC₁k k y' y'.2) (by rwa [Subgroup.orderOf_coe])
    rw [hΦN y' (hCkN 1 h1m y'.2)] at h
    exact h
  intro σ υ g hA
  have hc : Commute σ υ := commute_left_right hA
  have hgen : Subgroup.closure ({σ, υ} : Set (modelBase S e)) = ⊤ := hA.closure_eq_top
  have hσ : orderOf σ = m := orderOf_left' hA
  have hυ : orderOf υ = m := orderOf_right' hA
  have hint : Subgroup.zpowers σ ⊓ Subgroup.zpowers υ = ⊥ := zpowers_left_inf_right' hA
  have hσυ : ((σ * υ : modelBase S e) : G) = a := hA.mul_eq
  have : NeZero m := ⟨by omega⟩
  refine ⟨exists_linearCharacters hc hgen hσ hυ hint hζ, ?_⟩
  intro lamU hlamU tm c Cl
  have hcardU : (Fintype.card (modelBase S e) : ℂ) = (m : ℂ) ^ 2 := by
    rw [card_eq_sq hc hgen hσ hυ hint hζ lamU hlamU]
    push_cast
    ring
  set χres : basis.index → modelBase S e → ℂ := fun χ u => (basis.representation χ).character u
    with hχres
  have hcbase : ∀ i j χ, c i j χ = baseColumn lamU (χres χ) ζ (v χ) (q₀ : ℂ) i j := by
    intro i j χ
    simp only [c, tm, Fs, baseColumn, baseMultiplicity, zmodFourier, hχres,
      Nat.card_eq_fintype_card]
  have hClbase : ∀ l χ, Cl l χ = baseColumnSum lamU (χres χ) ζ (v χ) (q₀ : ℂ) l := by
    intro l χ
    simp only [Cl, baseColumnSum, hcbase]
  have hpowcoe : ∀ k : ℕ, (((σ * υ) ^ k : modelBase S e) : G) = a ^ k := by
    intro k
    rw [Subgroup.coe_pow, hσυ]
  have hval : ∀ χ ∈ BB, ∀ k ∈ Finset.Ico 1 m,
      χres χ ((σ * υ) ^ k) = v χ k 0 + (2 + m * (q₀ : ℂ)) * v χ k 1 := by
    intro χ hχ k hk
    have h := hv χ hχ k hk 1 (Subgroup.one_mem _) (by rw [orderOf_one]; exact odd_one)
    rw [mul_one, hΦ1, hlam1, one_mul] at h
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
  have hnorm : ∀ i j, ∀ χ ∈ BB, (m : ℂ) ^ 2 * c i j χ =
      ∑ k ∈ Finset.Ico 1 m, ((1 - conj (lamU i j ((σ * υ) ^ k))) +
        (1 - conj (lamU i j (σ ^ k)⁻¹)) + (1 - conj (lamU i j (υ ^ k)⁻¹))) *
          (v χ k 0 + 2 * v χ k 1) +
      ∑ x ∈ P, (1 - conj (lamU i j x)) * χres χ x := by
    intro i j χ hχ
    rw [hcbase, ← hcardU]
    exact card_mul_column_eq hc hgen hσ hυ hint hζ lamU hlamU P hsplit (χres χ) (v χ) q₀
      (htriple χ) (hval χ hχ) i j
  have hPne : ∀ u ∈ P, u ∉ hA.exc := fun u hu => (Finset.mem_filter.mp hu).2
  have hgenc : ∀ u : modelBase S e, u ∉ hA.exc →
      (∀ u'' : modelBase S e, ∑ χ ∈ BB, (basis.representation χ).character u *
          conj ((basis.representation χ).character u'') =
        if IsConj (u : G) (u'' : G) then ((2 ^ n : ℕ) : ℂ) ^ 2 else 0) ∧
      (∀ (k : ℕ) (r : G),
        r ∈ Subgroup.centralizer ({wreathModelHom S e (Original.a (2 ^ n)) ^ k} : Set G) →
        Odd (orderOf r) → ∑ χ ∈ BB, (basis.representation χ).character u *
          conj ((basis.representation χ).character
            (wreathModelHom S e (Original.a (2 ^ n)) ^ k * r)) = 0) ∧
      (∀ yy : G, orderOf yy = 2 * 2 ^ n → ∀ t : ℤ, Odd t →
        ∑ χ ∈ BB, (basis.representation χ).character u *
          conj ((basis.representation χ).character (yy ^ t)) = 0) ∧
      ∀ z : G, Odd (orderOf z) →
        ∑ χ ∈ BB, (basis.representation χ).character u *
          conj ((basis.representation χ).character z) = 0 := by
    intro u hu
    obtain ⟨u', hu', hxu', hconj⟩ := (hDgen (σ : G) (υ : G) g hA).2 u hu
    obtain ⟨⟨r, hr1, hr⟩, -⟩ := ConditionalGeneralBase.orderOf_generic hA hu'
    have hgroup : IsPGroup 2 (Subgroup.zpowers (u' : G)) :=
      IsPGroup.of_card (by rw [Nat.card_zpowers, hr])
    obtain ⟨-, hle, hloc⟩ := hLoc (u' : G) hgroup hxu'
    have hlocal : ∀ (lb : FiniteIrreducibleCharacterBasis
        (Subgroup.centralizer (Subgroup.zpowers (u' : G) : Set G))) (ℓ : lb.index),
        (∀ c', (lb.representation ℓ).character c' = lamN c') →
        brauerNormalizerCharacterResidueHom ideal 2 (Subgroup.zpowers (u' : G)) hgroup
            (Subgroup.centralizer (Subgroup.zpowers (u' : G) : Set G)) le_rfl
            (Subgroup.centralizer_le_normalizer _) lb ℓ =
          centralCharacterResidueHom basis ideal B ∧
        ∀ θ', brauerNormalizerCharacterResidueHom ideal 2 (Subgroup.zpowers (u' : G)) hgroup
            (Subgroup.centralizer (Subgroup.zpowers (u' : G) : Set G)) le_rfl
            (Subgroup.centralizer_le_normalizer _) lb θ' =
          centralCharacterResidueHom basis ideal B →
          θ' ∈ coefficientBlock lb (localizedComplexIntegerRing ideal) ℓ := by
      intro lb ℓ hℓ
      obtain ⟨-, hlb⟩ := hloc lb
      obtain ⟨principal, hprincipal⟩ := finiteIrreducibleCharacterBasis_exists_principal_label lb
      have hℓ' : ∀ c', (lb.representation ℓ).character c' =
          lam (Subgroup.inclusion (FlatTwistedBases.centralizer_zpowers_le_involutionCentralizer
            S e hxu') c') := fun c' => by
        rw [hℓ, hlamN c' (hle c'.2)]
        rfl
      obtain ⟨hbrauer, hunique, -⟩ := hlb ℓ principal hℓ' hprincipal
      exact ⟨hbrauer, fun θ' hθ' => (coefficientBlock_mem_iff _ _ _ _).mpr
        (sameCoefficientBlock_symm _ _ (hunique θ' hθ'))⟩
    obtain ⟨lb⟩ := finiteIrreducibleCharacterBasis_exists
      (G := Subgroup.centralizer (Subgroup.zpowers (u' : G) : Set G))
    obtain ⟨ℓ, hℓ⟩ := CompatibleFamily.exists_linear_label lb (lam.comp (Subgroup.inclusion hle))
    have hℓN : ∀ c', (lb.representation ℓ).character c' = lamN c' := fun c' => by
      rw [hℓ, hlamN c' (hle c'.2)]
      rfl
    have hdata := (hDgen (σ : G) (υ : G) g hA).1 u' hu' hxu' lb ℓ hℓ
    have hfun : (fun c' : Subgroup.centralizer (Subgroup.zpowers (u' : G) : Set G) =>
        lamN c') = fun c' => (lam (Subgroup.inclusion
          (FlatTwistedBases.centralizer_zpowers_le_involutionCentralizer S e hxu') c') : ℂ) := by
      funext c'
      rw [hlamN c' (hle c'.2)]
      rfl
    rw [← hfun] at hdata
    obtain ⟨-, h2, h3⟩ := FlatSquareRoot.singleton_section_column basis ideal B hr1 hr hgroup
      lamN hlam1 hlocal lb ℓ hℓN ((2 ^ n) ^ 2) hdata
    refine generic_columns_of_section hA hn basis ideal B hu' hconj ?_ h3
    rw [h2]
    push_cast
    rfl
  have hm2 : 2 ∣ m := ⟨2 ^ (n - 1), by
    simp only [m]
    rw [← pow_succ']
    congr 1
    omega⟩
  have hZZ : ∀ k ∈ Finset.Ico 1 m, ∀ l ∈ Finset.Ico 1 m,
      ∑ χ ∈ BB, (v χ k 0 + 2 * v χ k 1) * conj (v χ l 0 + 2 * v χ l 1) =
        if k = l then 2 * (m : ℂ) ^ 2 else 0 := fun k hk l hl =>
    (central_combination_gram BB hm2 v hvgram hk hl).1
  have hZX : ∀ k ∈ Finset.Ico 1 m, ∀ l ∈ Finset.Ico 1 m,
      ∑ χ ∈ BB, (v χ k 0 + 2 * v χ k 1) * conj (v χ l 0) = 0 := fun k hk l hl =>
    (central_combination_gram BB hm2 v hvgram hk hl).2
  have hWv : ∀ u ∈ P, ∀ k ∈ Finset.Ico 1 m, ∀ ℓ : Fin 2,
      ∑ χ ∈ BB, χres χ u * conj (v χ k ℓ) = 0 := by
    intro u hu k hk ℓ
    exact twisted_rows_orthogonal_of_section basis ideal B a m
      (fun k => centralSylowPowerCentralizer n S e k) lamN ΦN hΦreal ε hlam0 hindep v hv
      (fun χ => χres χ u) hk (fun r hr hrodd => (hgenc u (hPne u hu)).2.1 k r
        (by rw [← hCk]; exact hr) hrodd) ℓ
  have hZW : ∀ k ∈ Finset.Ico 1 m, ∀ u ∈ P,
      ∑ χ ∈ BB, (v χ k 0 + 2 * v χ k 1) * conj (χres χ u) = 0 := by
    intro k hk u hu
    have h0 := hWv u hu k hk 0
    have h1 := hWv u hu k hk 1
    have h : conj (∑ χ ∈ BB, χres χ u * conj (v χ k 0 + 2 * v χ k 1)) = 0 := by
      rw [show ∑ χ ∈ BB, χres χ u * conj (v χ k 0 + 2 * v χ k 1) =
          ∑ χ ∈ BB, χres χ u * conj (v χ k 0) + 2 * ∑ χ ∈ BB, χres χ u * conj (v χ k 1) by
        rw [Finset.mul_sum, ← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun χ _ => ?_
        rw [map_add, map_mul, map_ofNat]
        ring, h0, h1]
      simp
    rw [map_sum] at h
    rw [← h]
    refine Finset.sum_congr rfl fun χ _ => ?_
    rw [map_mul, Complex.conj_conj, mul_comm]
  have hWW : ∀ u ∈ P, ∀ u' ∈ P, ∑ χ ∈ BB, χres χ u * conj (χres χ u') =
      if ∃ k, h6 k u = u' then (m : ℂ) ^ 2 else 0 := by
    intro u hu u' _
    rw [(hgenc u (hPne u hu)).1 u']
    by_cases hcj : IsConj (u : G) (u' : G)
    · rw [ite_eq_left hcj, ite_eq_left ((isConj_iff_exists_sixAut hA hn u u').mp hcj)]
    · rw [ite_eq_right hcj, ite_eq_right (mt (isConj_iff_exists_sixAut hA hn u u').mpr hcj)]
  have hgram := gram_of_normalized_columns hc hgen hσ hυ hint hζ lamU hlamU h6 h6σ h6υ P hsplit
    hPmem hPinj BB (fun χ k => v χ k 0 + 2 * v χ k 1) χres hZZ hZW
    (fun u hu u' hu' => by convert hWW u hu u' hu' using 2) c hnorm
  have hfourier_orth : ∀ (T' : basis.index → ℂ),
      (∀ h ∈ Finset.Ico 1 m, ∑ χ ∈ BB, T' χ * conj (v χ h 0) = 0) → ∀ j : ZMod m,
      ∑ χ ∈ BB, T' χ * conj (X j χ) = 0 := by
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
      ∑ χ ∈ BB, (v χ k 0 + 2 * v χ k 1) * conj ((basis.representation χ).character z) = 0 := by
    intro k hk z hz
    rw [Finset.sum_congr rfl fun χ _ => add_mul _ _ _, Finset.sum_add_distrib,
      Finset.sum_congr rfl fun χ _ => mul_assoc 2 (v χ k 1) _, ← Finset.mul_sum,
      hvodd k hk 0 z hz, hvodd k hk 1 z hz, mul_zero, add_zero]
  obtain ⟨Fc, hFc, hFcY, hFcpar, -⟩ := hYrows v hv
  have hYZ : ∀ k ∈ Finset.Ico 1 m, ∀ r < M,
      ∑ χ ∈ BB, (v χ k 0 + 2 * v χ k 1) * conj ((Y r χ : ℤ) : ℂ) = 0 := by
    intro k hk r hr
    have hexp : ∀ χ ∈ BB, (v χ k 0 + 2 * v χ k 1) * conj ((Y r χ : ℤ) : ℂ) =
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
    have h0 : ∑ χ ∈ BB, Y r χ * Fc χ j 0 = 0 := hFcY r hr j hj 0
    have h1 : ∑ χ ∈ BB, Y r χ * Fc χ j 1 = 0 := hFcY r hr j hj 1
    have hc0 : ∑ χ ∈ BB, ((Y r χ * Fc χ j 0 : ℤ) : ℂ) = 0 := by
      rw [← Int.cast_sum, h0, Int.cast_zero]
    have hc1 : ∑ χ ∈ BB, ((Y r χ * Fc χ j 1 : ℤ) : ℂ) = 0 := by
      rw [← Int.cast_sum, h1, Int.cast_zero]
    rw [hc0, hc1, mul_zero, add_zero, mul_zero]
  have hnat : ∀ i j χ, ∃ k : ℕ, tm i j χ = k := fun i j χ =>
    restriction_linear_pairing_nat basis (modelBase S e) (lamU i j) χ
  have hcint : ∀ i j, ∀ χ ∈ BB, ∃ z : ℤ, c i j χ = z := by
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
    exact baseColumn_symm hc hgen hζ lamU hlamU h6 h6σ h6υ (χres χ) (hχconj χ) (v χ) q₀ i j
  have hhalf : ∀ x : ZMod m, x ≠ 0 → (x, x) ≠ ((0 : ZMod m), (0 : ZMod m)) := fun x hx h =>
    hx (Prod.ext_iff.mp h).1
  have hne6 : ∀ I : ZMod m × ZMod m, (MulAction.orbit K I).ncard = 6 → I ≠ 0 := by
    intro I hI h0
    rw [h0, show (0 : ZMod m × ZMod m) = ((0 : ZMod m), (0 : ZMod m)) from rfl, orbit_zero,
      Set.ncard_singleton] at hI
    omega
  refine ⟨hnat, hcint, fun χ => by rw [hcbase]; exact baseColumn_zero lamU (χres χ) (v χ) q₀,
    hcsym, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
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
    exact column_orthogonal BB P (fun χ k => v χ k 0 + 2 * v χ k 1) χres (c i j) _ _
      (hnorm i j) (X j') (fun k hk => hfourier_orth _ (hZX k hk) j')
      (fun x hx => hfourier_orth _ (fun h hh => hWv x hx h hh 0) j')
  ·
    intro i j r hr
    have h := column_orthogonal BB P (fun χ k => v χ k 0 + 2 * v χ k 1) χres (c i j) _ _
      (hnorm i j) (fun χ => ((Y r χ : ℤ) : ℂ)) (fun k hk => hYZ k hk r hr) (fun x hx => by
        have hW := column_orthogonal_signed_even basis BB (fun χ => χres χ x) y ζ M
          (fun χ r => Y r χ) (fun h' hh' => (hgenc x (hPne x hx)).2.2.1 y hyord h' hh')
          hYinv hr
        rw [← hW]
        refine Finset.sum_congr rfl fun χ _ => ?_
        rw [map_intCast])
    rw [← h]
    refine Finset.sum_congr rfl fun χ _ => ?_
    rw [map_intCast]
  ·
    intro i j z hz
    exact column_orthogonal BB P (fun χ k => v χ k 0 + 2 * v χ k 1) χres (c i j) _ _
      (hnorm i j) (fun χ => (basis.representation χ).character z) (fun k hk => hoddZ k hk z hz)
      (fun x hx => (hgenc x (hPne x hx)).2.2.2 z hz)
  ·
    intro i j
    have h := column_orthogonal BB P (fun χ k => v χ k 0 + 2 * v χ k 1) χres (c i j) _ _
      (hnorm i j) (fun χ => (basis.representation χ).character 1)
      (fun k hk => hoddZ k hk 1 (by rw [orderOf_one]; exact odd_one))
      (fun x hx => (hgenc x (hPne x hx)).2.2.2 1 (by rw [orderOf_one]; exact odd_one))
    rw [← h]
    refine Finset.sum_congr rfl fun χ _ => ?_
    rw [FiniteComplexRepresentation.character, Representation.char_one, Complex.conj_natCast]
  ·
    intro j χ hχ
    rw [hClbase, hClbase]
    exact second_row_identity hc hgen hσ hυ hint hζ hlamU (χres χ) (v χ) q₀ (hval χ hχ) j
  ·
    intro χ hχ k hk
    have h := second_row_reconstruction hc hgen hσ hυ hint hζ hlamU (χres χ) (v χ) q₀
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
    have h := two_mul_row_value hc hgen hσ hυ hint hζ hlamU (χres χ) (v χ) q₀ (hval χ hχ) hk
      (ε * ΦN z) _ rfl
    rw [hw, show 2 * (lamN z * (v χ k 0 + v χ k 1 * (1 + ε * ΦN z))) =
      lamN z * (2 * (v χ k 0 + v χ k 1 * (1 + ↑ε * ΦN z))) by ring, h]
    congr 3
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [hClbase, hClbase]
  ·
    intro j hj hjodd χ hχ
    have hpar := base_column_parity hc hgen hσ hυ hint hζ hlamU (χres χ) (v χ) q₀ (hval χ hχ)
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
    have hpar := base_column_parity hc hgen hσ hυ hint hζ hlamU (χres χ) (v χ) q₀ (hval χ hχ)
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
    have hpar := base_column_parity hc hgen hσ hυ hint hζ hlamU (χres χ) (v χ) q₀ (hval χ hχ)
      ⟨2 ^ (n - 1), by
        simp only [m]
        rw [← two_mul, ← pow_succ']
        congr 1
        omega⟩
      (fun i j => by rw [← hcbase]; exact hcint i j χ hχ)
      (fun i j => by rw [← hcbase, ← hcbase]; exact (hcsym i j χ).1)
      (fun j => hFint χ hχ 1 j) (fun j => hFint χ hχ 0 j)
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

end CFSG.Wreathed.FlatBase

namespace CFSG.Wreathed

open CFSG.TwoRankLowerBound.Helpers CFSG.Semidihedral.Principal
  CFSG.ComponentClassification.CatalogueSchreierLinearTwo
  CFSG.Semidihedral.SemilinearOddExtensions CFSG.Wreathed.ActualProjectiveLayer
  CFSG.Wreathed.FullDefectLabels CFSG.Wreathed.ConditionalFourier
  CFSG.Wreathed.FlatCentralFourier CFSG.Wreathed.AdaptedBaseFusion
  CFSG.Wreathed.ConditionalGeneralBase

theorem conditional_flat_base_columns_and_second_row_reconstruction
    {G : Type} [Group G]
    [Fintype G] [IsSimpleGroup G] (hnonab : ∃ a b : G, a * b ≠ b * a) (n : ℕ) (hn : 2 ≤ n)
    (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n))
    (hfour : ¬ Nonempty (centralizerFullQuotient n hn S e ≃* Equiv.Perm (Fin 4)))
    (p f : ℕ) (hp : p.Prime) (hpodd : p ≠ 2) (hf : 1 ≤ f)
    (hmodel : PSLTwoClassicalModel (centralizerSimpleLayer n hn S e) p f)
    (ideal : Ideal ComplexAlgebraicIntegers) [ideal.IsMaximal]
    [CharP (ComplexAlgebraicIntegers ⧸ ideal) 2] (basis : FiniteIrreducibleCharacterBasis G)
    (B : basis.index) (hflat : FlatWreathedBlock basis ideal S e B)
    (eb : FiniteIrreducibleCharacterBasis (BaseFourCentralizerStructure.ambientOddCore
      (Subgroup.centralizer ((S : Subgroup G) : Set G)))) (θB : eb.index)
    (nb : FiniteIrreducibleCharacterBasis (Subgroup.normalizer ((S : Subgroup G) : Set G)))
    (θhat : nb.index) (hθ : InflatedLabel (oddCore_le_normalizer S) nb eb θB θhat)
    (hB : brauerNormalizerCharacterResidueHom ideal 2 (S : Subgroup G) S.isPGroup'
        (Subgroup.normalizer ((S : Subgroup G) : Set G)) (Subgroup.centralizer_le_normalizer _)
        le_rfl nb θhat = centralCharacterResidueHom basis ideal B)
    (η : G) (hη : η ∈ Subgroup.normalizer (modelBase S e : Set G))
    (hord : orderOf ((modelBase S e).normalizerMonoidHom ⟨η, hη⟩) = 3) :
    let N : Subgroup G := involutionCentralizer n S e
    let E : Subgroup G := BaseFourCentralizerStructure.ambientOddCore
      (Subgroup.centralizer ((S : Subgroup G) : Set G))
    let T : Subgroup G := Subgroup.closure {wreathModelHom S e (Original.s (2 ^ n)) ^ (2 ^ n / 2),
      wreathModelHom S e (Original.t (2 ^ n)) ^ (2 ^ n / 2)}
    let IsExtension : (N →* ℂˣ) → Prop := fun lam =>
      (∀ (v : N) (z : E), (v : G) = z → (lam v : ℂ) = (eb.representation θB).character z) ∧
      (∀ v : N, (v : G) ∈ (S : Subgroup G) → lam v = 1) ∧
      ∀ c c' : N, (c : G) ∈ Subgroup.centralizer (T : Set G) → (c' : G) = η⁻¹ * c * η →
        lam c' = lam c
    (∃ (F : Type) (_ : Field F) (_ : Finite F) (sigmaGroup : Subgroup (F ≃+* F))
        (ρ : centralizerFullQuotient n hn S e →* coordinateE F),
      Nat.card F = p ^ f ∧ Odd (Nat.card sigmaGroup) ∧ Function.Injective ρ ∧
        (centralizerSimpleLayer n hn S e).map ρ = specialLayer F ∧
        ρ.range = CFSG.Semidihedral.OddFieldLift.Gamma F sigmaGroup) ∧
    (∃ lam, IsExtension lam) ∧
    ∀ lam, IsExtension lam →
    ∀ (F : Type) [Field F] [Finite F] (sigmaGroup : Subgroup (F ≃+* F))
      (ρ : centralizerFullQuotient n hn S e →* coordinateE F),
      Nat.card F = p ^ f → Odd (Nat.card sigmaGroup) → Function.Injective ρ →
      (centralizerSimpleLayer n hn S e).map ρ = specialLayer F →
      ρ.range = CFSG.Semidihedral.OddFieldLift.Gamma F sigmaGroup →
      let m : ℕ := 2 ^ n
      let M : ℕ := m / 2
      let s : G := wreathModelHom S e (Original.s m)
      let t : G := wreathModelHom S e (Original.t m)
      let w : G := wreathModelHom S e (Original.z m)
      let a : G := wreathModelHom S e (Original.a m)
      let y : G := wreathModelHom S e (Original.s m * Original.z m)
      let U : Subgroup G := Subgroup.closure {s, t}
      let ΦH : centralizerOddCoreQuotient n S e → ℂ := fun h =>
        (Nat.card {ω : Omega F // ((ρ (centralizerFullQuotientMap n hn S e h) : coordinateE F) :
          Equiv.Perm (Omega F)) ω = ω} : ℂ) - 1
      let ΦN : G → ℂ := fun g => if hg : g ∈ N then
        ΦH (centralizerOddCoreMap n S e ⟨g, hg⟩) else 0
      let lamN : G → ℂ := fun g => if hg : g ∈ N then (lam ⟨g, hg⟩ : ℂ) else 0
      let ε : ℤ := if Nat.card F % 4 = 1 then 1 else -1
      let q : ℕ := Nat.card F
      let q₀ : ℤ := (ε * q - 1) / m
      let BB := coefficientBlock basis (localizedComplexIntegerRing ideal) B
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
      (∃ v : basis.index → ℕ → Fin 2 → ℂ, IsTwistedCentralSectionRows basis ideal B a m
        (fun k => centralSylowPowerCentralizer n S e k) lamN ΦN ε v) ∧
      ∀ v : basis.index → ℕ → Fin 2 → ℂ, IsTwistedCentralSectionRows basis ideal B a m
        (fun k => centralSylowPowerCentralizer n S e k) lamN ΦN ε v →
      let X : ZMod m → basis.index → ℂ := fun j χ =>
        fourierTransform m ζ (fun k => v χ k 0) j.val
      let Fs : ZMod m → basis.index → ℂ := fun j χ =>
        fourierTransform m ζ (fun k => v χ k 1) j.val
      ∀ (σ υ : U) (g : G), IsAdaptedBase U a w σ υ g →
      (∃ lamU : ZMod m → ZMod m → U →* ℂ,
        ∀ i j, lamU i j σ = ζ ^ i.val ∧ lamU i j υ = ζ ^ j.val) ∧
      ∀ lamU : ZMod m → ZMod m → U →* ℂ,
        (∀ i j, lamU i j σ = ζ ^ i.val ∧ lamU i j υ = ζ ^ j.val) →
      let tm : ZMod m → ZMod m → basis.index → ℂ := fun i j χ =>
        (Nat.card U : ℂ)⁻¹ * ∑ u : U, (basis.representation χ).character u * conj (lamU i j u)
      let c : ZMod m → ZMod m → basis.index → ℂ := fun i j χ =>
        tm 0 0 χ - tm i j χ + q₀ * (Fs i χ + Fs j χ + Fs (-i - j) χ)
      let Cl : ZMod m → basis.index → ℂ := fun l χ => ∑ i : ZMod m, c i (l - i) χ
      (∀ i j χ, ∃ k : ℕ, tm i j χ = k) ∧
      (∀ i j, ∀ χ ∈ BB, ∃ z : ℤ, c i j χ = z) ∧
      (∀ χ, c 0 0 χ = 0) ∧
      (∀ i j χ, c i j χ = c j i χ ∧ c i j χ = c j (-i - j) χ) ∧
      (∀ V : Finset (ZMod m × ZMod m), (∀ I ∈ V, (MulAction.orbit K I).ncard = 6) →
        (∀ I, (MulAction.orbit K I).ncard = 6 → ∃! J, J ∈ V ∧ J ∈ MulAction.orbit K I) →
        (∀ r : ZMod m, r ≠ 0 → ∑ χ ∈ BB, c r r χ * conj (c r r χ) = 8) ∧
        (∀ I ∈ V, ∑ χ ∈ BB, c I.1 I.2 χ * conj (c I.1 I.2 χ) = 7) ∧
        (∀ r r' : ZMod m, r ≠ 0 → r' ≠ 0 → r ≠ r' →
          ∑ χ ∈ BB, c r r χ * conj (c r' r' χ) = 6) ∧
        (∀ r : ZMod m, r ≠ 0 → ∀ I ∈ V,
          ∑ χ ∈ BB, c r r χ * conj (c I.1 I.2 χ) = 6 ∧
            ∑ χ ∈ BB, c I.1 I.2 χ * conj (c r r χ) = 6) ∧
        ∀ I ∈ V, ∀ J ∈ V, I ≠ J → ∑ χ ∈ BB, c I.1 I.2 χ * conj (c J.1 J.2 χ) = 6) ∧
      (∀ i j, ∀ j' ∈ Finset.Ico 1 m, ∑ χ ∈ BB, c i j χ * conj (X j' χ) = 0) ∧
      (∀ i j, ∀ r < M, ∑ χ ∈ BB, c i j χ * (Y r χ : ℂ) = 0) ∧
      (∀ i j, ∀ z : G, Odd (orderOf z) →
        ∑ χ ∈ BB, c i j χ * conj ((basis.representation χ).character z) = 0) ∧
      (∀ i j, ∑ χ ∈ BB, c i j χ * (basis.representation χ).character 1 = 0) ∧
      (∀ j : ZMod m, ∀ χ ∈ BB, X j χ + 2 * Fs j χ = Cl 0 χ - Cl (-j) χ) ∧
      (∀ χ ∈ BB, ∀ k ∈ Finset.Ico 1 m, v χ k 1 = (1 / 2) * ∑ j ∈ Finset.Ico 1 m,
        ζ ^ (-((j : ℤ) * k)) * (Cl 0 χ - Cl (-(j : ZMod m)) χ - X j χ)) ∧
      (∀ χ ∈ BB, ∀ k ∈ Finset.Ico 1 m, ∀ z ∈ Subgroup.centralizer {a ^ k}, Odd (orderOf z) →
        2 * (basis.representation χ).character (a ^ k * z) =
          lamN z * ((1 - ε * ΦN z) * ∑ j ∈ Finset.Ico 1 m, ζ ^ (-((j : ℤ) * k)) * X j χ +
            (1 + ε * ΦN z) * ∑ j ∈ Finset.Ico 1 m,
              ζ ^ (-((j : ℤ) * k)) * (Cl 0 χ - Cl (-(j : ZMod m)) χ))) ∧
      (∀ j ∈ Finset.Ico 1 m, Odd j → ∀ χ ∈ BB, ∃ k : ℤ, X j χ - c M M χ = 2 * k) ∧
      (∀ j ∈ Finset.Ico 1 m, Even j → ∀ r : ZMod m, 2 * r = -(j : ZMod m) → ∀ χ ∈ BB,
        ∃ k : ℤ, X j χ - (c M M χ + c r r χ + c (r + M) (r + M) χ) = 2 * k) ∧
      (∀ χ ∈ BB, ∃ k : ℤ, c M M χ - Y 0 χ = 2 * k) := by
  intro N E T IsExtension
  obtain ⟨hex, hlamex, -⟩ := conditional_flat_local_twisted_regular_bases hnonab n hn S e hfour
    p f hp hpodd hf hmodel ideal basis B hflat eb θB nb θhat hθ hB η hη hord
  refine ⟨hex, hlamex, ?_⟩
  intro lam hlam F _ _ sigmaGroup ρ hcard hodd hρ hlayer hrange
  have hU : Subgroup.closure {wreathModelHom S e (Original.s (2 ^ n)),
      wreathModelHom S e (Original.t (2 ^ n))} = modelBase S e := by
    rw [modelBase, ← Original.U_eq, Original.U, MonoidHom.map_closure, Set.image_pair]
  exact FlatBase.flat_base_core hnonab n hn S e hfour p f hp hpodd hf hmodel ideal basis B hflat
    eb θB nb θhat hθ hB η hη hord lam hlam F sigmaGroup ρ hcard hodd hρ hlayer hrange _ hU

end CFSG.Wreathed

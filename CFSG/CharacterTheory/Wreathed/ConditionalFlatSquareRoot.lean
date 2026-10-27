module

public import CFSG.CharacterTheory.Wreathed.ConditionalFlatSquareRootRows
public import CFSG.CharacterTheory.Wreathed.ConditionalFlatCentralFourier
public import CFSG.CharacterTheory.Wreathed.ConditionalSquareRoot
public import CFSG.CharacterTheory.Wreathed.ConditionalFlatSquareRootColumns

public section

open scoped BigOperators Classical ComplexConjugate

namespace CFSG.Wreathed

open CFSG.TwoRankLowerBound.Helpers CFSG.Semidihedral.Principal
  CFSG.ComponentClassification.CatalogueSchreierLinearTwo
  CFSG.Semidihedral.SemilinearOddExtensions CFSG.Wreathed.ActualProjectiveLayer
  CFSG.Wreathed.FullDefectLabels CFSG.Wreathed.ConditionalFourier
  CFSG.Wreathed.FlatCentralFourier CFSG.Wreathed.FlatSquareRoot
  CFSG.Wreathed.ConditionalSquareRoot CFSG.Wreathed.WreathCentralSquare
  CFSG.Wreathed.SquareRootSmallCharacterRigidity

theorem conditional_flat_square_root_columns_and_parity
    {G : Type} [Group G] [Fintype G]
    [IsSimpleGroup G] (hnonab : ∃ a b : G, a * b ≠ b * a) (n : ℕ) (hn : 2 ≤ n)
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
      let M₀ : ℕ := m / 2
      let a : G := wreathModelHom S e (Original.a (2 ^ n))
      let x : G := wreathModelHom S e (Original.x (2 ^ n))
      let y : G := wreathModelHom S e (Original.s (2 ^ n) * Original.z (2 ^ n))
      let D : Subgroup G := Subgroup.centralizer ({y} : Set G)
      let ΦH : centralizerOddCoreQuotient n S e → ℂ := fun h =>
        (Nat.card {ω : Omega F // ((ρ (centralizerFullQuotientMap n hn S e h) : coordinateE F) :
          Equiv.Perm (Omega F)) ω = ω} : ℂ) - 1
      let ΦN : G → ℂ := fun g => if hg : g ∈ N then
        ΦH (centralizerOddCoreMap n S e ⟨g, hg⟩) else 0
      let lamN : G → ℂ := fun g => if hg : g ∈ N then (lam ⟨g, hg⟩ : ℂ) else 0
      let ε : ℤ := if Nat.card F % 4 = 1 then 1 else -1
      let BB := coefficientBlock basis (localizedComplexIntegerRing ideal) B
      orderOf y = 2 * m ∧ y ^ 2 = a ∧ y ^ m = x ∧
      (∃ Ey : CFSG.oddCore D × Subgroup.zpowers y ≃* D,
        ∀ k z, (Ey (k, z) : G) = ((k : D) : G) * (z : G)) ∧
      (∀ h t : ℤ, Odd h → Odd t → (IsConj (y ^ h) (y ^ t) ↔ h ≡ t [ZMOD m])) ∧
      ∀ ζ : ℂ, IsPrimitiveRoot ζ m → ∀ θ : ℂ, IsPrimitiveRoot θ (2 * m) → θ ^ 2 = ζ →
        let ν : basis.index → ℕ → ℕ := fun χ t =>
          Module.finrank ℂ (Module.End.eigenspace ((basis.representation χ).representation y)
            (θ ^ t))
        let Y : basis.index → ℕ → ℤ := fun χ r => (ν χ (2 * r) : ℤ) - ν χ (2 * r + m)
        (∀ χ ∈ BB, ∀ h : ℤ, Odd h → ∀ z ∈ D, Odd (orderOf z) →
          (basis.representation χ).character (y ^ h * z) =
              lamN z * (basis.representation χ).character (y ^ h) ∧
            (basis.representation χ).character (y ^ h) =
              ∑ r ∈ Finset.range M₀, (Y χ r : ℂ) * ζ ^ ((r : ℤ) * h)) ∧
        (∀ χ ∈ BB, ∀ r < M₀, (Y χ r : ℂ) = (M₀ : ℂ)⁻¹ * ∑ i ∈ Finset.range M₀,
          (basis.representation χ).character (y ^ (2 * i + 1)) *
            ζ ^ (-((r : ℤ) * (2 * i + 1)))) ∧
        (∀ r < M₀, ∀ t < M₀, ∑ χ ∈ BB, Y χ r * Y χ t = if r = t then 4 else 0) ∧
        (∀ r < M₀, ∀ z : G, Odd (orderOf z) →
          ∑ χ ∈ BB, (Y χ r : ℂ) * conj ((basis.representation χ).character z) = 0) ∧
        (∀ r < M₀, ∑ χ ∈ BB, (Y χ r : ℂ) * (basis.representation χ).character 1 = 0) ∧
        (∀ r < M₀, (BB.filter (fun χ => Y χ r ≠ 0)).card = 4 ∧
          ∀ χ ∈ BB, Y χ r = 0 ∨ Y χ r = 1 ∨ Y χ r = -1) ∧
        (∃ v : basis.index → ℕ → Fin 2 → ℂ, IsTwistedCentralSectionRows basis ideal B a m
          (fun k => centralSylowPowerCentralizer n S e k) lamN ΦN ε v) ∧
        ∀ v : basis.index → ℕ → Fin 2 → ℂ, IsTwistedCentralSectionRows basis ideal B a m
          (fun k => centralSylowPowerCentralizer n S e k) lamN ΦN ε v →
        ∃ Fc : basis.index → ℕ → Fin 2 → ℤ,
          (∀ χ ∈ BB, ∀ j ∈ Finset.Ico 1 m, ∀ ℓ,
            (Fc χ j ℓ : ℂ) = fourierTransform m ζ (fun k => v χ k ℓ) j) ∧
          (∀ r < M₀, ∀ j ∈ Finset.Ico 1 m, ∀ ℓ, ∑ χ ∈ BB, Y χ r * Fc χ j ℓ = 0) ∧
          (∀ j ∈ Finset.Ico 1 m, Odd j → ∀ χ ∈ BB, Fc χ j 0 ≡ Y χ 0 [ZMOD 2]) ∧
          (∀ j ∈ Finset.Ico 1 m, Even j → ∀ r, 1 ≤ r → r < M₀ → (r + j / 2) % M₀ = 0 →
            ∀ χ ∈ BB, Fc χ j 0 ≡ Y χ 0 + Y χ r [ZMOD 2]) ∧
          (∀ j ∈ Finset.Ico 1 m, Odd j →
            (Finset.Ico 1 m).filter (fun j' => ∀ χ ∈ BB, Fc χ j' 0 ≡ Fc χ j 0 [ZMOD 2]) =
              (Finset.Ico 1 m).filter Odd) ∧
          ((Finset.Ico 1 m).filter Odd).card = M₀ ∧
          (∀ j ∈ Finset.Ico 1 m, Even j → ∀ j' ∈ Finset.Ico 1 m, Even j' →
            ∀ r, 1 ≤ r → r < M₀ → (r + j / 2) % M₀ = 0 →
            ∀ r', 1 ≤ r' → r' < M₀ → (r' + j' / 2) % M₀ = 0 →
            ((∀ χ ∈ BB, Fc χ j 0 ≡ Fc χ j' 0 [ZMOD 2]) ↔
              BB.filter (fun χ => Y χ r ≠ 0) = BB.filter (fun χ => Y χ r' ≠ 0))) ∧
          ∀ j ∈ Finset.Ico 1 m, Even j →
            ((Finset.Ico 1 m).filter
              (fun j' => ∀ χ ∈ BB, Fc χ j' 0 ≡ Fc χ j 0 [ZMOD 2])).card ≤ 3 := by
  intro N E T IsExtension
  obtain ⟨hex, hlamex, hall⟩ := conditional_flat_local_twisted_regular_bases hnonab n hn S e hfour
    p f hp hpodd hf hmodel ideal basis B hflat eb θB nb θhat hθ hB η hη hord
  have hcentral := conditional_flat_central_section_integral_fourier_columns hnonab n hn S e
    hfour p f hp hpodd hf hmodel ideal basis B hflat eb θB nb θhat hθ hB η hη hord
  refine ⟨hex, hlamex, ?_⟩
  intro lam hlam F _ _ sigmaGroup ρ hcard hodd hρ hlayer hrange m M₀ a x y D ΦH ΦN lamN ε BB
  obtain ⟨hA, -, hCroot, -⟩ := hall lam hlam
  obtain ⟨hyord, hysq, hym, -, -, hE, hcent, hroot⟩ := hCroot
  have hm4 : 4 ≤ m := by
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  have hm2 : 2 * M₀ = m := by
    obtain ⟨k, hk⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
    simp only [M₀, m]
    rw [hk, pow_succ, Nat.mul_div_cancel _ (by norm_num), mul_comm]
  refine ⟨hyord, hysq, hym, hE, fun h t hh ht => actualRoot_odd_zpow_isConj_iff n hn S e hh ht,
    ?_⟩
  intro ζ hζ θ hθ hθζ ν Y
  have hYdef : ∀ χ r, Y χ r =
      signedEvenEigenmultiplicity (basis.representation χ) (actualRoot S e) θ (2 ^ n) r :=
    fun _ _ => rfl
  have hνdef : ∀ χ t, ν χ t =
      cyclicEigenmultiplicity (basis.representation χ) (actualRoot S e) θ t := fun _ _ => rfl
  have hlamN : ∀ (g : G) (hg : g ∈ N), lamN g = lam ⟨g, hg⟩ := fun g hg => dite_eq_left hg
  have hΦN : ∀ (g : G) (hg : g ∈ N), ΦN g = ΦH (centralizerOddCoreMap n S e ⟨g, hg⟩) :=
    fun g hg => dite_eq_left hg
  have hlam1 : lamN 1 = 1 := by
    rw [hlamN 1 N.one_mem]
    have h1 : (⟨1, N.one_mem⟩ : N) = 1 := rfl
    rw [h1, map_one, Units.val_one]
  have hcent' : ∀ h : ℤ, Odd h → Subgroup.centralizer ({actualRoot S e ^ h} : Set G) =
      Subgroup.centralizer ({actualRoot S e} : Set G) := fun h hh => hcent h hh
  have hy2 : orderOf (actualRoot S e) = 2 ^ (n + 1) := by
    rw [actualRoot_orderOf n hn S e, pow_succ, mul_comm]
  have hsec : ∀ h : ℤ, Odd h →
      (∀ χ ∈ BB, ∀ z ∈ Subgroup.centralizer ({actualRoot S e} : Set G), Odd (orderOf z) →
          (basis.representation χ).character (actualRoot S e ^ h * z) =
            lamN z * (basis.representation χ).character (actualRoot S e ^ h)) ∧
      (∑ χ ∈ BB, (basis.representation χ).character (actualRoot S e ^ h) *
          conj ((basis.representation χ).character (actualRoot S e ^ h)) = 2 * 2 ^ n) ∧
      ∀ g : G, (∀ a c : G, a * c = g → Commute a c → (∃ e : ℕ, orderOf a = 2 ^ e) →
          Odd (orderOf c) → ¬ IsConj a (actualRoot S e ^ h)) →
        ∑ χ ∈ BB, (basis.representation χ).character (actualRoot S e ^ h) *
          conj ((basis.representation χ).character g) = 0 := by
    intro h hh
    have hyh : orderOf (actualRoot S e ^ h) = 2 ^ (n + 1) := orderOf_odd_power hy2 hh
    have hgroup : IsPGroup 2 (Subgroup.zpowers (actualRoot S e ^ h)) :=
      IsPGroup.of_card (by rw [Nat.card_zpowers, hyh])
    have hxu := FlatTwistedBases.root_zpow_involution S e hn hh
    obtain ⟨-, hle, hloc⟩ := hA (actualRoot S e ^ h) hgroup hxu
    have hlocal : ∀ (lb : FiniteIrreducibleCharacterBasis
        (Subgroup.centralizer (Subgroup.zpowers (actualRoot S e ^ h) : Set G))) (ℓ : lb.index),
        (∀ c, (lb.representation ℓ).character c = lamN c) →
        brauerNormalizerCharacterResidueHom ideal 2 (Subgroup.zpowers (actualRoot S e ^ h))
            hgroup (Subgroup.centralizer (Subgroup.zpowers (actualRoot S e ^ h) : Set G))
            le_rfl (Subgroup.centralizer_le_normalizer _) lb ℓ =
          centralCharacterResidueHom basis ideal B ∧
        ∀ θ', brauerNormalizerCharacterResidueHom ideal 2
            (Subgroup.zpowers (actualRoot S e ^ h)) hgroup
            (Subgroup.centralizer (Subgroup.zpowers (actualRoot S e ^ h) : Set G)) le_rfl
            (Subgroup.centralizer_le_normalizer _) lb θ' =
          centralCharacterResidueHom basis ideal B →
          θ' ∈ coefficientBlock lb (localizedComplexIntegerRing ideal) ℓ := by
      intro lb ℓ hℓ
      obtain ⟨-, hlb⟩ := hloc lb
      obtain ⟨principal, hprincipal⟩ := finiteIrreducibleCharacterBasis_exists_principal_label lb
      have hℓ' : ∀ c, (lb.representation ℓ).character c =
          lam (Subgroup.inclusion (FlatTwistedBases.centralizer_zpowers_le_involutionCentralizer
            S e hxu) c) := fun c => by
        rw [hℓ, hlamN c (hle c.2)]
        rfl
      obtain ⟨hbrauer, hunique, -⟩ := hlb ℓ principal hℓ' hprincipal
      exact ⟨hbrauer, fun θ' hθ' => (coefficientBlock_mem_iff _ _ _ _).mpr
        (sameCoefficientBlock_symm _ _ (hunique θ' hθ'))⟩
    obtain ⟨lb⟩ := finiteIrreducibleCharacterBasis_exists
      (G := Subgroup.centralizer (Subgroup.zpowers (actualRoot S e ^ h) : Set G))
    obtain ⟨ℓ, hℓ⟩ := CompatibleFamily.exists_linear_label lb (lam.comp (Subgroup.inclusion hle))
    have hℓN : ∀ c, (lb.representation ℓ).character c = lamN c := fun c => by
      rw [hℓ, hlamN c (hle c.2)]
      rfl
    have hdata := hroot h hh lb ℓ hℓ
    have hfun : (fun c : Subgroup.centralizer (Subgroup.zpowers (actualRoot S e ^ h) : Set G) =>
        lamN c) = fun c => (lam (Subgroup.inclusion
          (FlatTwistedBases.centralizer_zpowers_le_involutionCentralizer S e
            (FlatTwistedBases.root_zpow_involution S e hn hh)) c) : ℂ) := by
      funext c
      rw [hlamN c (hle c.2)]
      rfl
    rw [← hfun] at hdata
    obtain ⟨h1, h2, h3⟩ := singleton_section_column basis ideal B (by omega : 1 ≤ n + 1) hyh
      hgroup lamN hlam1 hlocal lb ℓ hℓN (2 * 2 ^ n) hdata
    refine ⟨fun χ hχ z hz hzodd => h1 χ hχ z ?_ hzodd, ?_, h3⟩
    · rw [FlatTwistedBases.centralizer_zpowers_eq_singleton, hcent' h hh]
      exact hz
    · rw [h2]
      push_cast
      rfl
  obtain ⟨hexp, hcgram, hcodd, hfour'⟩ := flat_signed_even_columns n hn S e basis ideal B lamN
    hθ hsec
  have hreal1 : ∀ χ : basis.index, conj ((basis.representation χ).character 1) =
      (basis.representation χ).character 1 := by
    intro χ
    have h1 : (basis.representation χ).character 1 =
        (Module.finrank ℂ (basis.representation χ).vector : ℂ) := Representation.char_one _
    rw [h1, Complex.conj_natCast]
  have hcdeg : ∀ r < M₀, ∑ χ ∈ BB, (Y χ r : ℂ) * (basis.representation χ).character 1 = 0 := by
    intro r hr
    rw [← hcodd r hr 1 (by rw [orderOf_one]; exact odd_one)]
    refine Finset.sum_congr rfl fun χ _ => ?_
    rw [hreal1]
    rfl
  have hdegpos : ∀ χ ∈ BB, 0 < (Module.finrank ℂ (basis.representation χ).vector : ℤ) := by
    intro χ _
    have h := irreducible_character_degree_ne_zero (basis.representation χ) (basis.irreducible χ)
    rw [FiniteComplexRepresentation.character, Representation.char_one] at h
    have h' : Module.finrank ℂ (basis.representation χ).vector ≠ 0 := by exact_mod_cast h
    omega
  have hcdegZ : ∀ r < M₀, ∑ χ ∈ BB,
      Y χ r * (Module.finrank ℂ (basis.representation χ).vector : ℤ) = 0 := by
    intro r hr
    have h := hcdeg r hr
    apply Int.cast_injective (α := ℂ)
    rw [Int.cast_sum, Int.cast_zero, ← h]
    refine Finset.sum_congr rfl fun χ _ => ?_
    rw [Int.cast_mul, Int.cast_natCast, FiniteComplexRepresentation.character,
      Representation.char_one]
  obtain ⟨v₀, -, hv₀row, hv₀uniq, -, -, -, hint₀, -⟩ :=
    hcentral.2.2 lam hlam F sigmaGroup ρ hcard hodd hρ hlayer hrange ζ hζ
  have hkdvd : ∀ k ∈ Finset.Ico 1 m, ¬ ((2 ^ n : ℕ) : ℤ) ∣ (k : ℤ) := by
    intro k hk hd
    rw [Finset.mem_Ico] at hk
    have h1 := Int.le_of_dvd (by omega) hd
    have h2 : 2 ^ n ≤ k := by exact_mod_cast h1
    omega
  have hCk : ∀ k : ℕ, centralSylowPowerCentralizer n S e k = Subgroup.centralizer {a ^ k} := by
    intro k
    simp only [centralSylowPowerCentralizer, zpow_natCast]
    rfl
  have hCkN : ∀ k ∈ Finset.Ico 1 m, centralSylowPowerCentralizer n S e k ≤ N := fun k hk =>
    centralizer_zpow_le_involutionCentralizer n hn S e k (hkdvd k hk)
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
  have hΦ1 : ΦN 1 = Nat.card F := by
    have h := hP₁.degree
    rw [hΦN 1 N.one_mem]
    exact h
  have hC₁k : ∀ k : ℕ, ∀ y ∈ centralSylowPowerCentralizer n S e (1 : ℕ),
      y ∈ centralSylowPowerCentralizer n S e k := by
    intro k y hy
    rw [hCk 1, pow_one, Subgroup.mem_centralizer_singleton_iff] at hy
    rw [hCk k, Subgroup.mem_centralizer_singleton_iff]
    exact ((Commute.pow_left (show Commute a y from hy.symm) k).eq).symm
  have hindep : ∀ k ∈ Finset.Ico 1 m, ∀ α β : ℂ,
      (∀ y ∈ centralSylowPowerCentralizer n S e k, Odd (orderOf y) →
        α + β * (1 + ε * ΦN y) = 0) → α = 0 ∧ β = 0 := by
    intro k _ α β hαβ
    refine eq_zero_of_odd_combination _ ε _ hP₁.degree hP₁.linearIndependent (fun y hy => ?_)
    have h := hαβ y (hC₁k k y y.2) (by rwa [Subgroup.orderOf_coe])
    rw [hΦN y (hCkN 1 h1m y.2)] at h
    exact h
  have hlam0 : ∀ k ∈ Finset.Ico 1 m, ∀ c ∈ centralSylowPowerCentralizer n S e k,
      lamN c ≠ 0 := fun k hk c hc => by
    rw [hlamN c (hCkN k hk hc)]
    exact (lam ⟨c, hCkN k hk hc⟩).ne_zero
  have hΦreal : ∀ g, conj (ΦN g) = ΦN g := by
    intro g
    simp only [ΦN, ΦH]
    split_ifs
    · rw [map_sub, map_one, Complex.conj_natCast]
    · rw [map_zero]
  have hqodd : Odd (Nat.card F) := by
    rw [hcard]
    exact (hp.odd_of_ne_two hpodd).pow
  have hε : ε = 1 ∨ ε = -1 := by
    simp only [ε]
    split_ifs
    · exact Or.inl rfl
    · exact Or.inr rfl
  refine ⟨fun χ hχ h hh z hz hzodd => ?_, ?_, hcgram, hcodd, hcdeg, hfour', ⟨v₀, hv₀row⟩, ?_⟩
  ·
    obtain ⟨h1, h2⟩ := hexp χ hχ h hh z hz hzodd
    refine ⟨h1, ?_⟩
    rw [← hθζ]
    exact h2
  ·
    intro χ _ r _
    rw [hYdef, actualRoot_signed_even_inversion n hn S e (basis.representation χ) hθ r, hθζ]
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [mul_comm, inv_pow, ← zpow_natCast ζ, ← zpow_neg]
    congr 2
  intro v hv
  have hvv₀ : ∀ χ ∈ BB, ∀ k ∈ Finset.Ico 1 m, v χ k = v₀ χ k := fun χ hχ k hk =>
    hv₀uniq χ hχ k hk (v χ k) fun r hr hrodd => hv χ hχ k hk r hr hrodd
  have hint : ∀ χ ∈ BB, ∀ j ∈ Finset.Ico 1 m, ∀ ℓ,
      ∃ z : ℤ, fourierTransform m ζ (fun k => v χ k ℓ) j = z := by
    intro χ hχ j hj ℓ
    obtain ⟨z, hz⟩ := hint₀ χ hχ j hj ℓ
    refine ⟨z, ?_⟩
    rw [fourierTransform_congr (w := fun k => v₀ χ k ℓ) (fun k hk => by rw [hvv₀ χ hχ k hk]) j]
    exact hz
  let Fc : basis.index → ℕ → Fin 2 → ℤ := fun χ j ℓ =>
    if h : χ ∈ BB ∧ j ∈ Finset.Ico 1 m then Classical.choose (hint χ h.1 j h.2 ℓ) else 0
  have hFc : ∀ χ ∈ BB, ∀ j ∈ Finset.Ico 1 m, ∀ ℓ,
      (Fc χ j ℓ : ℂ) = fourierTransform m ζ (fun k => v χ k ℓ) j := by
    intro χ hχ j hj ℓ
    simp only [Fc, dite_eq_left (⟨hχ, hj⟩ : χ ∈ BB ∧ j ∈ Finset.Ico 1 m)]
    exact (Classical.choose_spec (hint χ hχ j hj ℓ)).symm
  have hrow : ∀ ℓ, ∀ i ∈ Finset.range (2 ^ n / 2), ∀ k ∈ Finset.Ico 1 (2 ^ n),
      ∑ χ ∈ BB, (basis.representation χ).character (actualRoot S e ^ (2 * i + 1)) *
        conj (v χ k ℓ) = 0 := by
    intro ℓ i _ k hk
    have hodd' : Odd ((2 * i + 1 : ℕ) : ℤ) := ⟨i, by push_cast; ring⟩
    have h := flat_root_rows_orthogonal n hn S e basis ideal B
      (fun k => centralSylowPowerCentralizer n S e k) hCk lamN ΦN hΦreal ε hlam0 hindep v hv
      hodd' (hsec _ hodd').2.2 hk ℓ
    rwa [zpow_natCast] at h
  have hpar : ∀ χ ∈ BB, ∀ j ∈ Finset.Ico 1 m,
      Fc χ j 0 ≡ (ν χ (m - j) : ℤ) + ν χ (2 * m - j) - ν χ 0 - ν χ m [ZMOD 2] := by
    intro χ hχ j hj
    have h := flat_fourier_rows_at_one_eigen n hn S e basis ideal B
      (fun k => centralSylowPowerCentralizer n S e k) lamN ΦN hlam1 ε (Nat.card F) hΦ1 v hv
      hθ hθζ hχ hj
    rw [← hFc χ hχ j hj 0, ← hFc χ hχ j hj 1] at h
    have h' : (Fc χ j 0 : ℂ) + (1 + (ε : ℂ) * (Nat.card F : ℂ)) * (Fc χ j 1 : ℂ) =
        (((ν χ (m - j) : ℤ) + ν χ (2 * m - j) - ν χ 0 - ν χ m : ℤ) : ℂ) := h
    have hZ : Fc χ j 0 + (1 + ε * (Nat.card F : ℤ)) * Fc χ j 1 =
        (ν χ (m - j) : ℤ) + ν χ (2 * m - j) - ν χ 0 - ν χ m := by
      exact_mod_cast h'
    exact modEq_two_of_add_mul hqodd hε hZ
  have hcancel : ∀ χ, ∀ t, Odd t → ν χ t = ν χ (t + m) := fun χ t ht =>
    actual_root_odd_eigenmultiplicity_cancellation n hn S e (basis.representation χ) θ hθ t ht
  have hc0def : ∀ χ, Y χ 0 = (ν χ 0 : ℤ) - ν χ m := by
    intro χ
    simp only [Y, mul_zero, zero_add]
  have hoddpar : ∀ j ∈ Finset.Ico 1 m, Odd j → ∀ χ ∈ BB, Fc χ j 0 ≡ Y χ 0 [ZMOD 2] := by
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
  have hevenpar : ∀ j ∈ Finset.Ico 1 m, Even j → ∀ χ ∈ BB,
      Fc χ j 0 ≡ Y χ 0 + Y χ (M₀ - j / 2) [ZMOD 2] := by
    intro j hj hje χ hχ
    have hj' := Finset.mem_Ico.mp hj
    have h := hpar χ hχ j hj
    obtain ⟨k, rfl⟩ := hje
    have h1 : 2 * (M₀ - (k + k) / 2) = m - (k + k) := by omega
    have h2 : 2 * (M₀ - (k + k) / 2) + m = 2 * m - (k + k) := by omega
    have hcr : Y χ (M₀ - (k + k) / 2) = (ν χ (m - (k + k)) : ℤ) - ν χ (2 * m - (k + k)) := by
      show (ν χ (2 * (M₀ - (k + k) / 2)) : ℤ) - ν χ (2 * (M₀ - (k + k) / 2) + m) = _
      rw [h2, h1]
    rw [hc0def χ, hcr]
    unfold Int.ModEq at h ⊢
    omega
  rw [← hm2] at hoddpar hevenpar
  obtain ⟨hcls1, hcls2, hcls3, hcls4⟩ := parity_classes BB Y
    (fun χ => (Module.finrank ℂ (basis.representation χ).vector : ℤ)) hdegpos hcgram hcdegZ
    hfour' (fun χ j => Fc χ j 0) hoddpar hevenpar
  rw [hm2] at hcls1 hcls2 hcls3 hcls4 hoddpar hevenpar
  have hrj : ∀ j ∈ Finset.Ico 1 m, Even j → ∀ r, 1 ≤ r → r < M₀ → (r + j / 2) % M₀ = 0 →
      r = M₀ - j / 2 := by
    intro j hj hje r hr1 hrM hmod
    have hj' := Finset.mem_Ico.mp hj
    obtain ⟨k, rfl⟩ := hje
    have := eq_of_mod_eq_zero_of_lt hmod (by omega) (by omega)
    omega
  refine ⟨Fc, hFc, ?_, hoddpar, ?_, fun j hj hjo => by convert hcls1 j hj hjo, hcls2, ?_,
    fun j hj hje => by convert hcls4 j hj hje⟩
  ·
    intro r _ j hj ℓ
    exact flat_signed_even_fourier_orthogonal n S e basis ideal B v hn hθ ζ (fun χ => Fc χ j ℓ) ℓ
      (fun χ hχ => hFc χ hχ j hj ℓ) (hrow ℓ) r
  · intro j hj hje r hr1 hrM hmod χ hχ
    rw [hrj j hj hje r hr1 hrM hmod]
    exact hevenpar j hj hje χ hχ
  · intro j hj hje j' hj' hje' r hr1 hrM hmod r' hr1' hrM' hmod'
    rw [hrj j hj hje r hr1 hrM hmod, hrj j' hj' hje' r' hr1' hrM' hmod']
    exact hcls3 j hj hje j' hj' hje'

end CFSG.Wreathed

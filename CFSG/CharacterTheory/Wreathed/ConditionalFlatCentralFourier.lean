module

public import CFSG.CharacterTheory.Wreathed.ConditionalFlatCentralFourierFamily
public import CFSG.CharacterTheory.Wreathed.ConditionalFlatCentralFourierIntegrality
public import CFSG.CharacterTheory.Wreathed.ConditionalFlatTwistedBases

public section

open scoped BigOperators Classical ComplexConjugate

namespace CFSG.Wreathed

open CFSG.TwoRankLowerBound.Helpers CFSG.Semidihedral.Principal
  CFSG.ComponentClassification.CatalogueSchreierLinearTwo
  CFSG.Semidihedral.SemilinearOddExtensions CFSG.Wreathed.ActualProjectiveLayer
  CFSG.Wreathed.FullDefectLabels CFSG.Wreathed.ConditionalFourier
  CFSG.Wreathed.FlatCentralFourier

theorem conditional_flat_central_section_integral_fourier_columns
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
      let a : G := wreathModelHom S e (Original.a (2 ^ n))
      let ΦH : centralizerOddCoreQuotient n S e → ℂ := fun h =>
        (Nat.card {ω : Omega F // ((ρ (centralizerFullQuotientMap n hn S e h) : coordinateE F) :
          Equiv.Perm (Omega F)) ω = ω} : ℂ) - 1
      let ΦN : G → ℂ := fun g => if hg : g ∈ N then
        ΦH (centralizerOddCoreMap n S e ⟨g, hg⟩) else 0
      let lamN : G → ℂ := fun g => if hg : g ∈ N then (lam ⟨g, hg⟩ : ℂ) else 0
      let ε : ℤ := if Nat.card F % 4 = 1 then 1 else -1
      let Bm : Matrix (Fin 2) (Fin 2) ℤ := !![4, -2; -2, ((m / 2 + 1 : ℕ) : ℤ)]
      let BB := coefficientBlock basis (localizedComplexIntegerRing ideal) B
      ∀ ζ : ℂ, IsPrimitiveRoot ζ m →
      ∃ v : basis.index → ℕ → Fin 2 → ℂ,
        (∀ χ ∈ BB, ∀ k ∈ Finset.Ico 1 m, ∀ ℓ, v χ k ℓ ∈ Algebra.adjoin ℤ ({ζ} : Set ℂ)) ∧
        IsTwistedCentralSectionRows basis ideal B a m
          (fun k => centralSylowPowerCentralizer n S e k) lamN ΦN ε v ∧
        (∀ χ ∈ BB, ∀ k ∈ Finset.Ico 1 m, ∀ w : Fin 2 → ℂ,
          (∀ r ∈ centralSylowPowerCentralizer n S e k, Odd (orderOf r) →
            (basis.representation χ).character (a ^ k * r) =
              lamN r * (w 0 + w 1 * (1 + ε * ΦN r))) → w = v χ k) ∧
        (∀ k ∈ Finset.Ico 1 m, ∀ h ∈ Finset.Ico 1 m, ∀ ℓ t,
          ∑ χ ∈ BB, conj (v χ k ℓ) * v χ h t =
            if k = h then (((m : ℤ) • Bm) ℓ t : ℂ) else 0) ∧
        (∀ k ∈ Finset.Ico 1 m, ∀ ℓ, ∀ z : G, Odd (orderOf z) →
          ∑ χ ∈ BB, v χ k ℓ * conj ((basis.representation χ).character z) = 0) ∧
        (∀ k ∈ Finset.Ico 1 m, ∀ ℓ,
          ∑ χ ∈ BB, (basis.representation χ).character 1 * v χ k ℓ = 0) ∧
        (∀ χ ∈ BB, ∀ j ∈ Finset.Ico 1 m, ∀ ℓ,
          ∃ z : ℤ, fourierTransform m ζ (fun k => v χ k ℓ) j = z) ∧
        (∀ j ∈ Finset.Ico 1 m, ∀ h ∈ Finset.Ico 1 m, ∀ ℓ t,
          ∑ χ ∈ BB, fourierTransform m ζ (fun k => v χ k ℓ) j *
              fourierTransform m ζ (fun k => v χ k t) h =
            ((if j = h then 1 else 0) + 1) * (Bm ℓ t : ℂ)) ∧
        (∀ j ∈ Finset.Ico 1 m, ∀ ℓ, ∀ z : G, Odd (orderOf z) →
          ∑ χ ∈ BB, fourierTransform m ζ (fun k => v χ k ℓ) j *
            conj ((basis.representation χ).character z) = 0) ∧
        (∀ j ∈ Finset.Ico 1 m, ∀ ℓ,
          ∑ χ ∈ BB, (basis.representation χ).character 1 *
            fourierTransform m ζ (fun k => v χ k ℓ) j = 0) ∧
        (∀ χ ∈ BB, ∀ k ∈ Finset.Ico 1 m, ∀ ℓ,
          v χ k ℓ = ∑ j ∈ Finset.Ico 1 m,
            ζ ^ (-((j : ℤ) * k)) * fourierTransform m ζ (fun k => v χ k ℓ) j) ∧
        (∀ j ∈ Finset.Ico 1 m,
          ∑ χ ∈ BB, fourierTransform m ζ (fun k => v χ k 0) j ^ 2 = 8) ∧
        ∀ j ∈ Finset.Ico 1 m, ∀ h ∈ Finset.Ico 1 m, j ≠ h →
          ∑ χ ∈ BB, fourierTransform m ζ (fun k => v χ k 0) j *
            fourierTransform m ζ (fun k => v χ k 0) h = 4 := by
  intro N E T IsExtension
  obtain ⟨hex, hlamex, hall⟩ := conditional_flat_local_twisted_regular_bases hnonab n hn S e hfour
    p f hp hpodd hf hmodel ideal basis B hflat eb θB nb θhat hθ hB η hη hord
  refine ⟨hex, hlamex, ?_⟩
  intro lam hlam F _ _ sigmaGroup ρ hcard hodd hρ hlayer hrange m a ΦH ΦN lamN ε Bm BB ζ hζ
  obtain ⟨hA, hBpart, -, -⟩ := hall lam hlam
  obtain ⟨-, hCdata, -, -⟩ := hBpart F sigmaGroup ρ hcard hodd hρ hlayer hrange
  have hm4 : 4 ≤ m := by
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  have ha : orderOf a = m := orderOf_wreathModelHom_a n S e
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
  have hlamN : ∀ (g : G) (hg : g ∈ N), lamN g = lam ⟨g, hg⟩ := fun g hg => dite_eq_left hg
  have hΦN : ∀ (g : G) (hg : g ∈ N), ΦN g = ΦH (centralizerOddCoreMap n S e ⟨g, hg⟩) :=
    fun g hg => dite_eq_left hg
  have hlam0 : ∀ g ∈ N, lamN g ≠ 0 := fun g hg => by
    rw [hlamN g hg]
    exact (lam ⟨g, hg⟩).ne_zero
  have hCkN : ∀ k ∈ Finset.Ico 1 m, centralSylowPowerCentralizer n S e k ≤ N := fun k hk =>
    centralizer_zpow_le_involutionCentralizer n hn S e k (hkdvd k hk)
  have hΦreal : ∀ g, conj (ΦN g) = ΦN g := by
    intro g
    simp only [ΦN, ΦH]
    split_ifs
    · rw [map_sub, map_one, Complex.conj_natCast]
    · rw [map_zero]
  have hM : (2 ^ n : ℤ) • !![4, -2; -2, ((2 ^ n / 2 + 1 : ℕ) : ℤ)] = (m : ℤ) • Bm := by
    simp only [m, Bm]
    push_cast
    rfl
  have hdata : ∀ k ∈ Finset.Ico 1 m,
      ∀ (lb : FiniteIrreducibleCharacterBasis (centralSylowPowerCentralizer n S e k))
        (ℓ : lb.index), (∀ c, (lb.representation ℓ).character c = lamN c) →
        TwistedRegularIntegralBasisData lb ideal ℓ (fun c => lamN c) (fun c => ΦN c) ε
          ((m : ℤ) • Bm) := by
    intro k hk lb ℓ hℓ
    have hℓ' : ∀ c, (lb.representation ℓ).character c =
        lam (Subgroup.inclusion (centralizer_zpow_le_involutionCentralizer n hn S e k
          (hkdvd k hk)) c) := fun c => by
      rw [hℓ, hlamN c (hCkN k hk c.2)]
      rfl
    have h := (hCdata k (hkdvd k hk) lb ℓ hℓ').2
    rw [hM] at h
    have hfun₁ : (fun c : centralSylowPowerCentralizer n S e k => lamN c) =
        fun c => (lam (Subgroup.inclusion (centralizer_zpow_le_involutionCentralizer n hn S e k
          (hkdvd k hk)) c) : ℂ) := by
      funext c
      rw [hlamN c (hCkN k hk c.2)]
      rfl
    have hfun₂ : (fun c : centralSylowPowerCentralizer n S e k => ΦN c) =
        fun c => ΦH (centralizerOddCoreMap n S e (Subgroup.inclusion
          (centralizer_zpow_le_involutionCentralizer n hn S e k (hkdvd k hk)) c)) := by
      funext c
      rw [hΦN c (hCkN k hk c.2)]
      rfl
    rw [hfun₁, hfun₂]
    exact h
  have hlabel : ∀ k ∈ Finset.Ico 1 m,
      ∀ lb : FiniteIrreducibleCharacterBasis (centralSylowPowerCentralizer n S e k),
        ∃ ℓ : lb.index, ∀ c, (lb.representation ℓ).character c = lamN c := by
    intro k hk lb
    obtain ⟨ℓ, hℓ⟩ := CompatibleFamily.exists_linear_label lb (lam.comp (Subgroup.inclusion
      (centralizer_zpow_le_involutionCentralizer n hn S e k (hkdvd k hk))))
    refine ⟨ℓ, fun c => ?_⟩
    rw [hℓ, hlamN c (hCkN k hk c.2)]
    rfl
  have hlocal : ∀ k ∈ Finset.Ico 1 m, ∀ (hk2 : IsPGroup 2 (Subgroup.zpowers (a ^ k)))
      (lb : FiniteIrreducibleCharacterBasis
        (Subgroup.centralizer (Subgroup.zpowers (a ^ k) : Set G))) (ℓ : lb.index),
      (∀ c, (lb.representation ℓ).character c = lamN c) →
      brauerNormalizerCharacterResidueHom ideal 2 (Subgroup.zpowers (a ^ k)) hk2
          (Subgroup.centralizer (Subgroup.zpowers (a ^ k) : Set G)) le_rfl
          (Subgroup.centralizer_le_normalizer _) lb ℓ =
        centralCharacterResidueHom basis ideal B ∧
      ∀ θ, brauerNormalizerCharacterResidueHom ideal 2 (Subgroup.zpowers (a ^ k)) hk2
          (Subgroup.centralizer (Subgroup.zpowers (a ^ k) : Set G)) le_rfl
          (Subgroup.centralizer_le_normalizer _) lb θ =
        centralCharacterResidueHom basis ideal B →
        θ ∈ coefficientBlock lb (localizedComplexIntegerRing ideal) ℓ := by
    intro k hk hk2 lb ℓ hℓ
    have hxu : wreathModelHom S e (Original.x (2 ^ n)) ∈ Subgroup.zpowers (a ^ k) := by
      obtain ⟨l, hl⟩ := exists_zpow_eq_involution n (by omega) S e k (hkdvd k hk)
      rw [zpow_natCast] at hl
      rw [← hl]
      exact Subgroup.zpow_mem_zpowers _ _
    obtain ⟨-, hle, hloc⟩ := hA (a ^ k) hk2 hxu
    obtain ⟨-, hlb⟩ := hloc lb
    obtain ⟨principal, hprincipal⟩ := finiteIrreducibleCharacterBasis_exists_principal_label lb
    have hℓ' : ∀ c, (lb.representation ℓ).character c =
        lam (Subgroup.inclusion (FlatTwistedBases.centralizer_zpowers_le_involutionCentralizer S
          e hxu) c) := fun c => by
      rw [hℓ, hlamN c (hle c.2)]
      rfl
    obtain ⟨hbrauer, hunique, -⟩ := hlb ℓ principal hℓ' hprincipal
    exact ⟨hbrauer, fun θ hθ => (coefficientBlock_mem_iff _ _ _ _).mpr
      (sameCoefficientBlock_symm _ _ (hunique θ hθ))⟩
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
  have hC₁ : centralSylowPowerCentralizer n S e (1 : ℕ) = Subgroup.centralizer {a} := by
    rw [hCk 1, pow_one]
  have hC₁k : ∀ k : ℕ, ∀ y ∈ centralSylowPowerCentralizer n S e (1 : ℕ),
      y ∈ centralSylowPowerCentralizer n S e k := by
    intro k y hy
    rw [hC₁, Subgroup.mem_centralizer_singleton_iff] at hy
    rw [hCk k, Subgroup.mem_centralizer_singleton_iff]
    exact ((Commute.pow_left (show Commute a y from hy.symm) k).eq).symm
  have hindep₁ : ∀ α β : ℂ, (∀ y ∈ centralSylowPowerCentralizer n S e (1 : ℕ),
      Odd (orderOf y) → α + β * (1 + ε * ΦN y) = 0) → α = 0 ∧ β = 0 := by
    intro α β hαβ
    refine eq_zero_of_odd_combination _ ε _ hP₁.degree hP₁.linearIndependent (fun y hy => ?_)
    have h := hαβ y y.2 (by rwa [Subgroup.orderOf_coe])
    rw [hΦN y (hCkN 1 h1m y.2)] at h
    exact h
  have hindep : ∀ k ∈ Finset.Ico 1 m, ∀ α β : ℂ,
      (∀ y ∈ centralSylowPowerCentralizer n S e k, Odd (orderOf y) →
        α + β * (1 + ε * ΦN y) = 0) → α = 0 ∧ β = 0 :=
    fun k _ α β hαβ => hindep₁ α β fun y hy hyodd => hαβ y (hC₁k k y hy) hyodd
  obtain ⟨v, hvint, hvrow, hvuniq, hvgram, hvodd⟩ := twisted_section_rows_family basis ideal B ha
    ⟨n, rfl⟩ (fun k => centralSylowPowerCentralizer n S e k) hCk lamN ΦN hΦreal ε
    ((m : ℤ) • Bm) hlocal hlabel hdata (fun k hk c hc => hlam0 c (hCkN k hk hc)) hindep
    (fun k hk h hh hkh => wreath_powers_eq_of_isConj n hn S e hk hh hkh) hζ
  have hreal1 : ∀ χ : basis.index, conj ((basis.representation χ).character 1) =
      (basis.representation χ).character 1 := by
    intro χ
    have h1 : (basis.representation χ).character 1 =
        (Module.finrank ℂ (basis.representation χ).vector : ℂ) := Representation.char_one _
    rw [h1, Complex.conj_natCast]
  have hone : Odd (orderOf (1 : G)) := by
    rw [orderOf_one]
    exact odd_one
  have hvdeg : ∀ k ∈ Finset.Ico 1 m, ∀ ℓ,
      ∑ χ ∈ BB, (basis.representation χ).character 1 * v χ k ℓ = 0 := by
    intro k hk ℓ
    rw [← hvodd k hk ℓ 1 hone]
    refine Finset.sum_congr rfl fun χ _ => ?_
    rw [hreal1, mul_comm]
  obtain ⟨ℓ₁, hℓ₁⟩ := hlabel 1 h1m lb₁
  have hint : ∀ χ ∈ BB, ∀ j ∈ Finset.Ico 1 m, ∀ ℓ,
      ∃ z : ℤ, fourierTransform m ζ (fun k => v χ k ℓ) j = z := by
    intro χ hχ j hj ℓ
    rw [Finset.mem_Ico] at hj
    refine twisted_fourierTransform_integral basis ideal ha _ hC₁ lb₁ ℓ₁ lamN ΦN ε
      ((m : ℤ) • Bm) (hdata 1 h1m lb₁ ℓ₁ hℓ₁) (fun c hc => hlam0 c (hCkN 1 h1m hc)) hindep₁
      hζ χ (v χ) (fun k hk y hy hyodd => hvrow χ hχ k hk y (hC₁k k y hy) hyodd) hj.1 hj.2 ℓ
  have hreal : ∀ χ ∈ BB, ∀ j ∈ Finset.Ico 1 m, ∀ ℓ,
      conj (fourierTransform m ζ (fun k => v χ k ℓ) j) =
        fourierTransform m ζ (fun k => v χ k ℓ) j := by
    intro χ hχ j hj ℓ
    obtain ⟨z, hz⟩ := hint χ hχ j hj ℓ
    rw [hz, map_intCast]
  have hfgram : ∀ j ∈ Finset.Ico 1 m, ∀ h ∈ Finset.Ico 1 m, ∀ ℓ t,
      ∑ χ ∈ BB, fourierTransform m ζ (fun k => v χ k ℓ) j *
          fourierTransform m ζ (fun k => v χ k t) h =
        ((if j = h then 1 else 0) + 1) * (Bm ℓ t : ℂ) := by
    intro j hj h hh ℓ t
    rw [Finset.mem_Ico] at hj hh
    have hg := fourierTransform_gram BB hζ (fun χ k => v χ k ℓ) (fun χ k => v χ k t)
      (((m : ℤ) • Bm) ℓ t : ℂ) (fun k hk h' hh' => hvgram k hk h' hh' ℓ t) hj.1 hj.2 hh.1 hh.2
    rw [← Finset.sum_congr rfl fun χ hχ => by
      rw [hreal χ hχ j (Finset.mem_Ico.mpr hj) ℓ]] at hg
    rw [hg]
    have hm0 : (m : ℂ) ≠ 0 := by exact_mod_cast (show m ≠ 0 by omega)
    simp only [Matrix.smul_apply, smul_eq_mul]
    push_cast
    field_simp
  have hfodd : ∀ j ∈ Finset.Ico 1 m, ∀ ℓ, ∀ z : G, Odd (orderOf z) →
      ∑ χ ∈ BB, fourierTransform m ζ (fun k => v χ k ℓ) j *
        conj ((basis.representation χ).character z) = 0 := by
    intro j _ ℓ z hz
    have hterm : ∀ χ, fourierTransform m ζ (fun k => v χ k ℓ) j *
        conj ((basis.representation χ).character z) =
        (m : ℂ)⁻¹ * ∑ k ∈ Finset.Ico 1 m, (ζ ^ (j * k) - 1) *
          (v χ k ℓ * conj ((basis.representation χ).character z)) := by
      intro χ
      unfold fourierTransform
      rw [mul_assoc, Finset.sum_mul]
      congr 1
      refine Finset.sum_congr rfl fun k _ => ?_
      ring
    rw [Finset.sum_congr rfl fun χ _ => hterm χ, ← Finset.mul_sum, Finset.sum_comm]
    rw [Finset.sum_eq_zero fun k hk => by rw [← Finset.mul_sum, hvodd k hk ℓ z hz, mul_zero],
      mul_zero]
  refine ⟨v, fun χ _ k hk ℓ => hvint χ k hk ℓ, hvrow, fun χ hχ k hk w hw => hvuniq χ hχ k hk w hw,
    hvgram, hvodd, hvdeg, hint, hfgram, hfodd, ?_, ?_, ?_, ?_⟩
  · intro j hj ℓ
    rw [← hfodd j hj ℓ 1 hone]
    refine Finset.sum_congr rfl fun χ _ => ?_
    rw [hreal1, mul_comm]
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
  · intro j hj h hh hjh
    have h' := hfgram j hj h hh 0 0
    rw [ite_eq_right hjh] at h'
    rw [h']
    simp [Bm]

end CFSG.Wreathed

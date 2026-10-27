module

public import CFSG.CharacterTheory.Wreathed.ConditionalCompleteBase
public import CFSG.CharacterTheory.Wreathed.ConditionalGlobalDegreesVanishing
public import CFSG.CharacterTheory.Wreathed.ConditionalGlobalDegreesOrbits
public import CFSG.CharacterTheory.Wreathed.ConditionalGlobalDegreesFinal

public section

open scoped BigOperators Classical ComplexConjugate

namespace CFSG.Wreathed.ConditionalGlobalDegrees

open CFSG.TwoRankLowerBound.Helpers CFSG.Semidihedral.Principal
  CFSG.ComponentClassification.CatalogueSchreierLinearTwo
  CFSG.Semidihedral.SemilinearOddExtensions CFSG.Wreathed.ActualProjectiveLayer
  CFSG.Wreathed.CyclicCentralSL2Extension CFSG.Wreathed.ConditionalFourier
  CFSG.Wreathed.AdaptedBaseFusion CFSG.Wreathed.ConditionalSquareRoot
  CFSG.Wreathed.ConditionalGeneralBase CFSG.Wreathed.ConditionalFirstFourierRows
  CFSG.Wreathed.ConditionalOddFourier CFSG.Wreathed.ConditionalFiveFixed
  CFSG.Wreathed.ConditionalCompleteBase

theorem modulus_facts {m M : ℕ} (hm : m = 2 * M) (hM : 2 ≤ M) :
    M + M = m ∧ m - 2 ∈ Finset.Ico 1 m ∧ Even (m - 2) := by
  refine ⟨by omega, Finset.mem_Ico.mpr ⟨by omega, by omega⟩, ⟨M - 1, by omega⟩⟩

theorem sub_mem_Ico_of_ne_half {m M k : ℕ} (hm : m = 2 * M) (hk : k ∈ Finset.Ico 1 m)
    (hkM : k ≠ M) : m - k ∈ Finset.Ico 1 m ∧ k ≠ m - k ∧ k ≤ m := by
  rw [Finset.mem_Ico] at hk ⊢
  omega

theorem not_four_dvd_odd_sub_neg (i : ℕ) :
    ¬ (4 : ℤ) ∣ ((2 * i + 1 : ℕ) : ℤ) - -((2 * i + 1 : ℕ) : ℤ) := by
  push_cast
  omega

theorem four_dvd_two_pow {n : ℕ} (hn : 2 ≤ n) : (4 : ℤ) ∣ ((2 ^ n : ℕ) : ℤ) := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 2 := ⟨n - 2, by omega⟩
  exact ⟨2 ^ k, by push_cast; ring⟩

theorem three_le_prime_pow {p f : ℕ} (hp : p.Prime) (hpodd : p ≠ 2) (hf : 1 ≤ f) :
    3 ≤ p ^ f :=
  calc 3 ≤ p := lt_of_le_of_ne hp.two_le (Ne.symm hpodd)
    _ = p ^ 1 := (pow_one p).symm
    _ ≤ p ^ f := Nat.pow_le_pow_right hp.pos hf

theorem conditional_global_principal_degrees_and_involution_values_of_localHyp
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
      let J : Finset ℕ := (Finset.Ico 1 m).filter Odd
      let ch : basis.index → G → ℂ := fun ψ => (basis.representation ψ).character
      let deg : basis.index → ℤ := fun ψ => (Module.finrank ℂ (basis.representation ψ).vector : ℤ)
      (∃ σ υ g : G, IsAdaptedBase U a w σ υ g) ∧
      ∀ ζ : ℂ, IsPrimitiveRoot ζ m → ∀ θ : ℂ, IsPrimitiveRoot θ (2 * m) → θ ^ 2 = ζ →
      let ν : basis.index → ℕ → ℕ := fun χ t' =>
        Module.finrank ℂ (Module.End.eigenspace ((basis.representation χ).representation y)
          (θ ^ t'))
      let c : basis.index → ℕ → ℤ := fun χ r => (ν χ (2 * r) : ℤ) - ν χ (2 * r + m)
      let Y : ℕ → G → ℂ := fun r g =>
        ∑ χ ∈ B₀, (c χ r : ℂ) * (basis.representation χ).character g
      (∃ v : basis.index → ℕ → Fin 2 → ℂ, IsCentralSectionRows basis ideal principal a m
        (fun k => centralSylowPowerCentralizer n S e k) ΦN ε v) ∧
      ∀ v : basis.index → ℕ → Fin 2 → ℂ, IsCentralSectionRows basis ideal principal a m
        (fun k => centralSylowPowerCentralizer n S e k) ΦN ε v →
      let fc : basis.index → ℕ → ℂ := fun χ j => fourierTransform m ζ (fun k => v χ k 0) j
      let X : ℕ → G → ℂ := fun j => ∑ χ ∈ B₀, fc χ j • (basis.representation χ).character
      let Fs : ZMod m → basis.index → ℂ := fun j χ =>
        fourierTransform m ζ (fun k => v χ k 1) j.val
      ∀ (σb υb : U) (g : G), IsAdaptedBase U a w σb υb g →
      (∃ lam : ZMod m → ZMod m → U →* ℂ,
        ∀ i j, lam i j σb = ζ ^ i.val ∧ lam i j υb = ζ ^ j.val) ∧
      ∀ lam : ZMod m → ZMod m → U →* ℂ,
        (∀ i j, lam i j σb = ζ ^ i.val ∧ lam i j υb = ζ ^ j.val) →
      let tm : ZMod m → ZMod m → basis.index → ℂ := fun i j χ =>
        (Nat.card U : ℂ)⁻¹ * ∑ u : U, (basis.representation χ).character u * conj (lam i j u)
      let cb : ZMod m → ZMod m → basis.index → ℂ := fun i j χ =>
        tm 0 0 χ - tm i j χ + q₀ * (Fs i χ + Fs j χ + Fs (-i - j) χ)
      let C : G → ℂ := ∑ χ ∈ B₀, cb M M χ • (basis.representation χ).character
      let cf : ZMod m → ZMod m → G → ℂ := fun i j =>
        ∑ χ ∈ B₀, cb i j χ • (basis.representation χ).character
      let constituents : (Fin 3 → basis.index) → (Fin 3 → ℤ) → (Fin 3 → ℤ) → ℤ →
          (ℕ → basis.index) → ℕ → Fin 3 → Prop := fun α β η σ χ δ e₀ =>
        Function.Injective α ∧ (∀ i, α i ∈ B₀ ∧ α i ≠ principal) ∧
        (∀ i, β i = 1 ∨ β i = -1) ∧ (∀ i, η i = 1 ∨ η i = -1) ∧ (σ = 1 ∨ σ = -1) ∧
        Set.InjOn χ J ∧ (∀ j ∈ J, χ j ∈ B₀ ∧ χ j ≠ principal ∧ ∀ i, χ j ≠ α i) ∧ 0 < δ ∧
        η e₀ = -β e₀ ∧ (∀ i, i ≠ e₀ → η i = β i) ∧ (∀ i, η i = -β i → i = e₀) ∧
        Y 0 = 1 + ∑ i, (β i : ℂ) • (basis.representation (α i)).character ∧
        (∀ j ∈ J, X j = -1 + ∑ i, (η i : ℂ) • (basis.representation (α i)).character +
          (2 * σ : ℂ) • (basis.representation (χ j)).character) ∧
        (∀ j ∈ J, (basis.representation (χ j)).character 1 = δ) ∧
        1 + ∑ i, (β i : ℂ) * (basis.representation (α i)).character 1 = 0 ∧
        (σ * δ : ℂ) = 1 + β e₀ * (basis.representation (α e₀)).character 1 ∧
        β e₀ = σ ∧ (δ : ℂ) = (basis.representation (α e₀)).character 1 + σ
      (∃ (α : Fin 3 → basis.index) (β η : Fin 3 → ℤ) (σ : ℤ) (χ : ℕ → basis.index) (δ : ℕ)
          (e₀ : Fin 3), constituents α β η σ χ δ e₀) ∧
      ∀ (α : Fin 3 → basis.index) (β η : Fin 3 → ℤ) (σ : ℤ) (χ : ℕ → basis.index) (δ : ℕ)
          (e₀ : Fin 3), constituents α β η σ χ δ e₀ →
      let core : basis.index → Fin 3 → Fin 3 → ℤ → ℤ → Prop := fun ω iB iD τ₀ κ =>
        ω ∈ B₀ ∧ ω ≠ principal ∧ (∀ i, ω ≠ α i) ∧ (∀ j ∈ J, ω ≠ χ j) ∧
        iB ≠ e₀ ∧ iD ≠ e₀ ∧ iB ≠ iD ∧ (τ₀ = 1 ∨ τ₀ = -1) ∧ (κ = 1 ∨ κ = -1) ∧
        Y 0 = 1 + (σ : ℂ) • ch (α e₀) - (τ₀ : ℂ) • ch (α iB) + (κ : ℂ) • ch (α iD) ∧
        (∀ j ∈ J, X j = -1 - (σ : ℂ) • ch (α e₀) - (τ₀ : ℂ) • ch (α iB) +
          (κ : ℂ) • ch (α iD) + (2 * σ : ℂ) • ch (χ j)) ∧
        C = 1 - (σ : ℂ) • ch (α e₀) - (τ₀ : ℂ) • ch (α iB) - (κ : ℂ) • ch (α iD) +
          (2 * τ₀ : ℂ) • ch ω ∧
        deg ω = deg (α iB) - τ₀ ∧ 0 < deg (α iB) - τ₀
      let evenFamily : basis.index → Fin 3 → Fin 3 → ℤ → ℤ → (ℕ → Fin 4 → basis.index) →
          (ℕ → Fin 4 → ℤ) → Prop := fun ω iB iD τ₀ κ γ εs =>
        (∀ r ∈ Finset.Ico 1 M, ∀ l, γ r l ∈ B₀ ∧ (εs r l = 1 ∨ εs r l = -1)) ∧
        (∀ r ∈ Finset.Ico 1 M, Function.Injective (γ r)) ∧
        (∀ r ∈ Finset.Ico 1 M, ∀ r' ∈ Finset.Ico 1 M, r ≠ r' → ∀ l l', γ r l ≠ γ r' l') ∧
        (∀ r ∈ Finset.Ico 1 M, ∀ l, γ r l ≠ principal ∧ γ r l ≠ α e₀ ∧ γ r l ≠ α iB ∧
          γ r l ≠ α iD ∧ γ r l ≠ ω ∧ ∀ j ∈ J, γ r l ≠ χ j) ∧
        (∀ r ∈ Finset.Ico 1 M, X (m - 2 * r) = -1 - (σ : ℂ) • ch (α e₀) -
          (τ₀ : ℂ) • ch (α iB) + (κ : ℂ) • ch (α iD) + ∑ l, (εs r l : ℂ) • ch (γ r l)) ∧
        (∀ r ∈ Finset.Ico 1 M, Y r = (εs r 0 : ℂ) • ch (γ r 0) + (εs r 1 : ℂ) • ch (γ r 1) -
          (εs r 2 : ℂ) • ch (γ r 2) - (εs r 3 : ℂ) • ch (γ r 3)) ∧
        (∀ r ∈ Finset.Ico 1 M, εs r 0 * deg (γ r 0) + εs r 1 * deg (γ r 1) = σ * δ ∧
          εs r 2 * deg (γ r 2) + εs r 3 * deg (γ r 3) = σ * δ)
      (∃ (ω : basis.index) (iB iD : Fin 3) (τ₀ κ : ℤ) (γ : ℕ → Fin 4 → basis.index)
          (εs : ℕ → Fin 4 → ℤ), core ω iB iD τ₀ κ ∧ evenFamily ω iB iD τ₀ κ γ εs) ∧
      ∀ (ω : basis.index) (iB iD : Fin 3) (τ₀ κ : ℤ) (γ : ℕ → Fin 4 → basis.index)
          (εs : ℕ → Fin 4 → ℤ), core ω iB iD τ₀ κ → evenFamily ω iB iD τ₀ κ γ εs →
      let K : G → ℂ := 1 - (σ : ℂ) • ch (α e₀) + (2 * τ₀ : ℂ) • ch ω
      ∀ V : Finset (ZMod m × ZMod m), (∀ I ∈ V, (MulAction.orbit (dualGroup m) I).ncard = 6) →
        (∀ I, (MulAction.orbit (dualGroup m) I).ncard = 6 →
          ∃! I', I' ∈ V ∧ I' ∈ MulAction.orbit (dualGroup m) I) →
      let completeWitness : (ℕ → Fin 2 → basis.index) → (ℕ → Fin 2 → basis.index) →
          (ℕ → Fin 2) → (ZMod m × ZMod m → basis.index) → ℤ → ℤ → Prop :=
        fun P Q er ψ ρ₀ Δ =>
          (∀ r ∈ Finset.Ico 1 M, ({P r 0, Q r 0, P r 1, Q r 1} : Finset basis.index) =
              Finset.univ.image (γ r) ∧
            ∀ e', deg (P r e') = deg (α iB) ∧ deg (Q r e') = deg (α iD)) ∧
          (∀ r ∈ Finset.Ico 1 M, X (m - 2 * r) = -1 - (σ : ℂ) • ch (α e₀) -
            (τ₀ : ℂ) • ch (α iB) + (κ : ℂ) • ch (α iD) + (τ₀ : ℂ) • (ch (P r 0) + ch (P r 1)) -
            (κ : ℂ) • (ch (Q r 0) + ch (Q r 1))) ∧
          (∀ r ∈ Finset.Ico 1 M, Y r = (τ₀ : ℂ) • (ch (P r 0) - ch (P r 1)) -
            (κ : ℂ) • (ch (Q r 0) - ch (Q r 1))) ∧
          (∀ r ∈ Finset.Ico 1 M,
            cf r r = K - (τ₀ : ℂ) • ch (P r (er r)) - (κ : ℂ) • ch (Q r (er r)) ∧
            cf ((r + M : ℕ) : ZMod m) ((r + M : ℕ) : ZMod m) =
              K - (τ₀ : ℂ) • ch (P r (1 - er r)) - (κ : ℂ) • ch (Q r (1 - er r))) ∧
          (ρ₀ = 1 ∨ ρ₀ = -1) ∧ 0 < Δ ∧ ρ₀ * Δ = -(τ₀ * deg (α iB) + κ * deg (α iD)) ∧
          τ₀ * deg (α iB) + κ * deg (α iD) ≠ 0 ∧ Set.InjOn ψ ↑V ∧
          (∀ I ∈ V, ψ I ∈ B₀ ∧ ψ I ≠ principal ∧ ψ I ≠ α e₀ ∧ ψ I ≠ α iB ∧ ψ I ≠ α iD ∧
            ψ I ≠ ω ∧ (∀ j ∈ J, ψ I ≠ χ j) ∧ (∀ r ∈ Finset.Ico 1 M, ∀ l, ψ I ≠ γ r l) ∧
            cf I.1 I.2 = K + (ρ₀ : ℂ) • ch (ψ I) ∧ deg (ψ I) = Δ) ∧
          cf 0 0 = 0 ∧ cf M M = K - (τ₀ : ℂ) • ch (α iB) - (κ : ℂ) • ch (α iD) ∧
          (∀ I I' : ZMod m × ZMod m, I' ∈ MulAction.orbit (dualGroup m) I →
            cf I'.1 I'.2 = cf I.1 I.2) ∧
          (∀ I : ZMod m × ZMod m, I = (0, 0) ∨
            I ∈ MulAction.orbit (dualGroup m) ((M : ZMod m), (M : ZMod m)) ∨
            (∃ r ∈ Finset.Ico 1 M, I ∈ MulAction.orbit (dualGroup m) ((r : ZMod m), (r : ZMod m)) ∨
              I ∈ MulAction.orbit (dualGroup m)
                (((r + M : ℕ) : ZMod m), ((r + M : ℕ) : ZMod m))) ∨
            ∃ I' ∈ V, I ∈ MulAction.orbit (dualGroup m) I') ∧
          B₀ = ({principal, α e₀, α iB, α iD, ω} : Finset basis.index) ∪ J.image χ ∪
            ((Finset.Ico 1 M ×ˢ (Finset.univ : Finset (Fin 2))).image fun re => P re.1 re.2) ∪
            ((Finset.Ico 1 M ×ˢ (Finset.univ : Finset (Fin 2))).image fun re => Q re.1 re.2) ∪
            V.image ψ ∧
          B₀.card = (m ^ 2 + 12 * m + 8) / 6 ∧
          Multiset.map deg B₀.val = {1, deg (α e₀), deg (α iB), deg (α iD), deg (α iB) - τ₀} +
            Multiset.replicate M (δ : ℤ) + Multiset.replicate (m - 2) (deg (α iB)) +
            Multiset.replicate (m - 2) (deg (α iD)) +
            Multiset.replicate ((m - 1) * (m - 2) / 6) Δ
      (∃ (P Q : ℕ → Fin 2 → basis.index) (er : ℕ → Fin 2) (ψ : ZMod m × ZMod m → basis.index)
          (ρ₀ Δ : ℤ), completeWitness P Q er ψ ρ₀ Δ) ∧
      ∀ (P Q : ℕ → Fin 2 → basis.index) (er : ℕ → Fin 2) (ψ : ZMod m × ZMod m → basis.index)
          (ρ₀ Δ : ℤ), completeWitness P Q er ψ ρ₀ Δ →
      let Qd : ℤ := (q : ℤ) ^ 2 + ε * q + 1
      let x : G := a ^ M
      (σ = -ε ∧ τ₀ = 1 ∧ κ = ε ∧ ρ₀ = -ε) ∧
      (deg (α e₀) = (q : ℤ) ^ 3 ∧ deg (α iB) = Qd ∧ deg (α iD) = q * Qd ∧
        deg ω = q * (q + ε) ∧ (∀ j ∈ J, deg (χ j) = (q : ℤ) ^ 3 - ε) ∧
        (∀ r ∈ Finset.Ico 1 M, ∀ e', deg (P r e') = Qd ∧ deg (Q r e') = q * Qd) ∧
        (∀ I ∈ V, deg (ψ I) = (q + ε) * Qd) ∧ Δ = (q + ε) * Qd) ∧
      Multiset.map deg B₀.val = {1, (q : ℤ) ^ 3, q * (q + ε)} +
        Multiset.replicate (m - 1) Qd + Multiset.replicate (m - 1) (q * Qd) +
        Multiset.replicate M ((q : ℤ) ^ 3 - ε) +
        Multiset.replicate ((m - 1) * (m - 2) / 6) ((q + ε) * Qd) ∧
      (ch principal x = 1 ∧ ch (α e₀) x = q ∧ ch (α iB) x = 2 + ε * q ∧
        ch (α iD) x = 2 * q + ε ∧ ch ω x = 1 + ε * q ∧ (∀ j ∈ J, ch (χ j) x = ε - q) ∧
        (∀ r ∈ Finset.Ico 1 M, ∀ e', ch (P r e') x = (if Odd r then -ε * q else 2 + ε * q) ∧
          ch (Q r e') x = (if Odd r then -ε else 2 * q + ε)) ∧
        ∀ I ∈ V, ch (ψ I) x =
          if Even I.1.val ∧ Even I.2.val then 3 * (q + ε) else -(q + ε)) ∧
      (∀ I I' : ZMod m × ZMod m, I' ∈ MulAction.orbit (dualGroup m) I →
        (Even I'.1.val ∧ Even I'.2.val ↔ Even I.1.val ∧ Even I.2.val)) ∧
      (V.filter fun I => Even I.1.val ∧ Even I.2.val).card = (M - 1) * (M - 2) / 6 ∧
      (V.filter fun I => ¬ (Even I.1.val ∧ Even I.2.val)).card = m * (m - 2) / 8 ∧
      ∀ k ∈ Finset.Ico 1 m, ∀ z ∈ Subgroup.centralizer {a ^ k}, Odd (orderOf z) →
        ch (α e₀) (a ^ k * z) = ΦN z ∧ ch ω (a ^ k * z) = 1 + ε * ΦN z ∧
        ch (α iB) (a ^ k * z) = 1 + (-1) ^ k * (1 + ε * ΦN z) ∧
        ch (α iD) (a ^ k * z) = -ε + ε * (1 + (-1) ^ k) * (1 + ε * ΦN z) ∧
        ∀ j ∈ J, ch (χ j) (a ^ k * z) = (ΦN z - ε) * ζ ^ (-((j : ℤ) * k)) := by
  refine ⟨hloc.modelData, ?_⟩
  intro F _ _ Sigma b hSigma ρ Ψ hdata m M s t w a y U ΦH ΦN ε q q₀ B₀ J ch deg
  have hCB := (conditional_complete_base_column_support_and_principal_block_exhaustion_of_localHyp
    n hn S e p f hp hpodd hf hloc ideal basis principal hprincipal).2 F Sigma b hSigma ρ Ψ
    hdata
  obtain ⟨-, horbit0, -, -, -, -, -, hadapt, hGBζ⟩ :=
    (conditional_general_base_integral_columns_and_second_row_reconstruction_of_localHyp n hn S e p
      f hp hpodd hf hloc ideal basis principal hprincipal).2 F Sigma b hSigma ρ Ψ hdata
  obtain ⟨hyord, -, -, -, -, -, hyconj, hSR⟩ :=
    (conditional_square_root_cyclic_section_fourier_columns_and_parity_of_localHyp n hn S e p f hp
      hpodd hf hloc ideal basis principal hprincipal).2 F Sigma b hSigma ρ Ψ hdata
  refine ⟨hadapt, fun ζ hζ θ hθ hθζ => ?_⟩
  intro ν c Y
  obtain ⟨hvex, hGBv⟩ := hGBζ ζ hζ θ hθ hθζ
  obtain ⟨-, hcr, -, -, hY1, -, -, -, -, hallSR⟩ := hSR ζ hζ θ hθ hθζ
  obtain ⟨vG, -, hvG, huniqG, -⟩ :=
    (conditional_global_central_section_integral_fourier_columns_of_localHyp n hn S e p f hp hpodd
      hf hloc ideal basis principal hprincipal).2 F Sigma b
    hSigma ρ Ψ hdata ζ hζ
  refine ⟨hvex, fun v hv => ?_⟩
  intro fc X Fs σb υb g hg
  obtain ⟨hlamex, hGBlam⟩ := hGBv v hv σb υb g hg
  have hCBv := ((hCB.2 ζ hζ θ hθ hθζ).2 v hv σb υb g hg).2
  refine ⟨hlamex, fun lam hlam => ?_⟩
  intro tm cb C cf constituents
  obtain ⟨-, hcint, hc00, hsym, hcprin, -, -, -, -, hcdeg, -, -, hval, -, -, -⟩ :=
    hGBlam lam hlam
  have hCBlam := hCBv lam hlam
  refine ⟨hCBlam.1, fun α β η σ χ δ e₀ hP => ?_⟩
  intro core evenFamily
  have hCBc := hCBlam.2 α β η σ χ δ e₀ hP
  refine ⟨hCBc.1, fun ω iB iD τ₀ κ γ εs hcore heven => ?_⟩
  intro K V hV6 hVrep completeWitness
  refine ⟨hCBc.2 ω iB iD τ₀ κ γ εs hcore heven V hV6 hVrep, fun P Q er ψ ρ₀ Δ hW => ?_⟩
  intro Qd x
  obtain ⟨hlab, hXrel, -, hdiagcf, hρ₀, hΔ, hρΔ, -, hψinj, hψ, -, hcfMM, -, hcov, hBunion, -,
    hBmul⟩ := hW
  obtain ⟨hinj, hα, -, -, hσ, hχinj, hχ, -, -, -, -, -, -, hdegχ, -, -, -, hδ⟩ := hP
  obtain ⟨hωB, hωp, hωα, hωχ, hBe, hDe, hBD, hτ₀, hκ, hY0c, hXjc, hCc, hdω, -⟩ := hcore
  obtain ⟨hγε, hγinj, hγdisj, hγav, hXk, hYr, hγdeg⟩ := heven
  have hm4 : 4 ≤ m := by
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  have hm2 : m = 2 * M :=
    (Nat.two_mul_div_two_of_even ((Nat.even_pow' (by omega)).mpr even_two)).symm
  have hM2 : 2 ≤ M := by omega
  have hM0 : 0 < M := by omega
  have : NeZero m := ⟨by omega⟩
  have hP0 : principal ∈ B₀ := coefficientBlock_self_mem basis _ principal
  have hαB : ∀ i, α i ∈ B₀ := fun i => (hα i).1
  have hJ : J = (Finset.Ico 1 m).filter Odd := rfl
  have hJm : ∀ j ∈ J, j ∈ Finset.Ico 1 m := fun j hj => (Finset.mem_filter.mp hj).1
  have hIco : ∀ r ∈ Finset.Ico 1 M, 0 < r ∧ r < M := fun r hr => by
    rw [Finset.mem_Ico] at hr
    omega
  have hkI : ∀ r ∈ Finset.Ico 1 M, m - 2 * r ∈ Finset.Ico 1 m := fun r hr => by
    have := hIco r hr
    rw [Finset.mem_Ico]
    omega
  have hsymb : ∀ i j χ, cb i j χ = cb j i χ ∧ cb i j χ = cb j (-i - j) χ := hsym
  have hc00' : ∀ χ, cb 0 0 χ = 0 := hc00
  obtain ⟨Fc, hFc, -, -, -, -, hJcard, -, -⟩ := hallSR v hv
  have hJM : J.card = M := hJcard
  let cc : ℕ → basis.index → ℤ := fun j φ => Fc φ j 0
  have hcc : ∀ j ∈ Finset.Ico 1 m, ∀ φ ∈ B₀, (cc j φ : ℂ) = fc φ j :=
    fun j hj φ hφ => hFc φ hφ j hj 0
  have hXb : ∀ j ∈ Finset.Ico 1 m, basisCombination basis B₀ (cc j) = X j := fun j hj =>
    Finset.sum_congr rfl fun φ hφ => by rw [hcc j hj φ hφ]
  have hYb : ∀ r, basisCombination basis B₀ (fun φ => c φ r) = Y r := fun r =>
    basisCombination_eq_fun B₀ _
  have hXc : ∀ j ∈ Finset.Ico 1 m, ∀ φ ∈ B₀,
      fourierTransform m ζ (fun k => v φ k 0) ((j : ℕ) : ZMod m).val = (cc j φ : ℂ) := by
    intro j hj φ hφ
    rw [ZMod.val_cast_of_lt (Finset.mem_Ico.mp hj).2, hcc j hj φ hφ]
  have hCex : ∀ i j φ, ∃ z : ℤ, φ ∈ B₀ → cb i j φ = z := fun i j φ => by
    by_cases hφ : φ ∈ B₀
    · obtain ⟨z, hz⟩ := hcint i j φ hφ
      exact ⟨z, fun _ => hz⟩
    · exact ⟨0, fun h => absurd h hφ⟩
  choose Cz hCz using hCex
  have hCz' : ∀ i j, ∀ φ ∈ B₀, cb i j φ = Cz i j φ := fun i j φ hφ => hCz i j φ hφ
  have hcfb : ∀ i j, cf i j = basisCombination basis B₀ (Cz i j) := fun i j =>
    Finset.sum_congr rfl fun φ hφ => by rw [hCz' i j φ hφ]
  have hBA : α iB ≠ α e₀ := fun h => hBe (hinj h)
  have hDA : α iD ≠ α e₀ := fun h => hDe (hinj h)
  have hDB : α iD ≠ α iB := fun h => hBD (hinj h).symm
  have hS : CoreSetting B₀ principal (α e₀) (α iB) (α iD) ω σ τ₀ κ J χ (fun φ => c φ 0)
      (Cz M M) cc :=
    coreSetting_of_class hprincipal hP0 (hαB e₀) (hαB iB) (hαB iD) hωB (hα e₀).2 (hα iB).2
      (hα iD).2 hωp hBA hDA (hωα e₀) hDB (hωα iB) (hωα iD) hσ hτ₀ hκ
      (fun j hj => (hχ j hj).1) hχinj
      (fun j hj => ⟨(hχ j hj).2.1, (hχ j hj).2.2 e₀, (hχ j hj).2.2 iB, (hχ j hj).2.2 iD,
        fun h => hωχ j hj h.symm⟩)
      (by rw [hYb 0]; exact hY0c) (fun j hj => by rw [hXb j (hJm j hj)]; exact hXjc j hj)
      (by rw [← hcfb]; exact hCc)
  have hQ : ∀ r ∈ Finset.Ico 1 M, Quadruple B₀ principal (α e₀) (α iB) (α iD) ω σ τ₀ κ J χ
      (γ r) (εs r) (cc (m - 2 * r)) (fun φ => c φ r) := fun r hr =>
    quadruple_of_class hprincipal hP0 (hαB e₀) (hαB iB) (hαB iD) (hγinj r hr)
      (fun l => (hγε r hr l).1) (fun l => (hγε r hr l).2)
      (fun l => ⟨(hγav r hr l).1, (hγav r hr l).2.1, (hγav r hr l).2.2.1,
        (hγav r hr l).2.2.2.1, (hγav r hr l).2.2.2.2.1⟩)
      (fun l j hj => (hγav r hr l).2.2.2.2.2 j hj)
      (by rw [hXb _ (hkI r hr)]; exact hXk r hr) (by rw [hYb r]; exact hYr r hr)
  have hPQB : ∀ r ∈ Finset.Ico 1 M, ∀ e', P r e' ∈ B₀ ∧ Q r e' ∈ B₀ := fun r hr e' =>
    labels_mem (fun l => (hγε r hr l).1) (hγinj r hr) (hlab r hr).1 e'
  have hR : RepColumns B₀ principal (α e₀) (α iB) (α iD) ω σ τ₀ κ m M P Q er ψ ρ₀ V Cz := by
    refine ⟨fun φ hφ => ?_, fun φ hφ => ?_, fun r hr φ hφ => ?_, fun r hr φ hφ => ?_,
      fun I hI φ hφ => ?_, fun I I' hI' φ hφ => ?_, hcov⟩
    · have h := hc00' φ
      rw [hCz' 0 0 φ hφ] at h
      exact_mod_cast h
    · have h : basisCombination basis B₀ (Cz M M) = basisCombination basis B₀ (fun φ =>
          baseFixed principal (α e₀) ω σ τ₀ φ - τ₀ * unitVector (α iB) φ -
            κ * unitVector (α iD) φ) := by
        rw [basisCombination_diag hprincipal hP0 (hαB e₀) hωB (hαB iB) (hαB iD), ← hcfb]
        exact hcfMM
      exact eq_of_basisCombination_eq h hφ
    · have h : basisCombination basis B₀ (Cz r r) = basisCombination basis B₀ (fun φ =>
          baseFixed principal (α e₀) ω σ τ₀ φ - τ₀ * unitVector (P r (er r)) φ -
            κ * unitVector (Q r (er r)) φ) := by
        rw [basisCombination_diag hprincipal hP0 (hαB e₀) hωB (hPQB r hr _).1 (hPQB r hr _).2,
          ← hcfb]
        exact (hdiagcf r hr).1
      exact eq_of_basisCombination_eq h hφ
    · have h : basisCombination basis B₀ (Cz ((r + M : ℕ) : ZMod m) ((r + M : ℕ) : ZMod m)) =
          basisCombination basis B₀ (fun φ => baseFixed principal (α e₀) ω σ τ₀ φ -
            τ₀ * unitVector (P r (1 - er r)) φ - κ * unitVector (Q r (1 - er r)) φ) := by
        rw [basisCombination_diag hprincipal hP0 (hαB e₀) hωB (hPQB r hr _).1 (hPQB r hr _).2,
          ← hcfb]
        exact (hdiagcf r hr).2
      exact eq_of_basisCombination_eq h hφ
    · have h : basisCombination basis B₀ (Cz I.1 I.2) = basisCombination basis B₀ (fun φ =>
          baseFixed principal (α e₀) ω σ τ₀ φ + ρ₀ * unitVector (ψ I) φ) := by
        rw [basisCombination_gen hprincipal hP0 (hαB e₀) hωB (hψ I hI).1, ← hcfb]
        exact (hψ I hI).2.2.2.2.2.2.2.2.1
      exact eq_of_basisCombination_eq h hφ
    · have h : cb I'.1 I'.2 φ = cb I.1 I.2 φ :=
        base_column_orbit_invariant (fun i j => cb i j φ) (fun i j => hsymb i j φ) hI'
      rw [hCz' _ _ φ hφ, hCz' _ _ φ hφ] at h
      exact_mod_cast h
  have xPQ : ∀ t ∈ Finset.Ico 1 M, ∀ φ ∈ B₀, cc (m - 2 * t) φ =
      fixedPart principal (α e₀) (α iB) (α iD) σ τ₀ κ φ + (τ₀ * unitVector (P t 0) φ +
        τ₀ * unitVector (P t 1) φ + (-κ) * unitVector (Q t 0) φ +
        (-κ) * unitVector (Q t 1) φ) := by
    intro t ht φ hφ
    have h : basisCombination basis B₀ (cc (m - 2 * t)) = basisCombination basis B₀ (fun φ =>
        fixedPart principal (α e₀) (α iB) (α iD) σ τ₀ κ φ + (τ₀ * unitVector (P t 0) φ +
          τ₀ * unitVector (P t 1) φ + (-κ) * unitVector (Q t 0) φ +
          (-κ) * unitVector (Q t 1) φ)) := by
      rw [basisCombination_xk_labels hprincipal hP0 (hαB e₀) (hαB iB) (hαB iD)
        (fun e' => (hPQB t ht e').1) (fun e' => (hPQB t ht e').2), hXb _ (hkI t ht)]
      exact hXrel t ht
    exact eq_of_basisCombination_eq h hφ
  have T : ColumnTable B₀ principal (α e₀) (α iB) (α iD) ω σ τ₀ κ m M J χ γ εs P Q er ψ ρ₀ V
      (fun r φ => c φ r) cc Cz :=
    ⟨hm2, hM2, hJ, hS, hQ, hγdisj, fun r hr => (hlab r hr).1, fun I hI => by
      obtain ⟨n1, n2, n3, n4, n5, n6, n7, n8, -⟩ := hψ I hI
      exact ⟨n1, n2, n3, n4, n5, n6, n7, n8⟩, hψinj, hR, xPQ⟩
  have hval' : ∀ χ ∈ B₀, ∀ k ∈ Finset.Ico 1 m, ∀ z ∈ Subgroup.centralizer {a ^ k},
      Odd (orderOf z) → 2 * ch χ (a ^ k * z) =
        (1 - ε * ΦN z) * ∑ j ∈ Finset.Ico 1 m, ζ ^ (-((j : ℤ) * k)) *
          fourierTransform m ζ (fun k => v χ k 0) ((j : ℕ) : ZMod m).val +
        (1 + ε * ΦN z) * ∑ j ∈ Finset.Ico 1 m, ζ ^ (-((j : ℤ) * k)) *
          (∑ i : ZMod m, cb i (0 - i) χ - ∑ i : ZMod m, cb i (-(j : ZMod m) - i) χ) := hval
  have ST : SectionTable B₀ principal (α e₀) (α iB) (α iD) ω σ τ₀ κ m M J χ γ εs P Q er ψ ρ₀ V
      (fun r φ => c φ r) cc Cz ζ
      (fun φ j => fourierTransform m ζ (fun k => v φ k 0) ((j : ℕ) : ZMod m).val) cb ch a ΦN ε :=
    ⟨T, hζ, ⟨n, rfl⟩, hXc, hCz', hval'⟩
  have hp1 : ∀ g, ch principal g = 1 := fun g => by simp [ch, hprincipal]
  have h1 : ∀ φ ∈ B₀, ch φ 1 = deg φ := fun φ _ => by
    simp only [ch, deg, FiniteComplexRepresentation.character, Representation.char_one]
    push_cast
    rfl
  have hpos : ∀ φ ∈ B₀, 0 < deg φ := fun φ _ => by
    have h := irreducible_character_degree_ne_zero (basis.representation φ) (basis.irreducible φ)
    rw [FiniteComplexRepresentation.character, Representation.char_one] at h
    have h' : 0 < Module.finrank ℂ (basis.representation φ).vector :=
      Nat.pos_of_ne_zero (by exact_mod_cast h)
    show (0 : ℤ) < (Module.finrank ℂ (basis.representation φ).vector : ℤ)
    exact_mod_cast h'
  have hq3 : 3 ≤ q := by
    rw [show q = p ^ f from hdata.card]
    exact three_le_prime_pow hp hpodd hf
  have hεs : ε = 1 ∨ ε = -1 := by
    simp only [ε]
    split_ifs <;> simp
  have hΦ1 : ΦN 1 = (q : ℂ) := by
    have h1N : (1 : G) ∈ involutionCentralizer n S e := Subgroup.one_mem _
    simp only [ΦN, dite_eq_left h1N, ΦH]
    have hfix : Nat.card {x : Omega F // ((ρ (centralizerFullQuotientMap n hn S e
        (centralizerOddCoreMap n S e ⟨1, h1N⟩)) : coordinateE F) : Equiv.Perm (Omega F)) x =
          x} = Nat.card (Omega F) := Nat.card_congr (Equiv.subtypeUnivEquiv fun x => by
      rw [show (⟨1, h1N⟩ : involutionCentralizer n S e) = 1 from rfl, map_one, map_one,
        map_one]
      rfl)
    rw [hfix, CFSG.Wreathed.CentralSL2.card_omega]
    push_cast
    ring
  have hdeg0 : (1 : ℂ) + σ * ch (α e₀) 1 - τ₀ * ch (α iB) 1 + κ * ch (α iD) 1 = 0 := by
    have hY1' : Y 0 1 = 0 := hY1 0 hM0
    have h := congrFun hY0c 1
    rw [hY1'] at h
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Pi.one_apply] at h
    linear_combination -h
  have hxx : a ^ M * a ^ M = 1 := by
    rw [← pow_add, (modulus_facts hm2 hM2).1]
    have ha : orderOf a = m := orderOf_wreathModelHom_a n S e
    rw [← ha]
    exact pow_orderOf_eq_one a
  have hm4' : (4 : ℤ) ∣ (m : ℤ) := four_dvd_two_pow hn
  have hynr : ∀ i : ℕ, ¬ IsConj (y ^ (2 * i + 1)) (y ^ (2 * i + 1))⁻¹ := by
    intro i hc
    have hc' : IsConj (y ^ ((2 * i + 1 : ℕ) : ℤ)) (y ^ (-((2 * i + 1 : ℕ) : ℤ))) := by
      rw [zpow_neg, zpow_natCast]
      exact hc
    have hmod := (hyconj _ _ (by push_cast; exact ⟨i, by ring⟩)
      (by push_cast; exact ⟨-i - 1, by ring⟩)).mp hc'
    exact not_four_dvd_odd_sub_neg i (dvd_trans hm4' (Int.ModEq.dvd hmod.symm))
  have hyo : ∀ i : ℕ, orderOf (y ^ (2 * i + 1)) ∣ 2 ^ (n + 1) := fun i => by
    have h : orderOf y = 2 ^ (n + 1) := by rw [hyord]; show 2 * 2 ^ n = _; ring
    rw [← h]
    exact orderOf_pow_dvd _
  have hc0 : ∀ χ' ∈ B₀, (c χ' 0 : ℂ) = (M : ℂ)⁻¹ *
      ∑ i ∈ Finset.range M, (basis.representation χ').character (y ^ (2 * i + 1)) := by
    intro χ' hχ'
    have h := hcr χ' hχ' 0 hM0
    simp only [Nat.cast_zero, zero_mul, neg_zero, zpow_zero, mul_one] at h
    exact h
  have hWY : ∑ φ ∈ B₀, ((fun r φ => c φ r) 0 φ : ℂ) *
      (ch φ (a ^ M) * ch φ (a ^ M) / ch φ 1) = 0 :=
    weighted_power_vanishing basis ideal principal hxx hyo hynr (fun φ => (c φ 0 : ℂ)) hc0
  have ha : orderOf a = m := orderOf_wreathModelHom_a n S e
  have hCk : ∀ k : ℕ, centralSylowPowerCentralizer n S e k = Subgroup.centralizer {a ^ k} := by
    intro k
    simp only [centralSylowPowerCentralizer, zpow_natCast]
    rfl
  have hrow : ∀ χ ∈ B₀, ∀ k ∈ Finset.Ico 1 m, ∀ r ∈ Subgroup.centralizer {a ^ k},
      Odd (orderOf r) →
        (basis.representation χ).character (a ^ k * r) = v χ k 0 + v χ k 1 * (1 + ε * ΦN r) :=
    fun χ hχ k hk r hr hodd => hv χ hχ k hk r (by
      show r ∈ centralSylowPowerCentralizer n S e (k : ℤ)
      rw [hCk]
      exact hr) hodd
  have hne : ∀ k ∈ Finset.Ico 1 m,
      ∃ r ∈ Subgroup.centralizer {a ^ k}, Odd (orderOf r) ∧ ΦN r ≠ ΦN 1 := fun k hk =>
    exists_ne_of_unique_rows basis (v principal k)
      (fun r hr hodd => hrow principal hP0 k hk r hr hodd)
      (fun w hw => (huniqG principal hP0 k hk w (fun r hr hodd => hw r (by
          rw [← hCk]
          exact hr) hodd)).trans
        (huniqG principal hP0 k hk (v principal k) (fun r hr hodd => hrow principal hP0 k hk r
          (by
            rw [← hCk]
            exact hr) hodd)).symm)
  have hnr : ∀ k ∈ Finset.Ico 1 m, k ≠ M → ¬ IsConj (a ^ k) (a ^ k)⁻¹ := by
    intro k hk hkM hc
    obtain ⟨hmk, hne', hle⟩ := sub_mem_Ico_of_ne_half hm2 hk hkM
    have hinv : (a ^ k)⁻¹ = a ^ (m - k) := by
      refine (eq_inv_of_mul_eq_one_left ?_).symm
      rw [← pow_add, Nat.sub_add_cancel hle, ← ha]
      exact pow_orderOf_eq_one a
    rw [hinv] at hc
    exact hne' (wreath_powers_eq_of_isConj n hn S e hk hmk hc)
  have hu : ∀ k : ℕ, orderOf (a ^ k) ∣ 2 ^ n := fun k =>
    (orderOf_pow_dvd k).trans (by rw [ha])
  obtain ⟨-, hm2I, hm2e⟩ := modulus_facts hm2 hM2
  have hWXf := weighted_central_fourier_vanishing basis ideal principal hxx hm2 hu hnr hεs v
    hrow hne hζ (j := m - 2) hm2e
  have hWX : ∑ φ ∈ B₀, (cc (m - 2 * 1) φ : ℂ) * (ch φ (a ^ M) * ch φ (a ^ M) / ch φ 1) = 0 := by
    refine (Finset.sum_congr rfl fun φ hφ => ?_).trans hWXf
    rw [Nat.mul_one, hcc _ hm2I φ hφ]
    simp only [ch, fc]
    ring
  obtain ⟨hA, hB, hC, hD, hH⟩ := ST.global_conclusions (deg := deg) (q := q) (Δ := Δ) (δ := δ)
    hp1 h1 hpos hq3 hεs hΦ1 hdeg0 hWY hWX (fun r hr e' => (hlab r hr).2 e') hdω hdegχ hδ hρ₀ hΔ
    hρΔ (fun I hI => (hψ I hI).2.2.2.2.2.2.2.2.2) hV6 hBmul
  exact ⟨hA, hB, hC, hD, fun I I' h => evenEven_iff_of_mem_orbit ⟨M, hm2⟩ h,
    card_filter_evenEven hn V hV6 hVrep, card_filter_not_evenEven hn V hV6 hVrep, hH⟩

theorem conditional_global_principal_degrees_and_involution_values
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
      let J : Finset ℕ := (Finset.Ico 1 m).filter Odd
      let ch : basis.index → G → ℂ := fun ψ => (basis.representation ψ).character
      let deg : basis.index → ℤ := fun ψ => (Module.finrank ℂ (basis.representation ψ).vector : ℤ)
      (∃ σ υ g : G, IsAdaptedBase U a w σ υ g) ∧
      ∀ ζ : ℂ, IsPrimitiveRoot ζ m → ∀ θ : ℂ, IsPrimitiveRoot θ (2 * m) → θ ^ 2 = ζ →
      let ν : basis.index → ℕ → ℕ := fun χ t' =>
        Module.finrank ℂ (Module.End.eigenspace ((basis.representation χ).representation y)
          (θ ^ t'))
      let c : basis.index → ℕ → ℤ := fun χ r => (ν χ (2 * r) : ℤ) - ν χ (2 * r + m)
      let Y : ℕ → G → ℂ := fun r g =>
        ∑ χ ∈ B₀, (c χ r : ℂ) * (basis.representation χ).character g
      (∃ v : basis.index → ℕ → Fin 2 → ℂ, IsCentralSectionRows basis ideal principal a m
        (fun k => centralSylowPowerCentralizer n S e k) ΦN ε v) ∧
      ∀ v : basis.index → ℕ → Fin 2 → ℂ, IsCentralSectionRows basis ideal principal a m
        (fun k => centralSylowPowerCentralizer n S e k) ΦN ε v →
      let fc : basis.index → ℕ → ℂ := fun χ j => fourierTransform m ζ (fun k => v χ k 0) j
      let X : ℕ → G → ℂ := fun j => ∑ χ ∈ B₀, fc χ j • (basis.representation χ).character
      let Fs : ZMod m → basis.index → ℂ := fun j χ =>
        fourierTransform m ζ (fun k => v χ k 1) j.val
      ∀ (σb υb : U) (g : G), IsAdaptedBase U a w σb υb g →
      (∃ lam : ZMod m → ZMod m → U →* ℂ,
        ∀ i j, lam i j σb = ζ ^ i.val ∧ lam i j υb = ζ ^ j.val) ∧
      ∀ lam : ZMod m → ZMod m → U →* ℂ,
        (∀ i j, lam i j σb = ζ ^ i.val ∧ lam i j υb = ζ ^ j.val) →
      let tm : ZMod m → ZMod m → basis.index → ℂ := fun i j χ =>
        (Nat.card U : ℂ)⁻¹ * ∑ u : U, (basis.representation χ).character u * conj (lam i j u)
      let cb : ZMod m → ZMod m → basis.index → ℂ := fun i j χ =>
        tm 0 0 χ - tm i j χ + q₀ * (Fs i χ + Fs j χ + Fs (-i - j) χ)
      let C : G → ℂ := ∑ χ ∈ B₀, cb M M χ • (basis.representation χ).character
      let cf : ZMod m → ZMod m → G → ℂ := fun i j =>
        ∑ χ ∈ B₀, cb i j χ • (basis.representation χ).character
      let constituents : (Fin 3 → basis.index) → (Fin 3 → ℤ) → (Fin 3 → ℤ) → ℤ →
          (ℕ → basis.index) → ℕ → Fin 3 → Prop := fun α β η σ χ δ e₀ =>
        Function.Injective α ∧ (∀ i, α i ∈ B₀ ∧ α i ≠ principal) ∧
        (∀ i, β i = 1 ∨ β i = -1) ∧ (∀ i, η i = 1 ∨ η i = -1) ∧ (σ = 1 ∨ σ = -1) ∧
        Set.InjOn χ J ∧ (∀ j ∈ J, χ j ∈ B₀ ∧ χ j ≠ principal ∧ ∀ i, χ j ≠ α i) ∧ 0 < δ ∧
        η e₀ = -β e₀ ∧ (∀ i, i ≠ e₀ → η i = β i) ∧ (∀ i, η i = -β i → i = e₀) ∧
        Y 0 = 1 + ∑ i, (β i : ℂ) • (basis.representation (α i)).character ∧
        (∀ j ∈ J, X j = -1 + ∑ i, (η i : ℂ) • (basis.representation (α i)).character +
          (2 * σ : ℂ) • (basis.representation (χ j)).character) ∧
        (∀ j ∈ J, (basis.representation (χ j)).character 1 = δ) ∧
        1 + ∑ i, (β i : ℂ) * (basis.representation (α i)).character 1 = 0 ∧
        (σ * δ : ℂ) = 1 + β e₀ * (basis.representation (α e₀)).character 1 ∧
        β e₀ = σ ∧ (δ : ℂ) = (basis.representation (α e₀)).character 1 + σ
      (∃ (α : Fin 3 → basis.index) (β η : Fin 3 → ℤ) (σ : ℤ) (χ : ℕ → basis.index) (δ : ℕ)
          (e₀ : Fin 3), constituents α β η σ χ δ e₀) ∧
      ∀ (α : Fin 3 → basis.index) (β η : Fin 3 → ℤ) (σ : ℤ) (χ : ℕ → basis.index) (δ : ℕ)
          (e₀ : Fin 3), constituents α β η σ χ δ e₀ →
      let core : basis.index → Fin 3 → Fin 3 → ℤ → ℤ → Prop := fun ω iB iD τ₀ κ =>
        ω ∈ B₀ ∧ ω ≠ principal ∧ (∀ i, ω ≠ α i) ∧ (∀ j ∈ J, ω ≠ χ j) ∧
        iB ≠ e₀ ∧ iD ≠ e₀ ∧ iB ≠ iD ∧ (τ₀ = 1 ∨ τ₀ = -1) ∧ (κ = 1 ∨ κ = -1) ∧
        Y 0 = 1 + (σ : ℂ) • ch (α e₀) - (τ₀ : ℂ) • ch (α iB) + (κ : ℂ) • ch (α iD) ∧
        (∀ j ∈ J, X j = -1 - (σ : ℂ) • ch (α e₀) - (τ₀ : ℂ) • ch (α iB) +
          (κ : ℂ) • ch (α iD) + (2 * σ : ℂ) • ch (χ j)) ∧
        C = 1 - (σ : ℂ) • ch (α e₀) - (τ₀ : ℂ) • ch (α iB) - (κ : ℂ) • ch (α iD) +
          (2 * τ₀ : ℂ) • ch ω ∧
        deg ω = deg (α iB) - τ₀ ∧ 0 < deg (α iB) - τ₀
      let evenFamily : basis.index → Fin 3 → Fin 3 → ℤ → ℤ → (ℕ → Fin 4 → basis.index) →
          (ℕ → Fin 4 → ℤ) → Prop := fun ω iB iD τ₀ κ γ εs =>
        (∀ r ∈ Finset.Ico 1 M, ∀ l, γ r l ∈ B₀ ∧ (εs r l = 1 ∨ εs r l = -1)) ∧
        (∀ r ∈ Finset.Ico 1 M, Function.Injective (γ r)) ∧
        (∀ r ∈ Finset.Ico 1 M, ∀ r' ∈ Finset.Ico 1 M, r ≠ r' → ∀ l l', γ r l ≠ γ r' l') ∧
        (∀ r ∈ Finset.Ico 1 M, ∀ l, γ r l ≠ principal ∧ γ r l ≠ α e₀ ∧ γ r l ≠ α iB ∧
          γ r l ≠ α iD ∧ γ r l ≠ ω ∧ ∀ j ∈ J, γ r l ≠ χ j) ∧
        (∀ r ∈ Finset.Ico 1 M, X (m - 2 * r) = -1 - (σ : ℂ) • ch (α e₀) -
          (τ₀ : ℂ) • ch (α iB) + (κ : ℂ) • ch (α iD) + ∑ l, (εs r l : ℂ) • ch (γ r l)) ∧
        (∀ r ∈ Finset.Ico 1 M, Y r = (εs r 0 : ℂ) • ch (γ r 0) + (εs r 1 : ℂ) • ch (γ r 1) -
          (εs r 2 : ℂ) • ch (γ r 2) - (εs r 3 : ℂ) • ch (γ r 3)) ∧
        (∀ r ∈ Finset.Ico 1 M, εs r 0 * deg (γ r 0) + εs r 1 * deg (γ r 1) = σ * δ ∧
          εs r 2 * deg (γ r 2) + εs r 3 * deg (γ r 3) = σ * δ)
      (∃ (ω : basis.index) (iB iD : Fin 3) (τ₀ κ : ℤ) (γ : ℕ → Fin 4 → basis.index)
          (εs : ℕ → Fin 4 → ℤ), core ω iB iD τ₀ κ ∧ evenFamily ω iB iD τ₀ κ γ εs) ∧
      ∀ (ω : basis.index) (iB iD : Fin 3) (τ₀ κ : ℤ) (γ : ℕ → Fin 4 → basis.index)
          (εs : ℕ → Fin 4 → ℤ), core ω iB iD τ₀ κ → evenFamily ω iB iD τ₀ κ γ εs →
      let K : G → ℂ := 1 - (σ : ℂ) • ch (α e₀) + (2 * τ₀ : ℂ) • ch ω
      ∀ V : Finset (ZMod m × ZMod m), (∀ I ∈ V, (MulAction.orbit (dualGroup m) I).ncard = 6) →
        (∀ I, (MulAction.orbit (dualGroup m) I).ncard = 6 →
          ∃! I', I' ∈ V ∧ I' ∈ MulAction.orbit (dualGroup m) I) →
      let completeWitness : (ℕ → Fin 2 → basis.index) → (ℕ → Fin 2 → basis.index) →
          (ℕ → Fin 2) → (ZMod m × ZMod m → basis.index) → ℤ → ℤ → Prop :=
        fun P Q er ψ ρ₀ Δ =>
          (∀ r ∈ Finset.Ico 1 M, ({P r 0, Q r 0, P r 1, Q r 1} : Finset basis.index) =
              Finset.univ.image (γ r) ∧
            ∀ e', deg (P r e') = deg (α iB) ∧ deg (Q r e') = deg (α iD)) ∧
          (∀ r ∈ Finset.Ico 1 M, X (m - 2 * r) = -1 - (σ : ℂ) • ch (α e₀) -
            (τ₀ : ℂ) • ch (α iB) + (κ : ℂ) • ch (α iD) + (τ₀ : ℂ) • (ch (P r 0) + ch (P r 1)) -
            (κ : ℂ) • (ch (Q r 0) + ch (Q r 1))) ∧
          (∀ r ∈ Finset.Ico 1 M, Y r = (τ₀ : ℂ) • (ch (P r 0) - ch (P r 1)) -
            (κ : ℂ) • (ch (Q r 0) - ch (Q r 1))) ∧
          (∀ r ∈ Finset.Ico 1 M,
            cf r r = K - (τ₀ : ℂ) • ch (P r (er r)) - (κ : ℂ) • ch (Q r (er r)) ∧
            cf ((r + M : ℕ) : ZMod m) ((r + M : ℕ) : ZMod m) =
              K - (τ₀ : ℂ) • ch (P r (1 - er r)) - (κ : ℂ) • ch (Q r (1 - er r))) ∧
          (ρ₀ = 1 ∨ ρ₀ = -1) ∧ 0 < Δ ∧ ρ₀ * Δ = -(τ₀ * deg (α iB) + κ * deg (α iD)) ∧
          τ₀ * deg (α iB) + κ * deg (α iD) ≠ 0 ∧ Set.InjOn ψ ↑V ∧
          (∀ I ∈ V, ψ I ∈ B₀ ∧ ψ I ≠ principal ∧ ψ I ≠ α e₀ ∧ ψ I ≠ α iB ∧ ψ I ≠ α iD ∧
            ψ I ≠ ω ∧ (∀ j ∈ J, ψ I ≠ χ j) ∧ (∀ r ∈ Finset.Ico 1 M, ∀ l, ψ I ≠ γ r l) ∧
            cf I.1 I.2 = K + (ρ₀ : ℂ) • ch (ψ I) ∧ deg (ψ I) = Δ) ∧
          cf 0 0 = 0 ∧ cf M M = K - (τ₀ : ℂ) • ch (α iB) - (κ : ℂ) • ch (α iD) ∧
          (∀ I I' : ZMod m × ZMod m, I' ∈ MulAction.orbit (dualGroup m) I →
            cf I'.1 I'.2 = cf I.1 I.2) ∧
          (∀ I : ZMod m × ZMod m, I = (0, 0) ∨
            I ∈ MulAction.orbit (dualGroup m) ((M : ZMod m), (M : ZMod m)) ∨
            (∃ r ∈ Finset.Ico 1 M, I ∈ MulAction.orbit (dualGroup m) ((r : ZMod m), (r : ZMod m)) ∨
              I ∈ MulAction.orbit (dualGroup m)
                (((r + M : ℕ) : ZMod m), ((r + M : ℕ) : ZMod m))) ∨
            ∃ I' ∈ V, I ∈ MulAction.orbit (dualGroup m) I') ∧
          B₀ = ({principal, α e₀, α iB, α iD, ω} : Finset basis.index) ∪ J.image χ ∪
            ((Finset.Ico 1 M ×ˢ (Finset.univ : Finset (Fin 2))).image fun re => P re.1 re.2) ∪
            ((Finset.Ico 1 M ×ˢ (Finset.univ : Finset (Fin 2))).image fun re => Q re.1 re.2) ∪
            V.image ψ ∧
          B₀.card = (m ^ 2 + 12 * m + 8) / 6 ∧
          Multiset.map deg B₀.val = {1, deg (α e₀), deg (α iB), deg (α iD), deg (α iB) - τ₀} +
            Multiset.replicate M (δ : ℤ) + Multiset.replicate (m - 2) (deg (α iB)) +
            Multiset.replicate (m - 2) (deg (α iD)) +
            Multiset.replicate ((m - 1) * (m - 2) / 6) Δ
      (∃ (P Q : ℕ → Fin 2 → basis.index) (er : ℕ → Fin 2) (ψ : ZMod m × ZMod m → basis.index)
          (ρ₀ Δ : ℤ), completeWitness P Q er ψ ρ₀ Δ) ∧
      ∀ (P Q : ℕ → Fin 2 → basis.index) (er : ℕ → Fin 2) (ψ : ZMod m × ZMod m → basis.index)
          (ρ₀ Δ : ℤ), completeWitness P Q er ψ ρ₀ Δ →
      let Qd : ℤ := (q : ℤ) ^ 2 + ε * q + 1
      let x : G := a ^ M
      (σ = -ε ∧ τ₀ = 1 ∧ κ = ε ∧ ρ₀ = -ε) ∧
      (deg (α e₀) = (q : ℤ) ^ 3 ∧ deg (α iB) = Qd ∧ deg (α iD) = q * Qd ∧
        deg ω = q * (q + ε) ∧ (∀ j ∈ J, deg (χ j) = (q : ℤ) ^ 3 - ε) ∧
        (∀ r ∈ Finset.Ico 1 M, ∀ e', deg (P r e') = Qd ∧ deg (Q r e') = q * Qd) ∧
        (∀ I ∈ V, deg (ψ I) = (q + ε) * Qd) ∧ Δ = (q + ε) * Qd) ∧
      Multiset.map deg B₀.val = {1, (q : ℤ) ^ 3, q * (q + ε)} +
        Multiset.replicate (m - 1) Qd + Multiset.replicate (m - 1) (q * Qd) +
        Multiset.replicate M ((q : ℤ) ^ 3 - ε) +
        Multiset.replicate ((m - 1) * (m - 2) / 6) ((q + ε) * Qd) ∧
      (ch principal x = 1 ∧ ch (α e₀) x = q ∧ ch (α iB) x = 2 + ε * q ∧
        ch (α iD) x = 2 * q + ε ∧ ch ω x = 1 + ε * q ∧ (∀ j ∈ J, ch (χ j) x = ε - q) ∧
        (∀ r ∈ Finset.Ico 1 M, ∀ e', ch (P r e') x = (if Odd r then -ε * q else 2 + ε * q) ∧
          ch (Q r e') x = (if Odd r then -ε else 2 * q + ε)) ∧
        ∀ I ∈ V, ch (ψ I) x =
          if Even I.1.val ∧ Even I.2.val then 3 * (q + ε) else -(q + ε)) ∧
      (∀ I I' : ZMod m × ZMod m, I' ∈ MulAction.orbit (dualGroup m) I →
        (Even I'.1.val ∧ Even I'.2.val ↔ Even I.1.val ∧ Even I.2.val)) ∧
      (V.filter fun I => Even I.1.val ∧ Even I.2.val).card = (M - 1) * (M - 2) / 6 ∧
      (V.filter fun I => ¬ (Even I.1.val ∧ Even I.2.val)).card = m * (m - 2) / 8 ∧
      ∀ k ∈ Finset.Ico 1 m, ∀ z ∈ Subgroup.centralizer {a ^ k}, Odd (orderOf z) →
        ch (α e₀) (a ^ k * z) = ΦN z ∧ ch ω (a ^ k * z) = 1 + ε * ΦN z ∧
        ch (α iB) (a ^ k * z) = 1 + (-1) ^ k * (1 + ε * ΦN z) ∧
        ch (α iD) (a ^ k * z) = -ε + ε * (1 + (-1) ^ k) * (1 + ε * ΦN z) ∧
        ∀ j ∈ J, ch (χ j) (a ^ k * z) = (ΦN z - ε) * ζ ^ (-((j : ℤ) * k)) :=
  conditional_global_principal_degrees_and_involution_values_of_localHyp n hn S e p f hp hpodd hf
    (ConditionalLocalHyp.of_isSimpleGroup hnonab n hn S e hfour p f hp hpodd hf hmodel)
    ideal basis principal hprincipal

end CFSG.Wreathed.ConditionalGlobalDegrees

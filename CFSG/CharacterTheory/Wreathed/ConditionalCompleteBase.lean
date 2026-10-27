module

public import CFSG.CharacterTheory.Wreathed.ConditionalFiveFixed
public import CFSG.CharacterTheory.Wreathed.ConditionalCompleteBaseGram
public import CFSG.CharacterTheory.Wreathed.ConditionalCompleteBaseNonvanishing
public import CFSG.CharacterTheory.Wreathed.ConditionalCompleteBaseUnion
public import CFSG.CharacterTheory.Wreathed.ConditionalCompleteBaseTheorem

public section

open scoped BigOperators Classical ComplexConjugate

namespace CFSG.Wreathed.ConditionalCompleteBase

open CFSG.TwoRankLowerBound.Helpers CFSG.Semidihedral.Principal
  CFSG.ComponentClassification.CatalogueSchreierLinearTwo
  CFSG.Semidihedral.SemilinearOddExtensions CFSG.Wreathed.ActualProjectiveLayer
  CFSG.Wreathed.CyclicCentralSL2Extension CFSG.Wreathed.ConditionalFourier
  CFSG.Wreathed.AdaptedBaseFusion CFSG.Wreathed.ConditionalSquareRoot
  CFSG.Wreathed.ConditionalGeneralBase CFSG.Wreathed.ConditionalFirstFourierRows
  CFSG.Wreathed.ConditionalOddFourier CFSG.Wreathed.ConditionalFiveFixed

theorem conditional_complete_base_column_support_and_principal_block_exhaustion_of_localHyp
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
      ∃ (P Q : ℕ → Fin 2 → basis.index) (er : ℕ → Fin 2)
          (ψ : ZMod m × ZMod m → basis.index) (ρ₀ Δ : ℤ),
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
          Multiset.replicate ((m - 1) * (m - 2) / 6) Δ := by
  refine ⟨hloc.modelData, ?_⟩
  intro F _ _ Sigma b hSigma ρ Ψ hdata m M s t w a y U ΦH ΦN ε q q₀ B₀ J ch deg
  have hFF := (conditional_five_fixed_and_disjoint_even_constituent_families_of_localHyp n hn S e p
    f hp hpodd hf hloc ideal basis principal hprincipal).2 F Sigma b hSigma ρ Ψ hdata
  obtain ⟨-, horbit0, -, -, -, -, -, hadapt, hGBζ⟩ :=
    (conditional_general_base_integral_columns_and_second_row_reconstruction_of_localHyp n hn S e p
      f hp hpodd hf hloc ideal basis principal hprincipal).2 F Sigma b hSigma ρ Ψ hdata
  refine ⟨hadapt, fun ζ hζ θ hθ hθζ => ?_⟩
  intro ν c Y
  obtain ⟨hvex, hGBv⟩ := hGBζ ζ hζ θ hθ hθζ
  obtain ⟨-, -, -, -, -, -, -, hSR⟩ :=
    (conditional_square_root_cyclic_section_fourier_columns_and_parity_of_localHyp n hn S e p f hp
      hpodd hf hloc ideal basis principal hprincipal).2 F Sigma b hSigma ρ Ψ hdata
  obtain ⟨-, -, -, -, hY1, -, -, -, -, hallSR⟩ := hSR ζ hζ θ hθ hθζ
  refine ⟨hvex, fun v hv => ?_⟩
  intro fc X Fs σb υb g hg
  obtain ⟨hlamex, hGBlam⟩ := hGBv v hv σb υb g hg
  have hFFv := ((hFF.2 ζ hζ θ hθ hθζ).2 v hv σb υb g hg).2
  refine ⟨hlamex, fun lam hlam => ?_⟩
  intro tm cb C cf constituents
  obtain ⟨-, hcint, hc00, hsym, hcprin, hgramGB, hcX, hcY, -, hcdeg, -, -, hval, -, hcparE, -⟩ :=
    hGBlam lam hlam
  have hFFlam := hFFv lam hlam
  refine ⟨hFFlam.1, fun α β η σ χ δ e₀ hP => ?_⟩
  intro core evenFamily
  refine ⟨?_, fun ω iB iD τ₀ κ γ εs hcore heven => ?_⟩
  · obtain ⟨ω, iB, iD, τ₀, κ, hc, -, γ, εs, h1, h2, h3, h4, h5, h6, h7, -⟩ :=
      hFFlam.2 α β η σ χ δ e₀ hP
    exact ⟨ω, iB, iD, τ₀, κ, γ, εs, hc, h1, h2, h3, h4, h5, h6, h7⟩
  intro K V hV6 hVrep
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
  have hJm : ∀ j ∈ J, j ∈ Finset.Ico 1 m := fun j hj => (Finset.mem_filter.mp hj).1
  have hIco : ∀ r ∈ Finset.Ico 1 M, 0 < r ∧ r < M := fun r hr => by
    rw [Finset.mem_Ico] at hr
    omega
  have hkI : ∀ r ∈ Finset.Ico 1 M, m - 2 * r ∈ Finset.Ico 1 m := fun r hr => by
    have := hIco r hr
    rw [Finset.mem_Ico]
    omega
  have horbit0' : MulAction.orbit (dualGroup m) ((0 : ZMod m), (0 : ZMod m)) = {(0, 0)} :=
    horbit0
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
  have hV0 : ∀ I ∈ V, I ≠ (0, 0) := fun I hI h => by
    have h6 := hV6 I hI
    rw [h, horbit0'] at h6
    simp at h6
  have hF := baseFamily_of_columns (B := B₀) (p := principal) (yc := fun r φ => c φ r)
    (xc := cc) hm2 hM2 hJm cb Cz hCz'
    (fun j φ => fourierTransform m ζ (fun k => v φ k 0) j.val) hXc hS hQ hγdisj hV0 hcprin
    (hgramGB V hV6 hVrep) hcX hcY hcparE
  have ha : a ∈ Subgroup.centralizer ((S : Subgroup G) : Set G) :=
    wreathModelHom_a_mem_centralizer (by omega) S e
  have hnz : ∀ φ ∈ B₀, ch φ a ≠ 0 := fun φ hφ =>
    CFSG.LyonsUnitaryFour.principal_block_character_ne_zero_of_centralizes_sylow basis ideal 2
      principal hprincipal φ hφ S a ha
  have hnv : ∀ φ ∈ B₀, ∀ ξ : ℤ, Outside0 principal (α e₀) (α iB) (α iD) ω J χ φ →
      (∀ t ∈ Finset.Ico 1 M, ∀ l, φ ≠ γ t l) →
      (∀ t ∈ Finset.Ico 1 M, Cz t t φ = ξ ∧
        Cz ((t + M : ℕ) : ZMod m) ((t + M : ℕ) : ZMod m) φ = ξ) →
      (∀ I ∈ V, Cz I.1 I.2 φ = ξ) → False := by
    intro φ hφ ξ hout hγφ hdiag hgen
    obtain ⟨n1, n2, n3, n4, n5, n6⟩ := hout
    have hX0 : ∀ j ∈ Finset.Ico 1 m,
        fourierTransform m ζ (fun k => v φ k 0) ((j : ℕ) : ZMod m).val = 0 := by
      intro j hj
      rw [hXc j hj φ hφ]
      rcases Nat.even_or_odd j with ⟨k, hk⟩ | hjo
      · have hr : M - k ∈ Finset.Ico 1 M := by
          rw [Finset.mem_Ico] at hj ⊢
          omega
        have hj' : j = m - 2 * (M - k) := by
          rw [Finset.mem_Ico] at hj
          omega
        rw [hj', (hQ _ hr).hxk φ hφ, fixedPart_of_ne σ τ₀ κ n1 n2 n3 n4,
          Finset.sum_eq_zero fun l _ => by rw [unitVector_of_ne (hγφ _ hr l), mul_zero]]
        simp
      · have hjJ : j ∈ J := Finset.mem_filter.mpr ⟨hj, hjo⟩
        rw [hS.hxj j hjJ φ hφ, fixedPart_of_ne σ τ₀ κ n1 n2 n3 n4, unitVector_of_ne (n6 j hjJ)]
        simp
    have hCM : Cz M M φ = 0 := by
      rw [hS.hC φ hφ, unitVector_of_ne n1, unitVector_of_ne n2, unitVector_of_ne n3,
        unitVector_of_ne n4, unitVector_of_ne n5]
      ring
    have h := hval φ hφ 1 (Finset.mem_Ico.mpr ⟨le_rfl, by omega⟩) 1 (Subgroup.one_mem _)
      (by simp)
    have hzero := value_eq_zero_of_residual hm2 hM0 hζ (fun i j => cb i j φ)
      (fun i j => hsymb i j φ) (ξ : ℂ) (hc00' φ)
      (by show cb M M φ = 0; rw [hCz' _ _ φ hφ, hCM]; simp)
      (fun t ht => ⟨by show cb t t φ = (ξ : ℂ); rw [hCz' _ _ φ hφ, (hdiag t ht).1],
        by
          show cb ((t + M : ℕ) : ZMod m) ((t + M : ℕ) : ZMod m) φ = (ξ : ℂ)
          rw [hCz' _ _ φ hφ, (hdiag t ht).2]⟩)
      hVrep (fun I hI => by show cb I.1 I.2 φ = (ξ : ℂ); rw [hCz' _ _ φ hφ, hgen I hI])
      (fun j => fourierTransform m ζ (fun k => v φ k 0) ((j : ℕ) : ZMod m).val) hX0 h
    rw [pow_one, mul_one] at hzero
    exact hnz φ hφ hzero
  have hdpos : ∀ φ ∈ B₀, 0 < deg φ := fun φ _ => basisDegree_pos basis φ
  have hd1 : deg principal = 1 := basisDegree_principal basis hprincipal
  have hdc : ∀ ψ, ((deg ψ : ℤ) : ℂ) = ch ψ 1 := fun ψ => basisDegree_cast basis ψ
  have hdc' : ∀ ψ, ((deg ψ : ℤ) : ℂ) = (basis.representation ψ).character 1 := fun ψ =>
    basisDegree_cast basis ψ
  have hdω' : deg ω = deg (α iB) - τ₀ := hdω
  have hτ2 : τ₀ * τ₀ = 1 := by rcases hτ₀ with h | h <;> rw [h] <;> norm_num
  have hσ2 : σ * σ = 1 := by rcases hσ with h | h <;> rw [h] <;> norm_num
  have hY0deg : 1 + σ * deg (α e₀) - τ₀ * deg (α iB) + κ * deg (α iD) = 0 := by
    have h : Y 0 1 = 0 := hY1 0 hM0
    rw [hY0c] at h
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Pi.one_apply] at h
    rw [← hdc, ← hdc, ← hdc] at h
    exact_mod_cast h
  have hdχ : ∀ j ∈ J, deg (χ j) = (δ : ℤ) := fun j hj => by
    have h := hdegχ j hj
    rw [← hdc'] at h
    exact_mod_cast h
  have hδ' : (δ : ℤ) = deg (α e₀) + σ := by
    rw [← hdc'] at hδ
    exact_mod_cast hδ
  have hK1 : deg principal - σ * deg (α e₀) + 2 * τ₀ * deg ω =
      τ₀ * deg (α iB) + κ * deg (α iD) := by
    rw [hd1, hdω']
    linear_combination -hY0deg - 2 * hτ2
  have hσδ : σ * (δ : ℤ) = τ₀ * deg (α iB) - κ * deg (α iD) := by
    rw [hδ']
    linear_combination hσ2 + hY0deg
  have hpair : ∀ r ∈ Finset.Ico 1 M,
      εs r 0 * deg (γ r 0) + εs r 1 * deg (γ r 1) = τ₀ * deg (α iB) - κ * deg (α iD) ∧
        εs r 2 * deg (γ r 2) + εs r 3 * deg (γ r 3) = τ₀ * deg (α iB) - κ * deg (α iD) :=
    fun r hr => by
      rw [← hσδ]
      exact hγdeg r hr
  have hdegCz : ∀ i j, ∑ φ ∈ B₀, deg φ * Cz i j φ = 0 := by
    intro i j
    have h : ∑ χ ∈ B₀, cb i j χ * (basis.representation χ).character 1 = 0 := hcdeg i j
    have key : ((∑ φ ∈ B₀, deg φ * Cz i j φ : ℤ) : ℂ) =
        ∑ φ ∈ B₀, cb i j φ * (basis.representation φ).character 1 := by
      push_cast
      exact Finset.sum_congr rfl fun φ hφ => by rw [hCz' i j φ hφ, hdc', mul_comm]
    rw [← key] at h
    exact_mod_cast h
  have hdegd : ∀ r ∈ Finset.Ico 1 M, ∑ φ ∈ B₀, deg φ * Cz r r φ = 0 ∧
      ∑ φ ∈ B₀, deg φ * Cz ((r + M : ℕ) : ZMod m) ((r + M : ℕ) : ZMod m) φ = 0 :=
    fun r _ => ⟨hdegCz _ _, hdegCz _ _⟩
  have hdegg : ∀ I ∈ V, ∑ φ ∈ B₀, deg φ * Cz I.1 I.2 φ = 0 := fun I _ => hdegCz _ _
  have hJM' : M ≤ J.card := hJM.ge
  have hVcard : V.card = (m - 1) * (m - 2) / 6 := card_orbit_representatives_two_pow V hV6 hVrep
  have hVne : V.Nonempty := Finset.card_pos.mp (card_orbit_representatives_pos hn V hV6 hVrep)
  have hlab : ∀ r, ∃ P Q : Fin 2 → basis.index, r ∈ Finset.Ico 1 M →
      ((P 0 = γ r 0 ∧ Q 0 = γ r 1) ∨ (P 0 = γ r 1 ∧ Q 0 = γ r 0)) ∧
      ((P 1 = γ r 2 ∧ Q 1 = γ r 3) ∨ (P 1 = γ r 3 ∧ Q 1 = γ r 2)) ∧
      (∀ e', deg (P e') = deg (α iB) ∧ deg (Q e') = deg (α iD) ∧
        cc (m - 2 * r) (P e') = τ₀ ∧ cc (m - 2 * r) (Q e') = -κ) ∧
      (((∀ φ ∈ B₀, Cz r r φ = baseFixed principal (α e₀) ω σ τ₀ φ - τ₀ * unitVector (P 0) φ -
            κ * unitVector (Q 0) φ) ∧
          (∀ φ ∈ B₀, Cz ((r + M : ℕ) : ZMod m) ((r + M : ℕ) : ZMod m) φ =
            baseFixed principal (α e₀) ω σ τ₀ φ - τ₀ * unitVector (P 1) φ -
              κ * unitVector (Q 1) φ)) ∨
        ((∀ φ ∈ B₀, Cz r r φ = baseFixed principal (α e₀) ω σ τ₀ φ - τ₀ * unitVector (P 1) φ -
            κ * unitVector (Q 1) φ) ∧
          (∀ φ ∈ B₀, Cz ((r + M : ℕ) : ZMod m) ((r + M : ℕ) : ZMod m) φ =
            baseFixed principal (α e₀) ω σ τ₀ φ - τ₀ * unitVector (P 0) φ -
              κ * unitVector (Q 0) φ))) := by
    intro r
    by_cases hr : r ∈ Finset.Ico 1 M
    · obtain ⟨P, Q, h⟩ := hF.diag_labels hS hM2 hJM' hnv hdpos hK1 hpair hdegd hr
      exact ⟨P, Q, fun _ => h⟩
    · exact ⟨fun _ => principal, fun _ => principal, fun h => absurd h hr⟩
  choose P Q hPQ using hlab
  have her : ∀ r, ∃ e' : Fin 2, r ∈ Finset.Ico 1 M →
      (∀ φ ∈ B₀, Cz r r φ = baseFixed principal (α e₀) ω σ τ₀ φ -
        τ₀ * unitVector (P r e') φ - κ * unitVector (Q r e') φ) ∧
      (∀ φ ∈ B₀, Cz ((r + M : ℕ) : ZMod m) ((r + M : ℕ) : ZMod m) φ =
        baseFixed principal (α e₀) ω σ τ₀ φ - τ₀ * unitVector (P r (1 - e')) φ -
          κ * unitVector (Q r (1 - e')) φ) := by
    intro r
    by_cases hr : r ∈ Finset.Ico 1 M
    · rcases (hPQ r hr).2.2.2 with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact ⟨0, fun _ => ⟨h1, h2⟩⟩
      · exact ⟨1, fun _ => ⟨h1, h2⟩⟩
    · exact ⟨0, fun h => absurd h hr⟩
  choose er her using her
  have hmemPQ : ∀ r ∈ Finset.Ico 1 M, ∀ e', P r e' ∈ B₀ ∧ Q r e' ∈ B₀ := fun r hr e' => by
    obtain ⟨⟨l, hl⟩, ⟨l', hl'⟩⟩ :=
      (pair_labels_facts (hγinj r hr) (hPQ r hr).1 (hPQ r hr).2.1).2.2.2.1 e'
    rw [hl, hl']
    exact ⟨(hγε r hr l).1, (hγε r hr l').1⟩
  have hrel : ∀ r ∈ Finset.Ico 1 M,
      ∑ l, (εs r l : ℂ) • ch (γ r l) =
          (τ₀ : ℂ) • (ch (P r 0) + ch (P r 1)) - (κ : ℂ) • (ch (Q r 0) + ch (Q r 1)) ∧
        (εs r 0 : ℂ) • ch (γ r 0) + (εs r 1 : ℂ) • ch (γ r 1) - (εs r 2 : ℂ) • ch (γ r 2) -
          (εs r 3 : ℂ) • ch (γ r 3) =
          (τ₀ : ℂ) • (ch (P r 0) - ch (P r 1)) - (κ : ℂ) • (ch (Q r 0) - ch (Q r 1)) := by
    intro r hr
    have hx := (hQ r hr).xk_apply
    refine quad_relabel (hPQ r hr).1 (hPQ r hr).2.1 (fun e' l h => ?_) (fun e' l h => ?_) ch
    · rw [← hx l, ← h]
      exact ((hPQ r hr).2.2.1 e').2.2.1
    · rw [← hx l, ← h]
      exact ((hPQ r hr).2.2.1 e').2.2.2
  obtain ⟨ψ, ρ₀, Δ, hρ₀, hΔ, hρΔ, hψinj, hψ⟩ :=
    hF.generic_labels hS hM2 hJM' hnv hdpos hK1 hdegg hVne
  have hexh := hF.exhaustion hS hM2 hJM' hnv (ψ := ψ) fun I hI => (hψ I hI).2.2.2.2.1
  obtain ⟨hBunion, hBcard, hBmul⟩ := complete_base_union hS (fun r hr l => (hγε r hr l).1)
    hγinj (fun r hr l => (hQ r hr).core l) (fun r hr l => (hQ r hr).odd l) hγdisj
    (fun r hr => ⟨(hPQ r hr).1, (hPQ r hr).2.1⟩) hψinj
    (fun I hI => ⟨(hψ I hI).1, (hψ I hI).2.1, (hψ I hI).2.2.1⟩) hexh deg hdχ
    (fun r hr e' => ((hPQ r hr).2.2.1 e').1) (fun r hr e' => ((hPQ r hr).2.2.1 e').2.1)
    (fun I hI => (hψ I hI).2.2.2.1)
  refine ⟨P, Q, er, ψ, ρ₀, Δ, fun r hr => ⟨pair_labels_image (hPQ r hr).1 (hPQ r hr).2.1,
      fun e' => ⟨((hPQ r hr).2.2.1 e').1, ((hPQ r hr).2.2.1 e').2.1⟩⟩,
    fun r hr => ?_, fun r hr => ?_, fun r hr => ?_, hρ₀, hΔ, hρΔ, ?_, hψinj, fun I hI => ?_,
    ?_, ?_, ?_, fun I => orbit_cover hm2 hVrep I, hBunion, ?_, ?_⟩
  ·
    rw [hXk r hr, (hrel r hr).1, ← add_sub_assoc]
  ·
    rw [hYr r hr, (hrel r hr).2]
  ·
    obtain ⟨h1, h2⟩ := her r hr
    exact ⟨(hcfb _ _).trans ((basisCombination_congr B₀ h1).trans
        (basisCombination_diag hprincipal hP0 (hαB e₀) hωB (hmemPQ r hr _).1
          (hmemPQ r hr _).2 σ τ₀ κ)),
      (hcfb _ _).trans ((basisCombination_congr B₀ h2).trans
        (basisCombination_diag hprincipal hP0 (hαB e₀) hωB (hmemPQ r hr _).1
          (hmemPQ r hr _).2 σ τ₀ κ))⟩
  ·
    intro h0
    have h0' : ρ₀ * Δ = 0 := by rw [hρΔ, h0, neg_zero]
    rcases hρ₀ with h | h <;> rw [h] at h0' <;> omega
  ·
    obtain ⟨hψB, ⟨n1, n2, n3, n4, n5, n6⟩, hψγ, hψd, -, hrep⟩ := hψ I hI
    exact ⟨hψB, n1, n2, n3, n4, n5, n6, hψγ, (hcfb _ _).trans
      ((basisCombination_congr B₀ hrep).trans
        (basisCombination_gen hprincipal hP0 (hαB e₀) hωB hψB σ τ₀ ρ₀)), hψd⟩
  ·
    show ∑ χ ∈ B₀, cb 0 0 χ • (basis.representation χ).character = 0
    simp only [hc00', zero_smul, Finset.sum_const_zero]
  ·
    show C = 1 - (σ : ℂ) • ch (α e₀) + (2 * τ₀ : ℂ) • ch ω - (τ₀ : ℂ) • ch (α iB) -
      (κ : ℂ) • ch (α iD)
    rw [hCc]
    abel
  ·
    intro I I' hI'
    have hsymf : ∀ i j, cf i j = cf j i ∧ cf i j = cf j (-i - j) := fun i j =>
      ⟨Finset.sum_congr rfl fun χ _ => by rw [(hsymb i j χ).1],
        Finset.sum_congr rfl fun χ _ => by rw [(hsymb i j χ).2]⟩
    exact base_column_orbit_invariant cf hsymf hI'
  ·
    rw [hBcard, hJM, hVcard, ← card_formula hm2 hM2 (six_dvd_two_pow_sub_one_mul_sub_two n)]
    omega
  ·
    rw [hBmul, hd1, hdω', hJM, show 2 * (M - 1) = m - 2 by omega, hVcard]

theorem conditional_complete_base_column_support_and_principal_block_exhaustion
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
      ∃ (P Q : ℕ → Fin 2 → basis.index) (er : ℕ → Fin 2)
          (ψ : ZMod m × ZMod m → basis.index) (ρ₀ Δ : ℤ),
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
          Multiset.replicate ((m - 1) * (m - 2) / 6) Δ :=
  conditional_complete_base_column_support_and_principal_block_exhaustion_of_localHyp n hn S e p f
    hp hpodd hf
    (ConditionalLocalHyp.of_isSimpleGroup hnonab n hn S e hfour p f hp hpodd hf hmodel)
    ideal basis principal hprincipal

end CFSG.Wreathed.ConditionalCompleteBase

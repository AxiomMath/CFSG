module

public import CFSG.CharacterTheory.Wreathed.ConditionalFiveFixedCharacters
public import CFSG.CharacterTheory.Wreathed.ConditionalGeneralBase
public import CFSG.CharacterTheory.Wreathed.ConditionalFirstFourierRows
public import CFSG.CharacterTheory.Wreathed.ConditionalFiveFixedColumns

public section

open scoped BigOperators Classical ComplexConjugate

namespace CFSG.Wreathed.ConditionalFiveFixed

open CFSG.TwoRankLowerBound.Helpers CFSG.Semidihedral.Principal
  CFSG.ComponentClassification.CatalogueSchreierLinearTwo
  CFSG.Semidihedral.SemilinearOddExtensions CFSG.Wreathed.ActualProjectiveLayer
  CFSG.Wreathed.CyclicCentralSL2Extension CFSG.Wreathed.ConditionalFourier
  CFSG.Wreathed.AdaptedBaseFusion CFSG.Wreathed.ConditionalSquareRoot
  CFSG.Wreathed.ConditionalGeneralBase CFSG.Wreathed.ConditionalFirstFourierRows
  CFSG.Wreathed.ConditionalOddFourier

theorem conditional_five_fixed_and_disjoint_even_constituent_families_of_localHyp
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
      ∃ (ω : basis.index) (iB iD : Fin 3) (τ₀ κ : ℤ), core ω iB iD τ₀ κ ∧
        (∀ ω' iB' iD' τ₀' κ', core ω' iB' iD' τ₀' κ' →
          ω' = ω ∧ iB' = iB ∧ iD' = iD ∧ τ₀' = τ₀ ∧ κ' = κ) ∧
        ∃ (γ : ℕ → Fin 4 → basis.index) (εs : ℕ → Fin 4 → ℤ),
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
            εs r 2 * deg (γ r 2) + εs r 3 * deg (γ r 3) = σ * δ) ∧
          (∀ j ∈ Finset.Ico 1 m, fc (α e₀) j = -σ ∧ fc (α iB) j = -τ₀ ∧ fc (α iD) j = κ ∧
            fc ω j = 0 ∧ (∀ h ∈ J, fc (χ h) j = if j = h then 2 * σ else 0) ∧
            ∀ r ∈ Finset.Ico 1 M, ∀ l, fc (γ r l) j = if j = m - 2 * r then (εs r l : ℂ) else 0) ∧
          (∀ t ∈ Finset.Ico 1 M, c principal t = 0 ∧ c (α e₀) t = 0 ∧ c (α iB) t = 0 ∧
            c (α iD) t = 0 ∧ c ω t = 0 ∧ (∀ h ∈ J, c (χ h) t = 0) ∧
            ∀ φ ∈ B₀, (c φ t ≠ 0 ↔ ∃ l, φ = γ t l)) ∧
          c ω 0 = 0 ∧
          (∀ h : ℤ, Odd h → ∀ z ∈ Subgroup.centralizer ({y} : Set G), Odd (orderOf z) →
            ch ω (y ^ h * z) = 0 ∧ ch (α iB) (y ^ h * z) = -τ₀ ∧ ch (α iD) (y ^ h * z) = κ ∧
            ∀ r ∈ Finset.Ico 1 M, ∀ l : Fin 4,
              (l.val < 2 → ch (γ r l) (y ^ h * z) = εs r l * ζ ^ ((r : ℤ) * h)) ∧
              (2 ≤ l.val → ch (γ r l) (y ^ h * z) = -(εs r l) * ζ ^ ((r : ℤ) * h))) ∧
          (({principal, α e₀, α iB, α iD, ω} : Finset basis.index) ∪ J.image χ ∪
              ((Finset.Ico 1 M) ×ˢ (Finset.univ : Finset (Fin 4))).image
                (fun rl => γ rl.1 rl.2)) ⊆ B₀ ∧
          (({principal, α e₀, α iB, α iD, ω} : Finset basis.index) ∪ J.image χ ∪
              ((Finset.Ico 1 M) ×ˢ (Finset.univ : Finset (Fin 4))).image
                (fun rl => γ rl.1 rl.2)).card = 1 + 5 * M := by
  refine ⟨hloc.modelData, ?_⟩
  intro F _ _ Sigma b hSigma ρ Ψ hdata m M s t w a y U ΦH ΦN ε q q₀ B₀ J ch deg
  obtain ⟨-, -, -, -, -, -, -, hadapt, hGBζ⟩ :=
    (conditional_general_base_integral_columns_and_second_row_reconstruction_of_localHyp n hn S e p
      f hp hpodd hf hloc ideal basis principal hprincipal).2 F Sigma b hSigma ρ Ψ hdata
  refine ⟨hadapt, fun ζ hζ θ hθ hθζ => ?_⟩
  intro ν c Y
  obtain ⟨hvex, hGBv⟩ := hGBζ ζ hζ θ hθ hθζ
  refine ⟨hvex, fun v hv => ?_⟩
  intro fc X Fs σb υb g hg
  obtain ⟨hlamex, hGBlam⟩ := hGBv v hv σb υb g hg
  refine ⟨hlamex, fun lam hlam => ?_⟩
  intro tm cb C constituents
  obtain ⟨-, hcint, -, -, hcprin, hgramGB, hcX, hcY, -, hcdeg, -, -, -, -, -, hcpar⟩ :=
    hGBlam lam hlam
  obtain ⟨-, hFRv⟩ := (conditional_odd_constituent_complete_first_fourier_rows_of_localHyp n hn S e
    p f hp hpodd hf hloc ideal basis principal hprincipal).2 F Sigma b hSigma ρ Ψ hdata
    ζ hζ θ hθ hθζ
  obtain ⟨hex, hall⟩ := hFRv v hv
  refine ⟨?_, fun α β η σ χ δ e₀ hP => ?_⟩
  · obtain ⟨α, β, η, σ, χ, δ, e₀, hP, -, -⟩ := hex
    exact ⟨α, β, η, σ, χ, δ, e₀, hP⟩
  intro core
  obtain ⟨hχrow, hArow, hcχ, -, hcαr, -⟩ := hall α β η σ χ δ e₀ hP
  obtain ⟨hinj, hα, hβ, -, hσ, hχinj, hχ, -, hηe, hηi, -, hY0, hXj, hdegχ, -, -, hβe, -⟩ := hP
  obtain ⟨-, -, -, -, -, -, -, hSR⟩ :=
    (conditional_square_root_cyclic_section_fourier_columns_and_parity_of_localHyp n hn S e p f hp
      hpodd hf hloc ideal basis principal hprincipal).2 F Sigma b hSigma ρ Ψ hdata
  obtain ⟨hsec, -, -, hcgram, -, -, hcr, hfourc, -, hallSR⟩ := hSR ζ hζ θ hθ hθζ
  obtain ⟨Fc, hFc, horth, -, heven, -, hcard, -, -⟩ := hallSR v hv
  obtain ⟨v₀, -, -, huniq, -, -, -, -, hdeg, hprin, -, hsq, hgram⟩ :=
    (conditional_global_central_section_integral_fourier_columns_of_localHyp n hn S e p f hp hpodd
      hf hloc ideal basis principal hprincipal).2 F Sigma b hSigma ρ Ψ hdata ζ hζ
  have hP0 : principal ∈ B₀ := coefficientBlock_self_mem basis _ principal
  have hm4 : 4 ≤ m := by
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  have hm2 : m = 2 * M :=
    (Nat.two_mul_div_two_of_even ((Nat.even_pow' (by omega)).mpr even_two)).symm
  have hM2 : 2 ≤ M := by omega
  have hM0 : 0 < M := by omega
  let cc : ℕ → basis.index → ℤ := fun j χ => Fc χ j 0
  have hcc : ∀ j ∈ Finset.Ico 1 m, ∀ χ ∈ B₀, (cc j χ : ℂ) = fc χ j :=
    fun j hj χ hχ => hFc χ hχ j hj 0
  have hccF : ∀ j ∈ Finset.Ico 1 m, ∀ χ ∈ B₀,
      (cc j χ : ℂ) = fourierTransform m ζ (fun k => v₀ χ k 0) j := by
    intro j hj χ hχ
    rw [hcc j hj χ hχ]
    refine fourierTransform_congr (fun k hk => ?_) j
    rw [huniq χ hχ k hk (v χ k) fun r hr hodd => hv χ hχ k hk r hr hodd]
  have hgramZ : ∀ j ∈ Finset.Ico 1 m, ∀ t ∈ Finset.Ico 1 m,
      ∑ χ ∈ B₀, cc j χ * cc t χ = if j = t then 8 else 4 := by
    intro j hj t ht
    have key : ((∑ χ ∈ B₀, cc j χ * cc t χ : ℤ) : ℂ) = ∑ χ ∈ B₀,
        fourierTransform m ζ (fun k => v₀ χ k 0) j *
          fourierTransform m ζ (fun k => v₀ χ k 0) t := by
      push_cast
      exact Finset.sum_congr rfl fun χ hχ => by rw [hccF j hj χ hχ, hccF t ht χ hχ]
    by_cases hjt : j = t
    · subst hjt
      rw [ite_eq_left rfl]
      have h : ∑ χ ∈ B₀, fourierTransform m ζ (fun k => v₀ χ k 0) j ^ 2 = 8 := hsq j hj
      rw [show ∑ χ ∈ B₀, fourierTransform m ζ (fun k => v₀ χ k 0) j ^ 2 =
        ∑ χ ∈ B₀, fourierTransform m ζ (fun k => v₀ χ k 0) j *
          fourierTransform m ζ (fun k => v₀ χ k 0) j from
        Finset.sum_congr rfl fun _ _ => sq _, ← key] at h
      exact_mod_cast h
    · rw [ite_eq_right hjt]
      have h : ∑ χ ∈ B₀, fourierTransform m ζ (fun k => v₀ χ k 0) j *
          fourierTransform m ζ (fun k => v₀ χ k 0) t = 4 := hgram j hj t ht hjt
      rw [← key] at h
      exact_mod_cast h
  have hdegZ : ∀ j ∈ Finset.Ico 1 m, ∑ χ ∈ B₀, basisDegree basis χ * cc j χ = 0 := by
    intro j hj
    have h : ∑ χ ∈ B₀, (basis.representation χ).character 1 *
        fourierTransform m ζ (fun k => v₀ χ k 0) j = 0 := hdeg j hj 0
    have key : ((∑ χ ∈ B₀, basisDegree basis χ * cc j χ : ℤ) : ℂ) = ∑ χ ∈ B₀,
        (basis.representation χ).character 1 * fourierTransform m ζ (fun k => v₀ χ k 0) j := by
      push_cast
      exact Finset.sum_congr rfl fun χ hχ => by rw [basisDegree_cast, hccF j hj χ hχ]
    rw [← key] at h
    exact_mod_cast h
  have hprinZ : ∀ j ∈ Finset.Ico 1 m, cc j principal = -1 := by
    intro j hj
    have h : fourierTransform m ζ (fun k => v₀ principal k 0) j = -1 := (hprin j hj).1
    rw [← hccF j hj principal hP0] at h
    exact_mod_cast h
  have hydeg : ∀ r < M, ∑ χ ∈ B₀, basisDegree basis χ * c χ r = 0 := by
    intro r hr
    have h : Y r 1 = 0 := by
      obtain ⟨-, -, -, -, hY1, -⟩ := hSR ζ hζ θ hθ hθζ
      exact hY1 r hr
    have key : ((∑ χ ∈ B₀, basisDegree basis χ * c χ r : ℤ) : ℂ) = Y r 1 := by
      push_cast
      exact Finset.sum_congr rfl fun χ _ => by rw [basisDegree_cast, mul_comm]
    rw [← key] at h
    exact_mod_cast h
  have hαB : ∀ i, α i ∈ B₀ := fun i => (hα i).1
  have hJI : ∀ j ∈ J, j ∈ Finset.Ico 1 m := fun j hj => (Finset.mem_filter.mp hj).1
  have hy0 : ∀ φ ∈ B₀, c φ 0 = unitVector principal φ + ∑ i, β i * unitVector (α i) φ := by
    have h : basisCombination basis B₀ (fun χ => c χ 0) =
        basisCombination basis B₀ (unitVector principal + ∑ i, β i • unitVector (α i)) := by
      rw [basisCombination_principal_add_sum hprincipal hP0 hαB, ← hY0]
      exact basisCombination_eq_fun B₀ _
    intro φ hφ
    rw [eq_of_basisCombination_eq h hφ]
    simp only [Pi.add_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  have hcj : ∀ j ∈ J, ∀ φ ∈ B₀, cc j φ = -unitVector principal φ +
      ∑ i, η i * unitVector (α i) φ + 2 * σ * unitVector (χ j) φ := by
    intro j hj
    have hX : X j = basisCombination basis B₀ (cc j) :=
      Finset.sum_congr rfl fun χ hχ' => by rw [← hcc j (hJI j hj) χ hχ']
    have h : basisCombination basis B₀ (cc j) = basisCombination basis B₀
        (-unitVector principal + ∑ i, η i • unitVector (α i) + (2 * σ) • unitVector (χ j)) := by
      rw [basisCombination_neg_principal_add_sum_add hprincipal hP0 hαB (hχ j hj).1, ← hX,
        hXj j hj]
      push_cast
      rfl
    intro φ hφ
    rw [eq_of_basisCombination_eq h hφ]
    simp only [Pi.add_apply, Pi.neg_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  have hdχ : ∀ j ∈ J, basisDegree basis (χ j) = δ := by
    intro j hj
    have h := basisDegree_cast basis (χ j)
    rw [hdegχ j hj] at h
    exact_mod_cast h
  have hpar : ∀ r, 0 < r → r < M → ∀ φ ∈ B₀, cc (m - 2 * r) φ ≡ c φ 0 + c φ r [ZMOD 2] := by
    intro r hr0 hrM φ hφ
    refine heven (m - 2 * r) (by rw [Finset.mem_Ico]; omega) ⟨M - r, by omega⟩ r (by omega) hrM
      ?_ φ hφ
    rw [show r + (m - 2 * r) / 2 = M by omega, Nat.mod_self]
  have hMz : (M : ZMod m) ≠ 0 := by
    rw [Ne, ZMod.natCast_eq_zero_iff]
    intro h
    exact absurd (Nat.le_of_dvd hM0 h) (by omega)
  have hCex : ∀ φ, ∃ z : ℤ, φ ∈ B₀ → cb M M φ = z := fun φ => by
    by_cases hφ : φ ∈ B₀
    · obtain ⟨z, hz⟩ := hcint M M φ hφ
      exact ⟨z, fun _ => hz⟩
    · exact ⟨0, fun h => absurd h hφ⟩
  choose Cz hCz using hCex
  have hXval : ∀ j ∈ Finset.Ico 1 m, ∀ φ ∈ B₀,
      fourierTransform m ζ (fun k => v φ k 0) ((j : ℕ) : ZMod m).val = (cc j φ : ℂ) := by
    intro j hj φ hφ
    rw [ZMod.val_cast_of_lt (Finset.mem_Ico.mp hj).2, hcc j hj φ hφ]
  have hCsq : ∑ φ ∈ B₀, Cz φ * Cz φ = 8 := by
    have : NeZero m := ⟨by omega⟩
    obtain ⟨V, hV1, hV2⟩ := exists_orbit_representatives (K := dualGroup m)
      (X := ZMod m × ZMod m) (fun O => O.ncard = 6)
    have h : ∑ χ ∈ B₀, cb M M χ * conj (cb M M χ) = 8 := (hgramGB V hV1 hV2).1 M hMz
    rw [Finset.sum_congr rfl fun φ hφ => by rw [hCz φ hφ, map_intCast (starRingEnd ℂ)]] at h
    exact_mod_cast h
  have hCp : Cz principal = 1 := by
    have h : cb M M principal = 1 := hcprin M M fun h => hMz (Prod.ext_iff.mp h).1
    rw [hCz principal hP0] at h
    exact_mod_cast h
  have hCpar : ∀ φ ∈ B₀, Cz φ ≡ c φ 0 [ZMOD 2] := by
    intro φ hφ
    obtain ⟨k, hk⟩ : ∃ k : ℤ, cb M M φ - (c φ 0 : ℂ) = 2 * k := hcpar φ hφ
    rw [hCz φ hφ] at hk
    have hk' : Cz φ - c φ 0 = 2 * k := by exact_mod_cast hk
    exact Int.ModEq.symm (Int.modEq_iff_dvd.mpr ⟨k, hk'⟩)
  have hCx : ∀ j ∈ Finset.Ico 1 m, ∑ φ ∈ B₀, Cz φ * cc j φ = 0 := by
    intro j hj
    have h : ∑ χ ∈ B₀, cb M M χ *
        conj (fourierTransform m ζ (fun k => v χ k 0) ((j : ℕ) : ZMod m).val) = 0 :=
      hcX M M j hj
    rw [Finset.sum_congr rfl fun φ hφ => by
      rw [hCz φ hφ, hXval j hj φ hφ, map_intCast (starRingEnd ℂ)]] at h
    exact_mod_cast h
  have hCy : ∀ r < M, ∑ φ ∈ B₀, Cz φ * c φ r = 0 := by
    intro r hr
    have h : ∑ χ ∈ B₀, cb M M χ * (c χ r : ℂ) = 0 := hcY M M r hr
    rw [Finset.sum_congr rfl fun φ hφ => by rw [hCz φ hφ]] at h
    exact_mod_cast h
  have hCdeg : ∑ φ ∈ B₀, basisDegree basis φ * Cz φ = 0 := by
    have h : ∑ χ ∈ B₀, cb M M χ * (basis.representation χ).character 1 = 0 := hcdeg M M
    have key : ((∑ φ ∈ B₀, basisDegree basis φ * Cz φ : ℤ) : ℂ) =
        ∑ φ ∈ B₀, cb M M φ * (basis.representation φ).character 1 := by
      push_cast
      exact Finset.sum_congr rfl fun φ hφ => by rw [hCz φ hφ, basisDegree_cast, mul_comm]
    rw [← key] at h
    exact_mod_cast h
  obtain ⟨ω, iB, iD, τ₀, hωB, hωp, hωα, hωχ, hBe, hDe, hBD, hτ₀, hβB, hdω, hy0', hxJ', hCrep,
      hrows, hyrows, γ, εs, hγε, hdisj, hxγ, hyγ, hsub, hcardS⟩ :=
    five_fixed_columns (B := B₀) (p := principal) (y := fun r φ => c φ r) (x := cc) (C := Cz)
      (d := basisDegree basis) (δ := (δ : ℤ)) hm2 hM2 rfl hcard hP0
      (fun φ _ => basisDegree_pos basis φ) (basisDegree_principal basis hprincipal) hαB hinj
      (fun i => (hα i).2) hβ hσ (fun j hj => (hχ j hj).1) (fun j hj => (hχ j hj).2.1)
      (fun j hj => (hχ j hj).2.2) hχinj hηe hηi hβe hdχ hy0 hcj
      (fun t ht => by
        have h : fc (α e₀) t = -σ := hArow t ht
        rw [← hcc t ht (α e₀) (hαB e₀)] at h
        exact_mod_cast h)
      hcχ hcαr hcr (fun r hr => (hfourc r hr).2) (fun r hr => (hfourc r hr).1) hcgram hydeg
      hgramZ hdegZ hprinZ (fun r hr j hj => horth r hr j hj 0) hpar hCsq hCp hCpar hCx hCy hCdeg
  set κ := β iD with hκdef
  have hκ : κ = 1 ∨ κ = -1 := hβ iD
  have hAp := (hα e₀).2
  have hBp := (hα iB).2
  have hDp := (hα iD).2
  have hBA : α iB ≠ α e₀ := fun h => hBe (hinj h)
  have hDA : α iD ≠ α e₀ := fun h => hDe (hinj h)
  have hDB : α iD ≠ α iB := fun h => hBD (hinj h).symm
  have hIco : ∀ r ∈ Finset.Ico 1 M, 0 < r ∧ r < M := fun r hr => by
    rw [Finset.mem_Ico] at hr
    omega
  have hkI : ∀ r ∈ Finset.Ico 1 M, m - 2 * r ∈ Finset.Ico 1 m := fun r hr => by
    rw [Finset.mem_Ico] at hr ⊢
    omega
  have hch1 : ∀ x, ch principal x = 1 := fun x => by
    show (basis.representation principal).character x = 1
    rw [hprincipal, Pi.one_apply]
  have hXx : ∀ j ∈ Finset.Ico 1 m, ∀ x, X j x = ∑ φ ∈ B₀, (cc j φ : ℂ) * ch φ x := by
    intro j hj x
    show (∑ χ ∈ B₀, fc χ j • (basis.representation χ).character) x = _
    rw [Finset.sum_apply]
    exact Finset.sum_congr rfl fun φ hφ => by rw [Pi.smul_apply, smul_eq_mul, hcc j hj φ hφ]
  have hCx' : ∀ x, C x = ∑ φ ∈ B₀, (Cz φ : ℂ) * ch φ x := by
    intro x
    show (∑ χ ∈ B₀, cb M M χ • (basis.representation χ).character) x = _
    rw [Finset.sum_apply]
    exact Finset.sum_congr rfl fun φ hφ => by rw [Pi.smul_apply, smul_eq_mul, hCz φ hφ]
  have hYclass : Y 0 = 1 + (σ : ℂ) • ch (α e₀) - (τ₀ : ℂ) • ch (α iB) + (κ : ℂ) • ch (α iD) := by
    funext x
    show ∑ φ ∈ B₀, (c φ 0 : ℂ) * ch φ x = _
    rw [Finset.sum_congr rfl fun φ hφ => by
      rw [show (c φ 0 : ℂ) = ((1 * unitVector principal φ + σ * unitVector (α e₀) φ +
        (-τ₀) * unitVector (α iB) φ + κ * unitVector (α iD) φ : ℤ) : ℂ) by
          rw [hy0' φ hφ]; push_cast; ring],
      sum_cast_four_mul hP0 (hαB e₀) (hαB iB) (hαB iD)]
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Pi.one_apply, hch1]
    push_cast
    ring
  have hXclass : ∀ j ∈ J, X j = -1 - (σ : ℂ) • ch (α e₀) - (τ₀ : ℂ) • ch (α iB) +
      (κ : ℂ) • ch (α iD) + (2 * σ : ℂ) • ch (χ j) := by
    intro j hj
    funext x
    rw [hXx j (hJI j hj), Finset.sum_congr rfl fun φ hφ => by
      rw [show (cc j φ : ℂ) = (((-1) * unitVector principal φ + (-σ) * unitVector (α e₀) φ +
        (-τ₀) * unitVector (α iB) φ + κ * unitVector (α iD) φ +
          (2 * σ) * unitVector (χ j) φ : ℤ) : ℂ) by
          rw [hxJ' j hj φ hφ, fixedPart]; push_cast; ring],
      sum_cast_five_mul hP0 (hαB e₀) (hαB iB) (hαB iD) (hχ j hj).1]
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Pi.neg_apply,
      Pi.one_apply, hch1]
    push_cast
    ring
  have hCclass : C = 1 - (σ : ℂ) • ch (α e₀) - (τ₀ : ℂ) • ch (α iB) - (κ : ℂ) • ch (α iD) +
      (2 * τ₀ : ℂ) • ch ω := by
    funext x
    rw [hCx', Finset.sum_congr rfl fun φ hφ => by
      rw [show (Cz φ : ℂ) = ((1 * unitVector principal φ + (-σ) * unitVector (α e₀) φ +
        (-τ₀) * unitVector (α iB) φ + (-κ) * unitVector (α iD) φ +
          (2 * τ₀) * unitVector ω φ : ℤ) : ℂ) by
          rw [hCrep φ hφ]; push_cast; ring],
      sum_cast_five_mul hP0 (hαB e₀) (hαB iB) (hαB iD) hωB]
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Pi.one_apply, hch1]
    push_cast
    ring
  have hdegω : deg ω = deg (α iB) - τ₀ := hdω
  have hdegpos : 0 < deg (α iB) - τ₀ := by
    rw [← hdegω]
    exact basisDegree_pos basis ω
  refine ⟨ω, iB, iD, τ₀, κ, ⟨hωB, hωp, hωα, hωχ, hBe, hDe, hBD, hτ₀, hκ, hYclass, hXclass,
    hCclass, hdegω, hdegpos⟩, ?_, ?_⟩
  ·
    rintro ω' iB' iD' τ₀' κ' ⟨hω'B, hω'p, hω'α, -, hB'e, hD'e, hB'D', -, -, hY', -, hC', -, -⟩
    have hy' : ∀ φ ∈ B₀, c φ 0 = unitVector principal φ + σ * unitVector (α e₀) φ -
        τ₀' * unitVector (α iB') φ + κ' * unitVector (α iD') φ := by
      have h : basisCombination basis B₀ (fun φ => c φ 0) = basisCombination basis B₀
          (fun φ => 1 * unitVector principal φ + σ * unitVector (α e₀) φ +
            (-τ₀') * unitVector (α iB') φ + κ' * unitVector (α iD') φ) := by
        rw [basisCombination_eq_fun, basisCombination_eq_fun]
        funext x
        rw [sum_cast_four_mul hP0 (hαB e₀) (hαB iB') (hαB iD')]
        have hx := congrFun hY' x
        change ∑ φ ∈ B₀, (c φ 0 : ℂ) * ch φ x = _ at hx
        rw [hx]
        simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Pi.one_apply, ch,
          hprincipal]
        push_cast
        ring
      intro φ hφ
      rw [eq_of_basisCombination_eq h hφ]
      ring
    have hC'' : ∀ φ ∈ B₀, Cz φ = unitVector principal φ - σ * unitVector (α e₀) φ -
        τ₀' * unitVector (α iB') φ - κ' * unitVector (α iD') φ +
          2 * τ₀' * unitVector ω' φ := by
      have h : basisCombination basis B₀ Cz = basisCombination basis B₀
          (fun φ => 1 * unitVector principal φ + (-σ) * unitVector (α e₀) φ +
            (-τ₀') * unitVector (α iB') φ + (-κ') * unitVector (α iD') φ +
              (2 * τ₀') * unitVector ω' φ) := by
        rw [basisCombination_eq_fun, basisCombination_eq_fun]
        funext x
        rw [sum_cast_five_mul hP0 (hαB e₀) (hαB iB') (hαB iD') hω'B]
        have hx := hCx' x
        rw [hC'] at hx
        change _ = ∑ φ ∈ B₀, (Cz φ : ℂ) * (basis.representation φ).character x at hx
        rw [← hx]
        simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Pi.one_apply, ch,
          hprincipal]
        push_cast
        ring
      intro φ hφ
      rw [eq_of_basisCombination_eq h hφ]
      ring
    exact five_core_unique (B := B₀) (p := principal) (y₀ := fun φ => c φ 0) (C := Cz) hαB hinj
      (fun i => (hα i).2) hBe hDe hBD hB'e hD'e hB'D' hωB hωp hωα hω'p hω'α hτ₀ hy0' hy' hCrep
      hC''
  have hγB : ∀ r ∈ Finset.Ico 1 M, ∀ l, γ r l ∈ B₀ := fun r hr l =>
    (hγε r (hIco r hr).1 (hIco r hr).2).2.1 l
  have hsecφ : ∀ φ ∈ B₀, ∀ h : ℤ, Odd h → ∀ z ∈ Subgroup.centralizer ({y} : Set G),
      Odd (orderOf z) →
      ch φ (y ^ h * z) = ∑ r ∈ Finset.range M, (c φ r : ℂ) * ζ ^ ((r : ℤ) * h) := by
    intro φ hφ h hh z hz hzodd
    obtain ⟨h1, h2⟩ := hsec φ hφ h hh z hz hzodd
    have h2' : (basis.representation φ).character (y ^ h) =
        ∑ r ∈ Finset.range M, (c φ r : ℂ) * ζ ^ ((r : ℤ) * h) := h2
    show (basis.representation φ).character (y ^ h * z) = _
    rw [h1, h2']
  have hy0core : c (α iB) 0 = -τ₀ ∧ c (α iD) 0 = κ ∧ c ω 0 = 0 := by
    refine ⟨?_, ?_, ?_⟩
    · rw [hy0' _ (hαB iB)]
      simp [unitVector, hBp, hBA, hDB.symm]
    · rw [hy0' _ (hαB iD)]
      simp [unitVector, hDp, hDA, hDB]
    · rw [hy0' _ hωB]
      simp [unitVector, hωp, hωα]
  refine ⟨γ, εs, fun r hr l => ⟨hγB r hr l, (hγε r (hIco r hr).1 (hIco r hr).2).2.2.1 l⟩,
    fun r hr => (hγε r (hIco r hr).1 (hIco r hr).2).1,
    fun r hr r' hr' hrr' => hdisj r r' (hIco r hr).1 (hIco r hr).2 (hIco r' hr').1
      (hIco r' hr').2 hrr', fun r hr l => ?_, fun r hr => ?_, fun r hr => ?_,
    fun r hr => (hγε r (hIco r hr).1 (hIco r hr).2).2.2.2.2.2.2.2, fun j hj => ?_,
    fun t ht => ?_, hy0core.2.2, fun h hh z hz hzodd => ?_, hsub, hcardS⟩
  ·
    obtain ⟨c1, c2, c3, c4⟩ := (hγε r (hIco r hr).1 (hIco r hr).2).2.2.2.2.2.2.1 l
    exact ⟨c1, c2 e₀, c2 iB, c2 iD, c3, c4⟩
  ·
    obtain ⟨-, hBr, -, -, -, hxr, -, -, -⟩ := hγε r (hIco r hr).1 (hIco r hr).2
    funext x
    rw [hXx _ (hkI r hr), Finset.sum_congr rfl fun φ hφ => by rw [hxr φ hφ]]
    simp only [Int.cast_add, add_mul, Finset.sum_add_distrib]
    rw [sum_cast_fixedPart_mul hP0 (hαB e₀) (hαB iB) (hαB iD),
      sum_cast_lincomb_mul hBr]
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Pi.neg_apply,
      Pi.one_apply, hch1, Finset.sum_apply]
  ·
    obtain ⟨-, hBr, -, -, hyr, -, -, -, -⟩ := hγε r (hIco r hr).1 (hIco r hr).2
    funext x
    show ∑ φ ∈ B₀, (c φ r : ℂ) * ch φ x = _
    rw [Finset.sum_congr rfl fun φ hφ => by rw [hyr φ hφ], sum_cast_lincomb_mul hBr,
      Fin.sum_univ_four, quadSign_zero, quadSign_one, quadSign_two, quadSign_three]
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    push_cast
    ring
  ·
    have hcf : ∀ φ ∈ B₀, fc φ j = (cc j φ : ℂ) := fun φ hφ => (hcc j hj φ hφ).symm
    refine ⟨hArow j hj, ?_, ?_, ?_, fun h hh => hχrow h hh j hj, fun r hr l => ?_⟩
    · rw [hcf _ (hαB iB), (hrows j hj).1]
      push_cast
      ring
    · rw [hcf _ (hαB iD), (hrows j hj).2.1]
    · rw [hcf _ hωB, (hrows j hj).2.2]
      push_cast
      ring
    · rw [hcf _ (hγB r hr l), hxγ r (hIco r hr).1 (hIco r hr).2 l j hj]
      split_ifs <;> push_cast <;> rfl
  ·
    have htM := hIco t ht
    obtain ⟨-, -, -, hsupp, -, -, -, -, -⟩ := hγε t htM.1 htM.2
    exact ⟨hcr t htM.1 htM.2, hcαr t htM.1 htM.2, (hyrows t htM.1 htM.2).1,
      (hyrows t htM.1 htM.2).2.1, (hyrows t htM.1 htM.2).2.2,
      fun h hh => hcχ h hh t htM.2, hsupp⟩
  ·
    have hrange : ∀ φ ∈ B₀, (∀ r, 0 < r → r < M → c φ r = 0) →
        ch φ (y ^ h * z) = c φ 0 := by
      intro φ hφ h0
      rw [hsecφ φ hφ h hh z hz hzodd, Finset.sum_eq_single 0 (fun r hr hr0 => by
          rw [h0 r (Nat.pos_of_ne_zero hr0) (Finset.mem_range.mp hr), Int.cast_zero, zero_mul])
        fun h0' => absurd (Finset.mem_range.mpr hM0) h0']
      simp
    refine ⟨?_, ?_, ?_, fun r hr l => ?_⟩
    · rw [hrange ω hωB fun r h1 h2 => (hyrows r h1 h2).2.2, hy0core.2.2, Int.cast_zero]
    · rw [hrange (α iB) (hαB iB) fun r h1 h2 => (hyrows r h1 h2).1, hy0core.1, Int.cast_neg]
    · rw [hrange (α iD) (hαB iD) fun r h1 h2 => (hyrows r h1 h2).2.1, hy0core.2.1]
    · have hval : ch (γ r l) (y ^ h * z) = (quadSign l * εs r l : ℤ) * ζ ^ ((r : ℤ) * h) := by
        rw [hsecφ _ (hγB r hr l) h hh z hz hzodd, Finset.sum_eq_single r (fun t ht htr => by
            rw [hyγ r (hIco r hr).1 (hIco r hr).2 l t (Finset.mem_range.mp ht), ite_eq_right htr,
              Int.cast_zero, zero_mul])
          fun h0 => absurd (Finset.mem_range.mpr (hIco r hr).2) h0,
          hyγ r (hIco r hr).1 (hIco r hr).2 l r (hIco r hr).2, ite_eq_left rfl]
      refine ⟨fun hl => ?_, fun hl => ?_⟩
      · rw [hval, quadSign, ite_eq_left_iff.mpr fun h => absurd hl h]
        push_cast
        ring
      · rw [hval, quadSign, ite_eq_right_iff.mpr fun h => absurd h (by omega)]
        push_cast
        ring

theorem conditional_five_fixed_and_disjoint_even_constituent_families
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
      ∃ (ω : basis.index) (iB iD : Fin 3) (τ₀ κ : ℤ), core ω iB iD τ₀ κ ∧
        (∀ ω' iB' iD' τ₀' κ', core ω' iB' iD' τ₀' κ' →
          ω' = ω ∧ iB' = iB ∧ iD' = iD ∧ τ₀' = τ₀ ∧ κ' = κ) ∧
        ∃ (γ : ℕ → Fin 4 → basis.index) (εs : ℕ → Fin 4 → ℤ),
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
            εs r 2 * deg (γ r 2) + εs r 3 * deg (γ r 3) = σ * δ) ∧
          (∀ j ∈ Finset.Ico 1 m, fc (α e₀) j = -σ ∧ fc (α iB) j = -τ₀ ∧ fc (α iD) j = κ ∧
            fc ω j = 0 ∧ (∀ h ∈ J, fc (χ h) j = if j = h then 2 * σ else 0) ∧
            ∀ r ∈ Finset.Ico 1 M, ∀ l, fc (γ r l) j = if j = m - 2 * r then (εs r l : ℂ) else 0) ∧
          (∀ t ∈ Finset.Ico 1 M, c principal t = 0 ∧ c (α e₀) t = 0 ∧ c (α iB) t = 0 ∧
            c (α iD) t = 0 ∧ c ω t = 0 ∧ (∀ h ∈ J, c (χ h) t = 0) ∧
            ∀ φ ∈ B₀, (c φ t ≠ 0 ↔ ∃ l, φ = γ t l)) ∧
          c ω 0 = 0 ∧
          (∀ h : ℤ, Odd h → ∀ z ∈ Subgroup.centralizer ({y} : Set G), Odd (orderOf z) →
            ch ω (y ^ h * z) = 0 ∧ ch (α iB) (y ^ h * z) = -τ₀ ∧ ch (α iD) (y ^ h * z) = κ ∧
            ∀ r ∈ Finset.Ico 1 M, ∀ l : Fin 4,
              (l.val < 2 → ch (γ r l) (y ^ h * z) = εs r l * ζ ^ ((r : ℤ) * h)) ∧
              (2 ≤ l.val → ch (γ r l) (y ^ h * z) = -(εs r l) * ζ ^ ((r : ℤ) * h))) ∧
          (({principal, α e₀, α iB, α iD, ω} : Finset basis.index) ∪ J.image χ ∪
              ((Finset.Ico 1 M) ×ˢ (Finset.univ : Finset (Fin 4))).image
                (fun rl => γ rl.1 rl.2)) ⊆ B₀ ∧
          (({principal, α e₀, α iB, α iD, ω} : Finset basis.index) ∪ J.image χ ∪
              ((Finset.Ico 1 M) ×ˢ (Finset.univ : Finset (Fin 4))).image
                (fun rl => γ rl.1 rl.2)).card = 1 + 5 * M :=
  conditional_five_fixed_and_disjoint_even_constituent_families_of_localHyp n hn S e p f hp hpodd hf
    (ConditionalLocalHyp.of_isSimpleGroup hnonab n hn S e hfour p f hp hpodd hf hmodel)
    ideal basis principal hprincipal

end CFSG.Wreathed.ConditionalFiveFixed

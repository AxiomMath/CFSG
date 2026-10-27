module

public import CFSG.CharacterTheory.Wreathed.ConditionalEveryFlatDegrees

public section

open scoped BigOperators Classical ComplexConjugate

namespace CFSG.Wreathed

open CFSG.TwoRankLowerBound.Helpers CFSG.Semidihedral.Principal
  CFSG.ComponentClassification.CatalogueSchreierLinearTwo
  CFSG.Semidihedral.SemilinearOddExtensions CFSG.Wreathed.ActualProjectiveLayer
  CFSG.Wreathed.FullDefectLabels CFSG.Wreathed.ConditionalFourier
  CFSG.Wreathed.FlatCentralFourier CFSG.Wreathed.AdaptedBaseFusion
  CFSG.Wreathed.ConditionalGeneralBase

theorem conditional_every_flat_block_has_one_linear_character
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
    let m : ℕ := 2 ^ n
    let M : ℕ := m / 2
    let q : ℕ := p ^ f
    let ε : ℤ := if q % 4 = 1 then 1 else -1
    let Qd : ℤ := (q : ℤ) ^ 2 + ε * q + 1
    let BB := coefficientBlock basis (localizedComplexIntegerRing ideal) B
    let deg : basis.index → ℤ := fun χ => (Module.finrank ℂ (basis.representation χ).vector : ℤ)
    (∃! χ, χ ∈ BB ∧ deg χ = 1) ∧
    (∀ χ ∈ BB, deg χ = 1 → (basis.representation χ).character = 1) ∧
    Multiset.map deg BB.val = {1, (q : ℤ) ^ 3, q * (q + ε)} + Multiset.replicate (m - 1) Qd +
      Multiset.replicate (m - 1) (q * Qd) + Multiset.replicate M ((q : ℤ) ^ 3 - ε) +
      Multiset.replicate ((m - 1) * (m - 2) / 6) ((q + ε) * Qd) ∧
    (∀ principal : basis.index, (basis.representation principal).character = 1 →
      BB = coefficientBlock basis (localizedComplexIntegerRing ideal) principal ∧
      FlatWreathedBlock basis ideal S e principal) ∧
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
      let J : Finset ℕ := (Finset.Ico 1 m).filter Odd
      let deg : basis.index → ℤ := fun χ => (Module.finrank ℂ (basis.representation χ).vector : ℤ)
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
      (∃ V : Finset (ZMod m × ZMod m), (∀ I ∈ V, (MulAction.orbit K I).ncard = 6) ∧
        ∀ I, (MulAction.orbit K I).ncard = 6 → ∃! I', I' ∈ V ∧ I' ∈ MulAction.orbit K I) ∧
      ∀ V : Finset (ZMod m × ZMod m), (∀ I ∈ V, (MulAction.orbit K I).ncard = 6) →
        (∀ I, (MulAction.orbit K I).ncard = 6 → ∃! I', I' ∈ V ∧ I' ∈ MulAction.orbit K I) →
      let complete : ℤ → ℤ → ℤ → ℤ → ℤ → ℤ → ℤ → ℤ → basis.index → basis.index → basis.index →
          basis.index → basis.index → (ℕ → basis.index) → (ℕ → Fin 2 → basis.index) →
          (ℕ → Fin 2 → basis.index) → (ZMod m × ZMod m → basis.index) → ℤ → ℤ → Prop :=
        fun δ₀ δ₁ δ₂ δ₃ δ₄ α β γ χ₀ χ₁ χ₂ χ₃ χ₄ ξ P Q ψ D Δ =>
          let Acol : basis.index → ℤ :=
            (Pi.single χ₀ δ₀ : basis.index → ℤ) + Pi.single χ₁ δ₁ + Pi.single χ₂ δ₂ +
              Pi.single χ₃ δ₃
          let Kc : basis.index → ℤ :=
            (Pi.single χ₀ δ₀ : basis.index → ℤ) - Pi.single χ₁ δ₁ + Pi.single χ₄ (2 * δ₄)
          let Xodd : ℕ → basis.index → ℤ := fun h => Acol + Pi.single (ξ h) (2 * α)
          let Yzero : basis.index → ℤ :=
            β • ((Pi.single χ₀ δ₀ : basis.index → ℤ) + Pi.single χ₁ δ₁ - Pi.single χ₂ δ₂ -
              Pi.single χ₃ δ₃)
          let Cmid : basis.index → ℤ := Kc + Pi.single χ₂ δ₂ - Pi.single χ₃ δ₃
          let Xeven : ℕ → basis.index → ℤ := fun r => Acol - Pi.single (P r 0) δ₂ -
            Pi.single (P r 1) δ₂ - Pi.single (Q r 0) δ₃ - Pi.single (Q r 1) δ₃
          let Yeven : ℕ → basis.index → ℤ := fun r => -(Pi.single (P r 0) δ₂ : basis.index → ℤ) +
            Pi.single (P r 1) δ₂ - Pi.single (Q r 0) δ₃ + Pi.single (Q r 1) δ₃
          let Cdiag : ℕ → Fin 2 → basis.index → ℤ := fun r er =>
            Kc + Pi.single (P r er) δ₂ - Pi.single (Q r er) δ₃
          let Cgen : ZMod m × ZMod m → basis.index → ℤ := fun I => Kc + Pi.single (ψ I) γ
          let core : Finset basis.index := {χ₀, χ₁, χ₂, χ₃, χ₄}
          let evenFam : Finset basis.index :=
            ((Finset.Ico 1 M) ×ˢ (Finset.univ : Finset (Fin 2))).image (fun x => P x.1 x.2) ∪
              ((Finset.Ico 1 M) ×ˢ (Finset.univ : Finset (Fin 2))).image (fun x => Q x.1 x.2)
          (∀ sgn ∈ [δ₀, δ₁, δ₂, δ₃, δ₄, α, β, γ], sgn = 1 ∨ sgn = -1) ∧
          Function.Injective ![χ₀, χ₁, χ₂, χ₃, χ₄] ∧ Set.InjOn ξ J ∧
          (∀ r ∈ Finset.Ico 1 M, ∀ r' ∈ Finset.Ico 1 M, ∀ er er' : Fin 2,
            (P r er = P r' er' → r = r' ∧ er = er') ∧ (Q r er = Q r' er' → r = r' ∧ er = er') ∧
              P r er ≠ Q r' er') ∧
          Set.InjOn ψ V ∧
          (∀ h ∈ J, ξ h ∉ core) ∧
          (∀ r ∈ Finset.Ico 1 M, ∀ er, P r er ∉ core ∧ Q r er ∉ core ∧ P r er ∉ J.image ξ ∧
            Q r er ∉ J.image ξ) ∧
          (∀ I ∈ V, ψ I ∉ core ∧ ψ I ∉ J.image ξ ∧ ψ I ∉ evenFam) ∧
          (∀ h ∈ J, ∀ χ ∈ BB, X h χ = Xodd h χ) ∧
          (∀ χ ∈ BB, Y 0 χ = Yzero χ) ∧
          (∀ χ ∈ BB, c M M χ = Cmid χ) ∧
          (∀ r ∈ Finset.Ico 1 M, ∀ χ ∈ BB, X (-(2 * (r : ZMod m))) χ = Xeven r χ) ∧
          (∀ r ∈ Finset.Ico 1 M, ∀ χ ∈ BB, Y r χ = Yeven r χ) ∧
          (∀ r ∈ Finset.Ico 1 M, ∃ er : Fin 2, (∀ χ ∈ BB, c r r χ = Cdiag r er χ) ∧
            ∀ χ ∈ BB, c (r + M) (r + M) χ = Cdiag r (1 - er) χ) ∧
          (∀ I ∈ V, ∀ χ ∈ BB, c I.1 I.2 χ = Cgen I χ) ∧
          ((∀ χ ∈ BB, c 0 0 χ = 0 ∧ X 0 χ = 0 ∧ Fs 0 χ = 0) ∧
            (∀ I I' : ZMod m × ZMod m, I' ∈ MulAction.orbit K I → ∀ χ ∈ BB,
              c I'.1 I'.2 χ = c I.1 I.2 χ) ∧
            (∀ j : ZMod m, j = 0 ∨ (∃ h ∈ J, j = h) ∨
              ∃ r ∈ Finset.Ico 1 M, j = -(2 * (r : ZMod m))) ∧
            (∀ I : ZMod m × ZMod m, I = (0, 0) ∨
              I ∈ MulAction.orbit K ((M : ZMod m), (M : ZMod m)) ∨
              (∃ r ∈ Finset.Ico 1 M, I ∈ MulAction.orbit K ((r : ZMod m), (r : ZMod m)) ∨
                I ∈ MulAction.orbit K ((r : ZMod m) + M, (r : ZMod m) + M)) ∨
              ∃ I' ∈ V, I ∈ MulAction.orbit K I') ∧
            ∀ j : ZMod m, ∀ χ ∈ BB, X j χ + 2 * Fs j χ = Cl 0 χ - Cl (-j) χ) ∧
          (0 < deg χ₀ ∧ 0 < deg χ₁ ∧ 0 < deg χ₂ ∧ 0 < deg χ₃ ∧ 0 < deg χ₄) ∧
          0 < D ∧ 0 < Δ ∧
          (∀ h ∈ J, deg (ξ h) = D) ∧
          (∀ r ∈ Finset.Ico 1 M, ∀ er, deg (P r er) = deg χ₂ ∧ deg (Q r er) = deg χ₃) ∧
          (∀ I ∈ V, deg (ψ I) = Δ) ∧
          δ₀ * deg χ₀ + δ₁ * deg χ₁ = -(α * D) ∧ δ₂ * deg χ₂ + δ₃ * deg χ₃ = -(α * D) ∧
          δ₄ * deg χ₄ = δ₃ * deg χ₃ - δ₀ * deg χ₀ ∧ δ₄ * deg χ₄ = δ₁ * deg χ₁ - δ₂ * deg χ₂ ∧
          γ * Δ = δ₂ * deg χ₂ - δ₃ * deg χ₃ ∧ δ₂ * deg χ₂ - δ₃ * deg χ₃ ≠ 0 ∧
          BB = core ∪ J.image ξ ∪ evenFam ∪ V.image ψ ∧
          BB.card = (m ^ 2 + 12 * m + 8) / 6
      (∃ (δ₀ δ₁ δ₂ δ₃ δ₄ α β γ : ℤ) (χ₀ χ₁ χ₂ χ₃ χ₄ : basis.index) (ξ : ℕ → basis.index)
        (P Q : ℕ → Fin 2 → basis.index) (ψ : ZMod m × ZMod m → basis.index) (D Δ : ℤ),
        complete δ₀ δ₁ δ₂ δ₃ δ₄ α β γ χ₀ χ₁ χ₂ χ₃ χ₄ ξ P Q ψ D Δ) ∧
      ∀ (δ₀ δ₁ δ₂ δ₃ δ₄ α β γ : ℤ) (χ₀ χ₁ χ₂ χ₃ χ₄ : basis.index) (ξ : ℕ → basis.index)
        (P Q : ℕ → Fin 2 → basis.index) (ψ : ZMod m × ZMod m → basis.index) (D Δ : ℤ),
        complete δ₀ δ₁ δ₂ δ₃ δ₄ α β γ χ₀ χ₁ χ₂ χ₃ χ₄ ξ P Q ψ D Δ →
        let fb : ℤ := deg χ₁
        let Qd : ℤ := (q : ℤ) ^ 2 + ε * q + 1
        let Cubic : Prop :=
          (deg χ₀ = (q : ℤ) ^ 3 * fb ∧ deg χ₂ = Qd * fb ∧ deg χ₃ = q * Qd * fb ∧
            deg χ₄ = q * (q + ε) * fb) ∧
          (δ₀ = -(ε * δ₁) ∧ δ₂ = δ₁ ∧ δ₃ = -(ε * δ₁) ∧ δ₄ = -δ₁ ∧ α = ε * δ₁ ∧ γ = ε * δ₁) ∧
          D = ((q : ℤ) ^ 3 - ε) * fb ∧ (∀ h ∈ J, deg (ξ h) = ((q : ℤ) ^ 3 - ε) * fb) ∧
          (∀ r ∈ Finset.Ico 1 M, ∀ er, deg (P r er) = Qd * fb ∧ deg (Q r er) = q * Qd * fb) ∧
          Δ = (q + ε) * Qd * fb ∧ ∀ I ∈ V, deg (ψ I) = (q + ε) * Qd * fb
        Cubic ∧ fb = 1 ∧ δ₁ = -1 ∧ β = -1 ∧ δ₀ = ε ∧ δ₂ = -1 ∧ δ₃ = ε ∧ δ₄ = 1 ∧ α = -ε ∧
          γ = -ε := by
  intro N E T IsExtension m M q ε Qd BB deg
  have hW := FlatEvery.flat_witness_cubic hnonab n hn S e hfour p f hp hpodd hf hmodel ideal basis
    B hflat eb θB nb θhat hθ hB η hη hord
  have hD := FlatEvery.flat_block_degrees hnonab n hn S e hfour p f hp hpodd hf hmodel ideal
    basis B hflat eb θB nb θhat hθ hB η hη hord
  exact ⟨hD.1, hD.2.1, hD.2.2.1, hD.2.2.2, hW⟩

end CFSG.Wreathed

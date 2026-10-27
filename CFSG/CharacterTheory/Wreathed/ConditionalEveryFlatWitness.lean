module

public import CFSG.CharacterTheory.Wreathed.ConditionalFlatRelative
public import CFSG.CharacterTheory.Wreathed.ConditionalEveryFlatSum
public import CFSG.CharacterTheory.Wreathed.ConditionalEveryFlatMoment
public import CFSG.CharacterTheory.Wreathed.ConditionalEveryFlatGeneric

public section

open scoped BigOperators Classical ComplexConjugate

namespace CFSG.Wreathed.FlatEvery

open CFSG.TwoRankLowerBound.Helpers CFSG.Semidihedral.Principal
  CFSG.ComponentClassification.CatalogueSchreierLinearTwo
  CFSG.Semidihedral.SemilinearOddExtensions CFSG.Wreathed.ActualProjectiveLayer
  CFSG.Wreathed.FullDefectLabels CFSG.Wreathed.ConditionalFourier
  CFSG.Wreathed.FlatCentralFourier CFSG.Wreathed.AdaptedBaseFusion
  CFSG.Wreathed.ConditionalGeneralBase

theorem flat_witness_cubic
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
  intro N E T IsExtension
  have hFC := conditional_flat_complete_column_support_and_block_exhaustion hnonab n hn S e
    hfour p f hp hpodd hf hmodel ideal basis B hflat eb θB nb θhat hθ hB η hη hord
  have hRel := conditional_flat_relative_degree_alternatives_and_central_values hnonab n hn S e
    hfour p f hp hpodd hf hmodel ideal basis B hflat eb θB nb θhat hθ hB η hη hord
  have hMom := flat_cubic_moment hnonab n hn S e hfour p f hp hpodd hf hmodel ideal basis B hflat
    eb θB nb θhat hθ hB η hη hord
  refine ⟨hFC.1, hFC.2.1, ?_⟩
  intro lam hlam F _ _ sigmaGroup ρ hcard hodd hρ hlayer hrange m M s t w a y U ΦH ΦN lamN ε q q₀
    BB K J deg
  have hFC' := hFC.2.2 lam hlam F sigmaGroup ρ hcard hodd hρ hlayer hrange
  have hRel' := hRel.2.2 lam hlam F sigmaGroup ρ hcard hodd hρ hlayer hrange
  have hbase := (conditional_flat_base_columns_and_second_row_reconstruction hnonab n hn S e
    hfour p f hp hpodd hf hmodel ideal basis B hflat eb θB nb θhat hθ hB η hη hord).2.2 lam hlam
    F sigmaGroup ρ hcard hodd hρ hlayer hrange
  have hsqrt := (conditional_flat_square_root_columns_and_parity hnonab n hn S e hfour p f hp
    hpodd hf hmodel ideal basis B hflat eb θB nb θhat hθ hB η hη hord).2.2 lam hlam F sigmaGroup
    ρ hcard hodd hρ hlayer hrange
  refine ⟨hFC'.1, fun ζ hζ θ hθ hθζ => ?_⟩
  intro ν Y
  have hFCζ := hFC'.2 ζ hζ θ hθ hθζ
  have hRelζ := hRel'.2 ζ hζ θ hθ hθζ
  refine ⟨hFCζ.1, fun v hv => ?_⟩
  intro X Fs σ υ g hA
  have hFCv := hFCζ.2 v hv σ υ g hA
  have hRelv := hRelζ.2 v hv σ υ g hA
  refine ⟨hFCv.1, fun lamU hlamU => ?_⟩
  intro tm c Cl
  have hFCl := hFCv.2 lamU hlamU
  have hRell := hRelv.2 lamU hlamU
  refine ⟨hFCl.1, fun V hV6 hVrep => ?_⟩
  intro complete
  refine ⟨hFCl.2 V hV6 hVrep, ?_⟩
  intro δ₀ δ₁ δ₂ δ₃ δ₄ α β γ χ₀ χ₁ χ₂ χ₃ χ₄ ξ P Q ψ D Δ hcomp fb Qd Cubic
  obtain ⟨hX, hcen, hPQx, -, -⟩ := (hRell.2 V hV6 hVrep).2 δ₀ δ₁ δ₂ δ₃ δ₄ α β γ χ₀ χ₁ χ₂ χ₃ χ₄ ξ P
    Q ψ D Δ hcomp
  obtain ⟨hsign, hinj, hξinj, hPQinj, hψinj, hξcore, hPQcore, hψcore, hXodd, hY0, hcMM, hXeven,
    -, hdiag, hgen, ⟨hdet0, hinv, -, hcov, -⟩, ⟨hd₀, hd₁, hd₂, hd₃, hd₄⟩, hD, hΔ, hdξ,
    hdPQ, hdψ, -, -, -, -, -, -, hBB, -⟩ := hcomp
  have hm4 : 4 ≤ m := by
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  have hm : m = 2 * M :=
    (Nat.two_mul_div_two_of_even ((Nat.even_pow' (by omega)).mpr even_two)).symm
  have hM2 : 2 ≤ M := by omega
  have hM0 : 0 < M := by omega
  have : NeZero m := ⟨by omega⟩
  obtain ⟨K, hK, hK3, hMK, hmK⟩ := ConditionalExactOrder.modulus_split hn
  have hMeven : Even M := ⟨K, by show 2 ^ n / 2 = K + K; omega⟩
  have hq3 : 3 ≤ q := by
    have hp3 : 3 ≤ p := by
      have := hp.two_le
      omega
    show 3 ≤ Nat.card F
    rw [hcard]
    exact le_trans hp3 (Nat.le_self_pow (by omega) p)
  have hqodd : Odd q := by
    show Odd (Nat.card F)
    rw [hcard]
    exact (hp.odd_of_ne_two hpodd).pow
  have hε : ε = 1 ∨ ε = -1 := by
    by_cases h : Nat.card F % 4 = 1
    · exact Or.inl (ite_eq_left h)
    · exact Or.inr (ite_eq_right h)
  obtain ⟨s₀, s₁, s₂, s₃, s₄, sα, sβ, sγ⟩ := FlatRelative.signs_of_forall_mem hsign
  obtain ⟨hmemχ, hmemξ, hmemPQ⟩ := FlatRelative.mem_of_eq_union hBB
  have hmemψ := mem_gen_of_eq_union hBB
  choose! er her using hdiag
  have hS : FlatRelative.Support BB m M V X c δ₀ δ₁ δ₂ δ₃ δ₄ α γ χ₀ χ₁ χ₂ χ₃ χ₄ ξ P Q ψ er :=
    { hm := hm, hM := hM2, hV6 := hV6, inj := hinj, ξinj := hξinj, PQinj := hPQinj,
      ψinj := hψinj, ξcore := hξcore, PQcore := hPQcore, ψcore := hψcore, Xodd := hXodd,
      cMM := hcMM, Xeven := hXeven, diag := her, gen := hgen,
      c00 := fun χ hχ => (hdet0 χ hχ).1, inv := hinv, cov := hcov, memχ₀ := hmemχ.1,
      memχ₁ := hmemχ.2.1, memχ₂ := hmemχ.2.2.1, memχ₃ := hmemχ.2.2.2.1,
      memχ₄ := hmemχ.2.2.2.2, memξ := hmemξ, memPQ := hmemPQ }
  obtain ⟨-, -, -, -, -, -, -, -, hζall⟩ := hbase
  obtain ⟨-, hvall⟩ := hζall ζ hζ θ hθ hθζ
  obtain ⟨-, hlamUall⟩ := hvall v hv σ υ g hA
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, hsec₀, -, -, -⟩ := hlamUall lamU hlamU
  have hsec : ∀ χ ∈ BB, ∀ k ∈ Finset.Ico 1 m, ∀ z ∈ Subgroup.centralizer {a ^ k},
      Odd (orderOf z) → 2 * (basis.representation χ).character (a ^ k * z) =
        lamN z * ((1 - ε * ΦN z) * ∑ j ∈ Finset.Ico 1 m, ζ ^ (-((j : ℤ) * k)) * X j χ +
          (1 + ε * ΦN z) * ∑ j ∈ Finset.Ico 1 m,
            ζ ^ (-((j : ℤ) * k)) * (Cl 0 χ - Cl (-(j : ZMod m)) χ)) := hsec₀
  obtain ⟨-, -, -, -, -, hSqζ⟩ := hsqrt
  obtain ⟨-, hYinv₀, -, -, -, -, -, -⟩ := hSqζ ζ hζ θ hθ hθζ
  have hlamN : ∀ (g : G) (hg : g ∈ N), lamN g = lam ⟨g, hg⟩ := fun g hg => dite_eq_left hg
  have hlam1 : lamN 1 = 1 := by
    rw [hlamN 1 N.one_mem]
    have h1 : (⟨1, N.one_mem⟩ : N) = 1 := rfl
    rw [h1, map_one, Units.val_one]
  have hΦ1 : ΦN 1 = (q : ℂ) := by
    have hfix : Nat.card {ω : Omega F // ((ρ (centralizerFullQuotientMap n hn S e
        (centralizerOddCoreMap n S e ⟨1, N.one_mem⟩)) : coordinateE F) :
          Equiv.Perm (Omega F)) ω = ω} = Nat.card (Omega F) :=
      Nat.card_congr (Equiv.subtypeUnivEquiv fun ω => by
        rw [show (⟨1, N.one_mem⟩ : N) = 1 from rfl, map_one, map_one, map_one]
        rfl)
    show (if hg : (1 : G) ∈ N then ΦH (centralizerOddCoreMap n S e ⟨1, hg⟩) else 0) = _
    rw [dite_eq_left N.one_mem]
    show (Nat.card {ω : Omega F // _} : ℂ) - 1 = _
    rw [hfix, CFSG.Wreathed.CentralSL2.card_omega]
    push_cast
    ring
  have hM_Ico : M ∈ Finset.Ico 1 m := Finset.mem_Ico.mpr ⟨by omega, by omega⟩
  have h1C : (1 : G) ∈ Subgroup.centralizer {a ^ M} := Subgroup.one_mem _
  have h1odd : Odd (orderOf (1 : G)) := by
    rw [orderOf_one]
    exact odd_one
  have hnegM : (-1 : ℂ) ^ M = 1 := hMeven.neg_one_pow
  obtain ⟨x₀, x₁, x₂, x₃, x₄, xξ⟩ := hcen M hM_Ico 1 h1C h1odd
  have x₀' : (basis.representation χ₀).character (a ^ M * 1) = lamN 1 * δ₀ * ε * ΦN 1 := x₀
  have x₁' : (basis.representation χ₁).character (a ^ M * 1) = -(lamN 1 * δ₁) := x₁
  have x₂' : (basis.representation χ₂).character (a ^ M * 1) =
      -(lamN 1 * δ₂ * (1 + (-1) ^ M * (1 + ε * ΦN 1))) := x₂
  have x₃' : (basis.representation χ₃).character (a ^ M * 1) =
      lamN 1 * δ₃ * (-1 + (1 + (-1) ^ M) * (1 + ε * ΦN 1)) := x₃
  have x₄' : (basis.representation χ₄).character (a ^ M * 1) =
      lamN 1 * δ₄ * (1 + ε * ΦN 1) := x₄
  have xξ' : ∀ h ∈ J, (basis.representation (ξ h)).character (a ^ M * 1) =
      lamN 1 * α * (1 - ε * ΦN 1) * ζ ^ (-((h : ℤ) * M)) := xξ
  clear x₀ x₁ x₂ x₃ x₄ xξ
  simp only [mul_one, hlam1, hΦ1, one_mul, hnegM] at x₀' x₁' x₂' x₃' x₄' xξ'
  have vψ := fun I (hI : I ∈ V) => hS.values_gen hζ (fun χ => (basis.representation χ).character
    (a ^ M * 1)) (lamN 1) (ΦN 1) ε (fun χ hχ => hsec χ hχ M hM_Ico 1 h1C h1odd) hVrep hI
    (hmemψ I hI)
  simp only [mul_one, hlam1, hΦ1, one_mul] at vψ
  have hJ : ((Finset.Ico 1 m).filter Odd).card = M := by
    rw [show m = 2 * M from hm]
    exact CFSG.Wreathed.ConditionalSquareRoot.card_filter_odd_Ico M
  have hE := ConditionalGlobalDegrees.card_filter_evenEven hn V hV6 hVrep
  have hO := ConditionalGlobalDegrees.card_filter_not_evenEven hn V hV6 hVrep
  have hE' : ((V.filter fun I => Even I.1.val ∧ Even I.2.val).card : ℂ) =
      (2 * K - 1) * (2 * K - 2) / 6 := by
    rw [hE, hMK]
    exact ConditionalExactOrder.cast_even_count hK hK3
  have hO' : ((V.filter fun I => ¬ (Even I.1.val ∧ Even I.2.val)).card : ℂ) =
      4 * K * (4 * K - 2) / 8 := by
    rw [hO, hmK]
    exact ConditionalExactOrder.cast_other_count hK
  have hSB : ∑ φ ∈ BB, (basis.representation φ).character (a ^ M) ^ 3 / (deg φ : ℂ) =
      ((4 * K : ℕ) : ℂ) ^ 2 * ((q : ℂ) + ε) ^ 2 / ((q : ℂ) ^ 2 + ε * q + 1) := by
    rw [Finset.sum_congr rfl fun φ _ => by
      rw [show ((deg φ : ℤ) : ℂ) = (basis.representation φ).character 1 from
        basisDegree_cast basis φ]]
    have h := hMom
    rw [← hcard] at h
    refine h.trans ?_
    rw [show ((2 ^ n : ℕ) : ℂ) = ((4 * K : ℕ) : ℂ) from congrArg _ hmK]
  have hfin := hS.cubic_of_moment hBB hq3 hqodd hε s₁ hK hMK hJ hE' hO' deg hd₁ hdξ hdPQ hdψ
    (fun φ => (basis.representation φ).character (a ^ M)) x₀' x₁' (by rw [x₂']; ring)
    (by rw [x₃']; ring) x₄'
    (fun h hh => by
      rw [xξ' h hh, ConditionalGlobalDegrees.zpow_neg_odd_half hζ hm (Finset.mem_filter.mp hh).2]
      ring)
    (fun r hr e => hPQx r hr e) vψ hX hSB
  obtain ⟨hC, hfb1, hδ1⟩ := hfin
  have h1 : Module.finrank ℂ (basis.representation χ₁).vector = 1 := by
    have h' : (Module.finrank ℂ (basis.representation χ₁).vector : ℤ) = 1 := hfb1
    exact_mod_cast h'
  have hχ1 := character_eq_one_of_finrank_one hnonab (basis.representation χ₁) h1
  have hY1 := hYinv₀ χ₁ hmemχ.2.1 0 hM0
  have hYβ := hY0 χ₁ hmemχ.2.1
  obtain ⟨n01, n02, n03, -, n12, n13, -, -, -, -⟩ := hS.core_ne
  have hYc : (Y 0 χ₁ : ℂ) = 1 := by
    have hrow : ∀ i ∈ Finset.range M, (basis.representation χ₁).character (y ^ (2 * i + 1)) *
        ζ ^ (-(((0 : ℕ) : ℤ) * (2 * i + 1))) = 1 := fun i _ => by
      rw [hχ1, Pi.one_apply, one_mul, Nat.cast_zero, zero_mul, neg_zero, zpow_zero]
    rw [show (Y 0 χ₁ : ℂ) = _ from hY1, Finset.sum_congr rfl hrow, Finset.sum_const,
      Finset.card_range, nsmul_eq_mul, mul_one, inv_mul_cancel₀ (by exact_mod_cast hM0.ne')]
  have hYβ' : Y 0 χ₁ = β * δ₁ := by
    rw [hYβ]
    simp [n01, n12.symm, n13.symm]
  have hβ : β = -1 := by
    have h' : Y 0 χ₁ = 1 := by exact_mod_cast hYc
    rw [hYβ', hδ1] at h'
    omega
  obtain ⟨-, ⟨e₀, e₂, e₃, e₄, eα, eγ⟩, -⟩ := id hC
  refine ⟨hC, hfb1, hδ1, hβ, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [e₀, hδ1]
    ring
  · rw [e₂, hδ1]
  · rw [e₃, hδ1]
    ring
  · rw [e₄, hδ1]
    rfl
  · rw [eα, hδ1]
    ring
  · rw [eγ, hδ1]
    ring

end CFSG.Wreathed.FlatEvery

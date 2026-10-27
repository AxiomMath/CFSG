module

public import CFSG.CharacterTheory.Wreathed.ConditionalFlatCompleteColumns
public import CFSG.CharacterTheory.Wreathed.ConditionalFiveFixedCharacters
public import CFSG.CharacterTheory.Wreathed.ConditionalFlatBase

public section

open scoped BigOperators Classical ComplexConjugate

namespace CFSG.Wreathed

open CFSG.TwoRankLowerBound.Helpers CFSG.Semidihedral.Principal
  CFSG.ComponentClassification.CatalogueSchreierLinearTwo
  CFSG.Semidihedral.SemilinearOddExtensions CFSG.Wreathed.ActualProjectiveLayer
  CFSG.Wreathed.FullDefectLabels CFSG.Wreathed.ConditionalFourier
  CFSG.Wreathed.FlatCentralFourier CFSG.Wreathed.AdaptedBaseFusion
  CFSG.Wreathed.ConditionalGeneralBase

theorem conditional_flat_complete_column_support_and_block_exhaustion
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
      ∃ (δ₀ δ₁ δ₂ δ₃ δ₄ α β γ : ℤ) (χ₀ χ₁ χ₂ χ₃ χ₄ : basis.index) (ξ : ℕ → basis.index)
        (P Q : ℕ → Fin 2 → basis.index) (ψ : ZMod m × ZMod m → basis.index) (D Δ : ℤ),
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
        BB.card = (m ^ 2 + 12 * m + 8) / 6 := by
  intro N E T IsExtension
  obtain ⟨hex, hlamex, -⟩ := conditional_flat_local_twisted_regular_bases hnonab n hn S e hfour
    p f hp hpodd hf hmodel ideal basis B hflat eb θB nb θhat hθ hB η hη hord
  refine ⟨hex, hlamex, ?_⟩
  intro lam hlam F _ _ sigmaGroup ρ hcard hodd hρ hlayer hrange m M s t w a y U ΦH ΦN lamN ε q q₀
    BB K J deg
  have hnvA := FlatComplete.flat_value_a_ne_zero n hn S e ideal basis B eb θB nb θhat hθ hB lam
    hlam.1 hlam.2.1
  have hbase := (conditional_flat_base_columns_and_second_row_reconstruction hnonab n hn S e
    hfour p f hp hpodd hf hmodel ideal basis B hflat eb θB nb θhat hθ hB η hη hord).2.2 lam hlam
    F sigmaGroup ρ hcard hodd hρ hlayer hrange
  have hsqrt := (conditional_flat_square_root_columns_and_parity hnonab n hn S e hfour p f hp
    hpodd hf hmodel ideal basis B hflat eb θB nb θhat hθ hB η hη hord).2.2 lam hlam F sigmaGroup
    ρ hcard hodd hρ hlayer hrange
  have hcentral := (conditional_flat_central_section_integral_fourier_columns hnonab n hn S e
    hfour p f hp hpodd hf hmodel ideal basis B hflat eb θB nb θhat hθ hB η hη hord).2.2 lam hlam
    F sigmaGroup ρ hcard hodd hρ hlayer hrange
  obtain ⟨-, -, -, -, -, -, -, hadapt, hζall⟩ := hbase
  refine ⟨hadapt, ?_⟩
  intro ζ hζ θ hθ hθζ ν Y
  obtain ⟨hvex, hvall⟩ := hζall ζ hζ θ hθ hθζ
  refine ⟨hvex, ?_⟩
  intro v hv X Fs σ υ g hA
  obtain ⟨hlamUex, hlamUall⟩ := hvall v hv σ υ g hA
  refine ⟨hlamUex, ?_⟩
  intro lamU hlamU tm c Cl
  obtain ⟨-, hcint₀, hc00₀, hcsymm₀, hgram₀, hcX₀, hcY₀, -, hcdeg₀, hrecon₀, -, hsec₀, hpodd₀,
    hpeven₀, hpY₀⟩ := hlamUall lamU hlamU
  have hcint : ∀ i j, ∀ χ ∈ BB, ∃ z : ℤ, c i j χ = z := hcint₀
  have hc00 : ∀ χ, c 0 0 χ = 0 := hc00₀
  have hcsymm : ∀ i j χ, c i j χ = c j i χ ∧ c i j χ = c j (-i - j) χ := hcsymm₀
  have hcX : ∀ i j, ∀ j' ∈ Finset.Ico 1 m, ∑ χ ∈ BB, c i j χ * conj (X j' χ) = 0 := hcX₀
  have hcY : ∀ i j, ∀ r < M, ∑ χ ∈ BB, c i j χ * (Y r χ : ℂ) = 0 := hcY₀
  have hcdeg : ∀ i j, ∑ χ ∈ BB, c i j χ * (basis.representation χ).character 1 = 0 := hcdeg₀
  have hrecon : ∀ j : ZMod m, ∀ χ ∈ BB, X j χ + 2 * Fs j χ = Cl 0 χ - Cl (-j) χ := hrecon₀
  have hsec : ∀ χ ∈ BB, ∀ k ∈ Finset.Ico 1 m, ∀ z ∈ Subgroup.centralizer {a ^ k},
      Odd (orderOf z) → 2 * (basis.representation χ).character (a ^ k * z) =
        lamN z * ((1 - ε * ΦN z) * ∑ j ∈ Finset.Ico 1 m, ζ ^ (-((j : ℤ) * k)) * X j χ +
          (1 + ε * ΦN z) * ∑ j ∈ Finset.Ico 1 m,
            ζ ^ (-((j : ℤ) * k)) * (Cl 0 χ - Cl (-(j : ZMod m)) χ)) := hsec₀
  have hpodd : ∀ j ∈ Finset.Ico 1 m, Odd j → ∀ χ ∈ BB, ∃ k : ℤ, X j χ - c M M χ = 2 * k :=
    hpodd₀
  have hpeven : ∀ j ∈ Finset.Ico 1 m, Even j → ∀ r : ZMod m, 2 * r = -(j : ZMod m) →
      ∀ χ ∈ BB, ∃ k : ℤ, X j χ - (c M M χ + c r r χ + c (r + M) (r + M) χ) = 2 * k := hpeven₀
  have hpY : ∀ χ ∈ BB, ∃ k : ℤ, c M M χ - Y 0 χ = 2 * k := hpY₀
  have hm4 : 4 ≤ m := by
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  have hm : m = 2 * M :=
    (Nat.two_mul_div_two_of_even ((Nat.even_pow' (by omega)).mpr even_two)).symm
  have hM2 : 2 ≤ M := by omega
  have hM0 : 0 < M := by omega
  have : NeZero m := ⟨by omega⟩
  refine ⟨ConditionalFiveFixed.exists_orbit_representatives (K := dualGroup m)
    (X := ZMod m × ZMod m) (fun O => O.ncard = 6), ?_⟩
  intro V hV6 hVrep
  obtain ⟨-, -, -, -, -, hSqζ⟩ := hsqrt
  obtain ⟨-, -, hYgram, -, hYdeg, -, -, hYall⟩ := hSqζ ζ hζ θ hθ hθζ
  obtain ⟨Fc, hFc, hFcY, -, hFceven, -, -, -, -⟩ := hYall v hv
  obtain ⟨v₀, -, -, hv₀uniq, -, -, -, -, -, -, hfdeg, -, h8, h4⟩ := hcentral ζ hζ
  have hveq : ∀ χ ∈ BB, ∀ k ∈ Finset.Ico 1 m, v χ k = v₀ χ k := fun χ hχ k hk =>
    hv₀uniq χ hχ k hk (v χ k) (fun r hr hodd => hv χ hχ k hk r hr hodd)
  have hfeq : ∀ χ ∈ BB, ∀ (ℓ : Fin 2) (j : ℕ), fourierTransform m ζ (fun k => v χ k ℓ) j =
      fourierTransform m ζ (fun k => v₀ χ k ℓ) j := fun χ hχ ℓ j =>
    fourierTransform_congr (fun k hk => by rw [hveq χ hχ k hk]) j
  let Xz : ZMod m → BB → ℤ := fun j i => Fc i.1 j.val 0
  choose cz hcz using fun (a' b' : ZMod m) (i : BB) => hcint a' b' i.1 i.2
  have hvalpos : ∀ j : ZMod m, j ≠ 0 → j.val ∈ Finset.Ico 1 m := fun j hj =>
    Finset.mem_Ico.mpr ⟨Nat.pos_of_ne_zero fun h => hj ((ZMod.val_eq_zero j).mp h),
      ZMod.val_lt j⟩
  have hXz : ∀ j : ZMod m, j ≠ 0 → ∀ i : BB, X j i.1 = Xz j i := fun j hj i =>
    (hFc i.1 i.2 j.val (hvalpos j hj) 0).symm
  have hXz₀ : ∀ j : ZMod m, j ≠ 0 → ∀ i : BB,
      (Xz j i : ℂ) = fourierTransform m ζ (fun k => v₀ i.1 k 0) j.val := fun j hj i =>
    (hFc i.1 i.2 j.val (hvalpos j hj) 0).trans (hfeq i.1 i.2 0 j.val)
  have hdegc : ∀ χ, ((deg χ : ℤ) : ℂ) = (basis.representation χ).character 1 :=
    fun χ => basisDegree_cast basis χ
  have hsum : ∀ f : basis.index → ℤ, ((∑ i : BB, f i.1 : ℤ) : ℂ) = ∑ χ ∈ BB, (f χ : ℂ) := by
    intro f
    rw [Int.cast_sum]
    exact Finset.sum_coe_sort BB (fun χ => (f χ : ℂ))
  have hzint : ∀ (a' b' : ZMod m) (χ : basis.index) (hχ : χ ∈ BB),
      c a' b' χ = (cz a' b' ⟨χ, hχ⟩ : ℂ) := fun a' b' χ hχ => hcz a' b' ⟨χ, hχ⟩
  have hconj : ∀ z : ℤ, conj (z : ℂ) = z := fun z => map_intCast (starRingEnd ℂ) z
  have hXX : ∀ j j' : ZMod m, j ≠ 0 → j' ≠ 0 → Xz j ⬝ᵥ Xz j' = if j = j' then 8 else 4 := by
    intro j j' hj hj'
    have key : ((Xz j ⬝ᵥ Xz j' : ℤ) : ℂ) = ∑ χ ∈ BB,
        fourierTransform m ζ (fun k => v₀ χ k 0) j.val *
          fourierTransform m ζ (fun k => v₀ χ k 0) j'.val := by
      rw [dotProduct, Int.cast_sum, ← Finset.sum_coe_sort BB]
      refine Finset.sum_congr rfl fun i _ => ?_
      push_cast
      rw [hXz₀ j hj i, hXz₀ j' hj' i]
    by_cases hjj : j = j'
    · subst hjj
      rw [ite_eq_left rfl]
      have h := h8 j.val (hvalpos j hj)
      rw [show ∑ χ ∈ BB, fourierTransform m ζ (fun k => v₀ χ k 0) j.val ^ 2 =
        ∑ χ ∈ BB, fourierTransform m ζ (fun k => v₀ χ k 0) j.val *
          fourierTransform m ζ (fun k => v₀ χ k 0) j.val from
        Finset.sum_congr rfl fun _ _ => sq _, ← key] at h
      exact_mod_cast h
    · rw [ite_eq_right hjj]
      have hne : j.val ≠ j'.val := fun h => hjj (ZMod.val_injective m h)
      have h := h4 j.val (hvalpos j hj) j'.val (hvalpos j' hj') hne
      rw [← key] at h
      exact_mod_cast h
  have hXd : ∀ j : ZMod m, j ≠ 0 → Xz j ⬝ᵥ (fun i : BB => deg i.1) = 0 := by
    intro j hj
    have h := hfdeg j.val (hvalpos j hj) 0
    have key : ((Xz j ⬝ᵥ (fun i : BB => deg i.1) : ℤ) : ℂ) = ∑ χ ∈ BB,
        (basis.representation χ).character 1 * fourierTransform m ζ (fun k => v₀ χ k 0) j.val := by
      rw [dotProduct, Int.cast_sum, ← Finset.sum_coe_sort BB]
      refine Finset.sum_congr rfl fun i _ => ?_
      push_cast
      rw [hXz₀ j hj i, hdegc, mul_comm]
    rw [← key] at h
    exact_mod_cast h
  have hYY : ∀ r t, r < M → t < M → (fun i : BB => Y r i.1) ⬝ᵥ (fun i : BB => Y t i.1) =
      if r = t then 4 else 0 := by
    intro r t hr ht
    have h := hYgram r hr t ht
    rw [← h, dotProduct]
    exact Finset.sum_coe_sort BB (fun χ => Y r χ * Y t χ)
  have hYd : ∀ r < M, (fun i : BB => Y r i.1) ⬝ᵥ (fun i : BB => deg i.1) = 0 := by
    intro r hr
    have h := hYdeg r hr
    have key : (((fun i : BB => Y r i.1) ⬝ᵥ (fun i : BB => deg i.1) : ℤ) : ℂ) =
        ∑ χ ∈ BB, (Y r χ : ℂ) * (basis.representation χ).character 1 := by
      rw [dotProduct, Int.cast_sum, ← Finset.sum_coe_sort BB]
      refine Finset.sum_congr rfl fun i _ => ?_
      push_cast
      rw [hdegc]
    rw [← key] at h
    exact_mod_cast h
  have hYX : ∀ r < M, ∀ j : ZMod m, j ≠ 0 → (fun i : BB => Y r i.1) ⬝ᵥ Xz j = 0 := by
    intro r hr j hj
    have h := hFcY r hr j.val (hvalpos j hj) 0
    rw [← h, dotProduct]
    exact Finset.sum_coe_sort BB (fun χ => Y r χ * Fc χ j.val 0)
  have hc00' : cz 0 0 = 0 := by
    funext i
    have h := hc00 i.1
    rw [hcz] at h
    exact_mod_cast h
  have hcsymm' : ∀ a' b', cz a' b' = cz b' a' ∧ cz a' b' = cz b' (-a' - b') := by
    intro a' b'
    refine ⟨funext fun i => ?_, funext fun i => ?_⟩
    · have h := (hcsymm a' b' i.1).1
      rw [hcz, hcz] at h
      exact_mod_cast h
    · have h := (hcsymm a' b' i.1).2
      rw [hcz, hcz] at h
      exact_mod_cast h
  have hcd : ∀ a' b', cz a' b' ⬝ᵥ (fun i : BB => deg i.1) = 0 := by
    intro a' b'
    have h := hcdeg a' b'
    have key : ((cz a' b' ⬝ᵥ (fun i : BB => deg i.1) : ℤ) : ℂ) =
        ∑ χ ∈ BB, c a' b' χ * (basis.representation χ).character 1 := by
      rw [dotProduct, Int.cast_sum, ← Finset.sum_coe_sort BB]
      refine Finset.sum_congr rfl fun i _ => ?_
      push_cast
      rw [hcz, hdegc]
    rw [← key] at h
    exact_mod_cast h
  have hcX' : ∀ a' b' j', j' ≠ 0 → cz a' b' ⬝ᵥ Xz j' = 0 := by
    intro a' b' j' hj'
    have h := hcX a' b' j'.val (hvalpos j' hj')
    have key : ((cz a' b' ⬝ᵥ Xz j' : ℤ) : ℂ) =
        ∑ χ ∈ BB, c a' b' χ * conj (X (j'.val : ZMod m) χ) := by
      rw [dotProduct, Int.cast_sum, ← Finset.sum_coe_sort BB]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [ZMod.natCast_zmod_val, hXz j' hj' i, hcz, hconj]
      push_cast
      rfl
    rw [← key] at h
    exact_mod_cast h
  have hcY' : ∀ a' b', ∀ r < M, cz a' b' ⬝ᵥ (fun i : BB => Y r i.1) = 0 := by
    intro a' b' r hr
    have h := hcY a' b' r hr
    have key : ((cz a' b' ⬝ᵥ (fun i : BB => Y r i.1) : ℤ) : ℂ) =
        ∑ χ ∈ BB, c a' b' χ * (Y r χ : ℂ) := by
      rw [dotProduct, Int.cast_sum, ← Finset.sum_coe_sort BB]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [hcz]
      push_cast
      rfl
    rw [← key] at h
    exact_mod_cast h
  have hcc : ∀ (a₁ b₁ a₂ b₂ : ZMod m), ((cz a₁ b₁ ⬝ᵥ cz a₂ b₂ : ℤ) : ℂ) =
      ∑ χ ∈ BB, c a₁ b₁ χ * conj (c a₂ b₂ χ) := by
    intro a₁ b₁ a₂ b₂
    rw [dotProduct, Int.cast_sum, ← Finset.sum_coe_sort BB]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hcz, hcz, hconj]
    push_cast
    rfl
  obtain ⟨g8, g7, g6, g6', g6''⟩ := hgram₀ V hV6 hVrep
  have g8' : ∀ r : ZMod m, r ≠ 0 → ∑ χ ∈ BB, c r r χ * conj (c r r χ) = 8 := g8
  have g7' : ∀ I ∈ V, ∑ χ ∈ BB, c I.1 I.2 χ * conj (c I.1 I.2 χ) = 7 := g7
  have g6a : ∀ r r' : ZMod m, r ≠ 0 → r' ≠ 0 → r ≠ r' →
      ∑ χ ∈ BB, c r r χ * conj (c r' r' χ) = 6 := g6
  have g6b : ∀ r : ZMod m, r ≠ 0 → ∀ I ∈ V, ∑ χ ∈ BB, c r r χ * conj (c I.1 I.2 χ) = 6 :=
    fun r hr I hI => (g6' r hr I hI).1
  have g6c : ∀ I ∈ V, ∀ I' ∈ V, I ≠ I' → ∑ χ ∈ BB, c I.1 I.2 χ * conj (c I'.1 I'.2 χ) = 6 := g6''
  have hcrr : ∀ r : ZMod m, r ≠ 0 → cz r r ⬝ᵥ cz r r = 8 := fun r hr => by
    have h := g8' r hr
    rw [← hcc] at h
    exact_mod_cast h
  have hcV : ∀ I ∈ V, cz I.1 I.2 ⬝ᵥ cz I.1 I.2 = 7 := fun I hI => by
    have h := g7' I hI
    rw [← hcc] at h
    exact_mod_cast h
  have hcrr' : ∀ r r' : ZMod m, r ≠ 0 → r' ≠ 0 → r ≠ r' → cz r r ⬝ᵥ cz r' r' = 6 :=
    fun r r' hr hr' hrr => by
      have h := g6a r r' hr hr' hrr
      rw [← hcc] at h
      exact_mod_cast h
  have hcrV : ∀ r : ZMod m, r ≠ 0 → ∀ I ∈ V, cz r r ⬝ᵥ cz I.1 I.2 = 6 := fun r hr I hI => by
    have h := g6b r hr I hI
    rw [← hcc] at h
    exact_mod_cast h
  have hcVV : ∀ I ∈ V, ∀ I' ∈ V, I ≠ I' → cz I.1 I.2 ⬝ᵥ cz I'.1 I'.2 = 6 :=
    fun I hI I' hI' hII => by
      have h := g6c I hI I' hI' hII
      rw [← hcc] at h
      exact_mod_cast h
  have hmodeq : ∀ {x y : ℤ} (k : ℤ), x - y = 2 * k → x ≡ y [ZMOD 2] := fun {x y} k hk =>
    (Int.modEq_iff_dvd.mpr ⟨k, hk⟩).symm
  have hevenj : ∀ r ∈ Finset.Ico 1 M, m - 2 * r ∈ Finset.Ico 1 m ∧ Even (m - 2 * r) ∧
      (((m - 2 * r : ℕ) : ℕ) : ZMod m) = -(2 * (r : ZMod m)) := by
    intro r hr
    have hr' := Finset.mem_Ico.mp hr
    exact ⟨Finset.mem_Ico.mpr ⟨by omega, by omega⟩, ⟨M - r, by omega⟩,
      (FlatComplete.neg_two_mul_eq hm hr'.2.le).symm⟩
  have hpodd' : ∀ j ∈ Finset.Ico 1 m, Odd j → ∀ i : BB, Xz j i ≡ cz M M i [ZMOD 2] := by
    intro j hj hodd i
    obtain ⟨k, hk⟩ := hpodd j hj hodd i.1 i.2
    rw [hXz (j : ZMod m) (FlatComplete.natCast_ne_zero_of_lt (Finset.mem_Ico.mp hj).1
      (Finset.mem_Ico.mp hj).2) i, hcz] at hk
    exact hmodeq k (by exact_mod_cast hk)
  have hpeven' : ∀ r ∈ Finset.Ico 1 M, ∀ i : BB, Xz (-(2 * (r : ZMod m))) i ≡
      cz M M i + cz r r i + cz ((r : ZMod m) + M) ((r : ZMod m) + M) i [ZMOD 2] := by
    intro r hr i
    obtain ⟨hj, hje, hjr⟩ := hevenj r hr
    obtain ⟨k, hk⟩ := hpeven (m - 2 * r) hj hje (r : ZMod m) (by rw [hjr, neg_neg]) i.1 i.2
    rw [hjr, hXz _ (FlatComplete.neg_two_mul_ne_zero hm hr) i, hcz, hcz, hcz] at hk
    exact hmodeq k (by exact_mod_cast hk)
  have hpY' : ∀ i : BB, cz M M i ≡ Y 0 i.1 [ZMOD 2] := by
    intro i
    obtain ⟨k, hk⟩ := hpY i.1 i.2
    rw [hcz] at hk
    exact hmodeq k (by exact_mod_cast hk)
  have hpXY' : ∀ r ∈ Finset.Ico 1 M, ∀ i : BB,
      Xz (-(2 * (r : ZMod m))) i ≡ Y 0 i.1 + Y r i.1 [ZMOD 2] := by
    intro r hr i
    obtain ⟨hj, hje, hjr⟩ := hevenj r hr
    have hr' := Finset.mem_Ico.mp hr
    have h := hFceven (m - 2 * r) hj hje r hr'.1 hr'.2
      (by rw [show r + (m - 2 * r) / 2 = M by omega, Nat.mod_self]) i.1 i.2
    have hXv : Xz (-(2 * (r : ZMod m))) i = Fc i.1 (m - 2 * r) 0 := by
      show Fc i.1 (-(2 * (r : ZMod m))).val 0 = _
      rw [← hjr, ZMod.val_cast_of_lt (Finset.mem_Ico.mp hj).2]
    rw [hXv]
    exact h
  have hnv : ∀ (i : BB) (κ : ℤ), (∀ j : ZMod m, j ≠ 0 → Xz j i = 0) →
      (∀ a' b', cz a' b' i = if (a' = 0 ∨ a' = M) ∧ (b' = 0 ∨ b' = M) then 0 else κ) →
      False := by
    intro i κ hXi hci
    have hne := hnvA i.1 i.2
    have h1m : 1 ∈ Finset.Ico 1 m := Finset.mem_Ico.mpr ⟨le_rfl, by omega⟩
    have hval := hsec i.1 i.2 1 h1m 1 (Subgroup.one_mem _) (by rw [orderOf_one]; exact odd_one)
    have hX0 : ∀ j ∈ Finset.Ico 1 m, X (j : ZMod m) i.1 = 0 := fun j hj => by
      rw [hXz _ (FlatComplete.natCast_ne_zero_of_lt (Finset.mem_Ico.mp hj).1
        (Finset.mem_Ico.mp hj).2) i, hXi _ (FlatComplete.natCast_ne_zero_of_lt
          (Finset.mem_Ico.mp hj).1 (Finset.mem_Ico.mp hj).2), Int.cast_zero]
    have hCl : ∀ l, Cl l i.1 = if l = 0 ∨ l = M then ((m : ℂ) - 2) * κ else (m : ℂ) * κ := by
      intro l
      rw [← FlatComplete.line_sum hm hM0 (κ : ℂ) l]
      refine Finset.sum_congr rfl fun a' _ => ?_
      rw [hcz, hci]
      split_ifs <;> simp
    have hsum1 : ∑ j ∈ Finset.Ico 1 m, ζ ^ (-((j : ℤ) * ((1 : ℕ) : ℤ))) * X (j : ZMod m) i.1 =
        0 := Finset.sum_eq_zero fun j hj => by rw [hX0 j hj, mul_zero]
    have hsum2 := FlatComplete.fourier_exc_vanish hζ hm hM0 (fun l => Cl l i.1) (κ : ℂ) hCl
    rw [hsum1, hsum2, mul_zero, mul_zero, add_zero, mul_zero, pow_one, mul_one] at hval
    exact hne (by linear_combination hval / 2)
  have hD : FlatComplete.ColumnData m M (fun i : BB => deg i.1) Xz (fun r i => Y r i.1) cz V :=
    { pow := ⟨n, hn, rfl⟩, hm := hm, hd := fun i => basisDegree_pos basis i.1, hV6 := hV6,
      hVrep := hVrep, hXX := hXX, hXd := hXd, hYY := hYY, hYd := hYd, hYX := hYX,
      hc00 := hc00', hcsymm := hcsymm', hcd := hcd, hcX := hcX', hcY := hcY', hcrr := hcrr,
      hcV := hcV, hcrr' := hcrr', hcrV := hcrV, hcVV := hcVV, hpodd := hpodd',
      hpeven := hpeven', hpY := hpY', hpXY := hpXY', hnv := hnv }
  have hRdet : (∀ χ ∈ BB, c 0 0 χ = 0 ∧ X 0 χ = 0 ∧ Fs 0 χ = 0) ∧
      (∀ I I' : ZMod m × ZMod m, I' ∈ MulAction.orbit K I → ∀ χ ∈ BB,
        c I'.1 I'.2 χ = c I.1 I.2 χ) ∧
      (∀ j : ZMod m, j = 0 ∨ (∃ h ∈ J, j = h) ∨
        ∃ r ∈ Finset.Ico 1 M, j = -(2 * (r : ZMod m))) ∧
      (∀ I : ZMod m × ZMod m, I = (0, 0) ∨
        I ∈ MulAction.orbit K ((M : ZMod m), (M : ZMod m)) ∨
        (∃ r ∈ Finset.Ico 1 M, I ∈ MulAction.orbit K ((r : ZMod m), (r : ZMod m)) ∨
          I ∈ MulAction.orbit K ((r : ZMod m) + M, (r : ZMod m) + M)) ∨
        ∃ I' ∈ V, I ∈ MulAction.orbit K I') ∧
      ∀ j : ZMod m, ∀ χ ∈ BB, X j χ + 2 * Fs j χ = Cl 0 χ - Cl (-j) χ := by
    refine ⟨fun χ _ => ⟨hc00 χ, ?_, ?_⟩, fun I I' hI' χ _ =>
      FlatComplete.c_orbit_eq (fun a' b' => c a' b' χ) (fun a' b' => hcsymm a' b' χ) hI',
      fun j => ?_, fun I => ?_, hrecon⟩
    · show fourierTransform m ζ (fun k => v χ k 0) (0 : ZMod m).val = 0
      rw [ZMod.val_zero]
      exact fourierTransform_index_zero ζ _
    · show fourierTransform m ζ (fun k => v χ k 1) (0 : ZMod m).val = 0
      rw [ZMod.val_zero]
      exact fourierTransform_index_zero ζ _
    · by_cases hj : j = 0
      · exact Or.inl hj
      · exact Or.inr (FlatComplete.index_cases hm hj)
    · rcases orbit_trichotomy I with h | ⟨ρ, hρ, h⟩ | h
      · left
        have hI : I ∈ MulAction.orbit (dualGroup m) I := MulAction.mem_orbit_self I
        rw [h] at hI
        exact hI
      · right
        have hI : I ∈ MulAction.orbit K (ρ, ρ) := by
          show I ∈ MulAction.orbit (dualGroup m) (ρ, ρ)
          rw [← h]
          exact MulAction.mem_orbit_self I
        by_cases hρM : ρ = M
        · left
          rw [← hρM]
          exact hI
        · right
          left
          obtain ⟨r, hr, hρr | hρr⟩ := FlatComplete.diag_index hm hρ hρM
          · exact ⟨r, hr, Or.inl (hρr ▸ hI)⟩
          · exact ⟨r, hr, Or.inr (hρr ▸ hI)⟩
      · right
        right
        right
        obtain ⟨I', ⟨hI'V, hI'⟩, -⟩ := hVrep I h
        refine ⟨I', hI'V, ?_⟩
        show I ∈ MulAction.orbit (dualGroup m) I'
        rw [MulAction.orbit_eq_iff.mpr hI']
        exact MulAction.mem_orbit_self I
  exact FlatComplete.exists_support BB hm J rfl deg (fun χ => basisDegree_pos basis χ) X Y c V
    Xz cz hXz hcz _ hRdet hD.complete

end CFSG.Wreathed

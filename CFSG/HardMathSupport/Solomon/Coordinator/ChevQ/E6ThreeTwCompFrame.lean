module

public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeTorusGen
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeTwDecRho
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeTwDecSplit

public noncomputable section

namespace CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LocalAnalysis.ComponentInitial CFSG.ClassicalGroups.UnitaryFlag
  CFSG.RankThree.PartOne.KFU CFSG.RankThree.PartOne.KE6 CFSG.RankThree.Classical2
  CFSG.HardMathSupport.Lang.SeitzPlane CFSG.RankThree.PartOne.KD4T
  CFSG.HardMathSupport.Timmesfeld.CrossChar
open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open CFSG.RankThree.PartOne.KE (diagGL3 conjDiag3 card_fixSubfield_twisted rootSpan_commute_of_orth)

open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher (primeFormUnitary)

open CFSG.RankThree.PartOne.KCUnitaryModel (idGram)

open scoped Matrix MatrixGroups

set_option linter.unusedSectionVars false

section Blocks


variable {Ω : Type} [Field Ω]

theorem twFrame_diag_mem_torusGroup (i : Fin 3) {X : SL(3, Ω)}
    (hX : ∀ j k, j ≠ k → (X : Matrix (Fin 3) (Fin 3) Ω) j k = 0) :
    twFrame Ω i X ∈ torusGroup Tag.E6 Ω := by
  have h : CFSG.RankThree.PartOne.TCX.E.e6rhoA2₁ Ω X ∈ torusGroup Tag.E6 Ω :=
    (e6Std_frame Ω).diag X hX
  have h' := (Subgroup.mem_normalizer_iff.1
    (inv_mem (canonicalRep_mem_normalizer (R := Ω) (twE6FrameWeyl i))) _).1 h
  rw [inv_inv] at h'
  rw [twFrame_apply]
  exact h'

theorem twFrame_commute (i j : Fin 3) (hij : i ≠ j) (s t : SL(3, Ω)) :
    twFrame Ω i s * twFrame Ω j t = twFrame Ω j t * twFrame Ω i s :=
  rootSpan_commute_of_orth (Or.inr (Or.inl rfl)) (fun α hα => twE6FrameS_root i hα)
    (fun α hα => twE6FrameS_root j hα) (twE6FrameS_orth hij) _ (twFrame_mem_rootSpan i s) _
    (twFrame_mem_rootSpan j t)

variable (Ω) in
@[expose] def twBlockProd : (Fin 3 → SL(3, Ω)) →* ModGL Tag.E6 Ω :=
  commProd3 (twFrame Ω) twFrame_commute

theorem twBlockProd_apply (X : Fin 3 → SL(3, Ω)) :
    twBlockProd Ω X = twFrame Ω 0 (X 0) * twFrame Ω 1 (X 1) * twFrame Ω 2 (X 2) :=
  rfl

end Blocks

section Package


structure TwCompFrames (K : Type) [Field K] (σ : K ≃+* K) (h₀ : ModGL TwistTag.E6.tag K)
    (L : Fin 3 → Subgroup (ModGL TwistTag.E6.tag K)) (T : Subgroup (ModGL TwistTag.E6.tag K))
    (n : ModGL TwistTag.E6.tag K) {ℓ f : ℕ} (hU : UnitaryFieldData ℓ f K)
    (Fr : AlgebraicClosure K →+* AlgebraicClosure K) (g₀ : ModGL Tag.E6 (AlgebraicClosure K))
    (Hc : Fin 3 → SL(3, AlgebraicClosure K))
    (ρ : Fin 3 → unitarySU ℓ f K 3 →* twistedE6RootGroup K σ)
    (A : Fin 3 → ModGL TwistTag.E6.tag K → primeFormUnitary hU (idGram K 3)) : Prop where
  ne_three : ℓ ≠ 3
  mod_three : ℓ ^ f % 3 = 2
  pic : TwE6ThreeA2Picture K σ (ℓ ^ f) Fr g₀ h₀ L T n
  psi_rho : ∀ i x, twLinePsi K g₀ ((ρ i x : twistedE6RootGroup K σ) : ModGL TwistTag.E6.tag K) =
    twFrame (AlgebraicClosure K) i (twUnitaryFrame hU (Hc i) x)
  injective : ∀ i, Function.Injective (ρ i)
  range : ∀ i, (ρ i).range.map (twistedE6RootGroup K σ).subtype = L i
  realizes : ∀ i, ∀ τ ∈ twTorusHat K σ g₀, ∃ d : Fin 3 → (AlgebraicClosure K)ˣ,
    (∀ X, twLinePsi K g₀ τ * twFrame (AlgebraicClosure K) i X * (twLinePsi K g₀ τ)⁻¹ =
      twFrame (AlgebraicClosure K) i (conjDiag3 d X)) ∧
      TwDiagRealizes (Hc i) d (A i τ : GL (Fin 3) K)
  act : ∀ i, ∀ τ ∈ twTorusHat K σ g₀, ∀ w : unitarySU ℓ f K 3,
    τ * ((ρ i w : twistedE6RootGroup K σ) : ModGL TwistTag.E6.tag K) * τ⁻¹ =
      ((ρ i (conjSU hU (A i τ) w) : twistedE6RootGroup K σ) : ModGL TwistTag.E6.tag K)

variable {K : Type} [Field K] {σ : K ≃+* K} {h₀ : ModGL TwistTag.E6.tag K}
  {L : Fin 3 → Subgroup (ModGL TwistTag.E6.tag K)} {T : Subgroup (ModGL TwistTag.E6.tag K)}
  {n : ModGL TwistTag.E6.tag K} {ℓ f : ℕ} {hU : UnitaryFieldData ℓ f K}
  {Fr : AlgebraicClosure K →+* AlgebraicClosure K} {g₀ : ModGL Tag.E6 (AlgebraicClosure K)}
  {Hc : Fin 3 → SL(3, AlgebraicClosure K)}
  {ρ : Fin 3 → unitarySU ℓ f K 3 →* twistedE6RootGroup K σ}
  {A : Fin 3 → ModGL TwistTag.E6.tag K → primeFormUnitary hU (idGram K 3)}

theorem TwCompFrames.psi_layerProd (F : TwCompFrames K σ h₀ L T n hU Fr g₀ Hc ρ A)
    (x : Fin 3 → unitarySU ℓ f K 3) :
    twLinePsi K g₀ (twLayerProd ρ x) =
      twBlockProd (AlgebraicClosure K) (fun j => twUnitaryFrame hU (Hc j) (x j)) := by
  rw [twLayerProd, map_mul, map_mul, F.psi_rho, F.psi_rho, F.psi_rho, twBlockProd_apply]

theorem exists_twCompFrames [Finite K] {q : ℕ} (h3c : ringChar K ≠ 3) (hK : Nat.card K = q ^ 2)
    (h3 : 3 ∣ q + 1) (hl : TwE6ThreeA2Line K σ h₀ L T n) :
    ∃ (ℓ f : ℕ) (hU : UnitaryFieldData ℓ f K) (Fr : AlgebraicClosure K →+* AlgebraicClosure K)
      (g₀ : ModGL Tag.E6 (AlgebraicClosure K)) (Hc : Fin 3 → SL(3, AlgebraicClosure K))
      (ρ : Fin 3 → unitarySU ℓ f K 3 →* twistedE6RootGroup K σ)
      (A : Fin 3 → ModGL TwistTag.E6.tag K → primeFormUnitary hU (idGram K 3)),
      ℓ ^ f = q ∧ TwCompFrames K σ h₀ L T n hU Fr g₀ Hc ρ A := by
  classical
  obtain ⟨q', Fr, g₀, pic⟩ := hl.picture
  obtain ⟨ℓ, f, hU, rfl⟩ := CFSG.GH74.Generic.S1.rcard_exists_unitaryFieldData hK
  have hq' : q' = ℓ ^ f := by
    have h1 := pic.card_eq
    rw [hK] at h1
    exact (Nat.pow_left_injective two_ne_zero h1).symm
  subst hq'
  have hℓ : ℓ.Prime := hU.prime
  have hf : 1 ≤ f := hU.one_le
  haveI : Fact ℓ.Prime := ⟨hℓ⟩
  haveI : CharP K ℓ := hU.charP
  haveI : CharP (AlgebraicClosure K) ℓ :=
    charP_of_injective_algebraMap (algebraMap K (AlgebraicClosure K)).injective ℓ
  have hℓ3 : ℓ ≠ 3 := by
    intro h3'
    apply h3c
    rw [ringChar.eq K ℓ, h3']
  have hq1 : ℓ ^ f % 3 = 2 := by omega
  haveI : Module.Finite (fixSubfield σ) K := Module.Finite.of_finite
  haveI : Algebra.IsAlgebraic (fixSubfield σ) K := Algebra.IsAlgebraic.of_finite _ K
  haveI : IsAlgClosure (fixSubfield σ) (AlgebraicClosure K) :=
    IsAlgClosure.ofAlgebraic (fixSubfield σ) K (AlgebraicClosure K)
  have hkc : Nat.card (fixSubfield σ) = ℓ ^ f := card_fixSubfield_twisted hℓ hf hK σ pic.σ_apply
  choose Φ Hc hΘ hFix using fun i : Fin 3 =>
    twFrame_theta (Ω := AlgebraicClosure K) hf hkc pic.Fr_apply i
  have F : TwFrameFacts ℓ f Fr Φ Hc := ⟨hΘ, hFix⟩
  choose ρ hρ using fun i : Fin 3 => exists_twRho hU pic hl.L_le F i
  have hex : ∀ (i : Fin 3), ∀ τ ∈ twTorusHat K σ g₀,
      ∃ (γ : primeFormUnitary hU (idGram K 3)) (d : Fin 3 → (AlgebraicClosure K)ˣ),
        (∀ X, twLinePsi K g₀ τ * twFrame (AlgebraicClosure K) i X * (twLinePsi K g₀ τ)⁻¹ =
          twFrame (AlgebraicClosure K) i (conjDiag3 d X)) ∧
          TwDiagRealizes (Hc i) d (γ : GL (Fin 3) K) := by
    intro i τ hτ
    obtain ⟨hτC, hτH⟩ := mem_twTorusHat.1 hτ
    obtain ⟨-, hθ⟩ := twLinePsi_inndiag hℓ hf pic hτC
    exact F.exists_realizes hU hℓ3 hq1 i hτH hθ
  choose! A hA using hex
  refine ⟨ℓ, f, hU, Fr, g₀, Hc, ρ, A, rfl, ⟨hℓ3, hq1, pic, hρ,
    fun i => twRho_injective hU (hρ i), fun i => twRho_range hU pic F (hρ i),
    fun i τ hτ => hA i τ hτ, fun i τ hτ w => ?_⟩⟩
  obtain ⟨d, hd, hreal⟩ := hA i τ hτ
  apply twLinePsi_injective K g₀
  rw [map_mul, map_mul, map_inv, hρ i w, hρ i (conjSU hU (A i τ) w)]
  exact TwFrameFacts.act hU i hd hreal w

end Package

end CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three

end

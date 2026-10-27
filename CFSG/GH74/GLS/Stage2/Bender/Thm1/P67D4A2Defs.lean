module

public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67D4PlaneToral
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87GenCell
public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67D4Toral
public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67D4MonoNF
public import CFSG.GH74.GLS.Stage4.HexModelD4
public import CFSG.LieType.Steinberg.CentralExt.TrialityCoprime
public import CFSG.Timmesfeld.RankTwo.ModelD43Weyl
public import CFSG.GH74.GLS.IVK.Proofs2.OddTools
public import CFSG.GH74.GLS.Stage2.Bender.Thm1.Der61a
public import CFSG.GH74.GLS.Stage2.Bender.Thm1.Der69
public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67Red
public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67RedAut
public import CFSG.GH74.GLS.Stage2.Bender.Thm1.Prop67
public import CFSG.GH74.GLS.Stage2.Bender.Thm1.Statements
public import CFSG.GH74.GLS.Stage2.Bender.Thm1.Stmt7
public import CFSG.GH74.GLS.Stage2.Local.P34Main
public import CFSG.GH74.GLS.Stage2.Local.P34S5A
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87CoatomAbs
public import CFSG.LieType.Chevalley.EvenTrialityOuterInvolutions
public import CFSG.LinearAlgebra.OddSolvableUnitary.HomologySaturation
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogG2EvenCanonicalField
public import CFSG.RankThree.Chevalley.SteinbergCDTrialityTwelveLocalCore
public import CFSG.RankThree.Chevalley.SteinbergCFOddG2SplitInnerActor
public import CFSG.RankThree.PartOne.KC.UnitaryPlaneOrthogonal
public import CFSG.RankThree.PartOne.KGD.D4QFrame
public import CFSG.RankThree.PartOne.KGD.D4T36Frame
public import CFSG.Sporadic.ThSchreier.AutCore

public noncomputable section

namespace CFSG.GH74.GLS.Stage2.Bender.Thm1

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg
  CFSG.LieType.Steinberg.Adjoint CFSG.LieType.Steinberg.TwistedD4
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

variable {K : Type} [Field K]

@[expose] def a2S (d : Kˣ) : ModGL TwistTag.D4.tag K :=
  rootDiagUnit TwistTag.D4.tag ![1, 1, d, 1]

@[expose] def a2Conj (σ : K ≃+* K) (d : Kˣ) (g : ModGL TwistTag.D4.tag K) :
    ModGL TwistTag.D4.tag K :=
  a2S d * Units.map (entrywiseHom σ.toRingHom) g * (a2S d)⁻¹

structure A2Std [Finite K] (σ : K ≃+* K) (d : Kˣ) (q : ℕ) : Prop where
  two_le : 2 ≤ q
  card : Nat.card K = q ^ 3
  frob : ∀ c, σ c = c ^ q
  mod3 : q % 3 = 1
  odd : ringChar K ≠ 2
  fixed : Units.map σ.toRingHom.toMonoidHom d = d
  cube : d ^ 3 = 1
  ne_one : d ≠ 1

structure A2Core [Finite K] (σ : K ≃+* K) (d : Kˣ) (q : ℕ) : Prop where
  two_le : 2 ≤ q
  card : Nat.card K = q ^ 3
  frob : ∀ c, σ c = c ^ q
  mod3 : q % 3 = 1
  twisted_eq :     (twistedGroup σ.toRingHom).map (adjointGroup d4 K).subtype =
      graphFixedRootGroup TwistTag.D4 K σ.toRingHom
  fixed : Units.map σ.toRingHom.toMonoidHom d = d
  cube : d ^ 3 = 1
  ne_one : d ≠ 1

theorem A2Std.toCore [Finite K] {σ : K ≃+* K} {d : Kˣ} {q : ℕ} (h : A2Std σ d q) :
    A2Core σ d q :=
  ⟨h.two_le, h.card, h.frob, h.mod3,
    CFSG.LieType.Steinberg.CentralExt.TrialityClosed.map_twistedGroup_eq_graphFixedRootGroup
      (σ := σ.toRingHom) h.odd h.two_le h.card (fun c => h.frob c),
    h.fixed, h.cube, h.ne_one⟩

@[expose] def a2Char (d : Kˣ) (β : Fin d4.rank → ℤ) : K := ((d ^ β (nd 2) : Kˣ) : K)

theorem a2Conj_mul (σ : K ≃+* K) (d : Kˣ) (g h : ModGL TwistTag.D4.tag K) :
    a2Conj σ d (g * h) = a2Conj σ d g * a2Conj σ d h := by
  simp only [a2Conj, map_mul]
  group

theorem a2Conj_inv (σ : K ≃+* K) (d : Kˣ) (g : ModGL TwistTag.D4.tag K) :
    a2Conj σ d g⁻¹ = (a2Conj σ d g)⁻¹ := by
  simp only [a2Conj, map_inv]
  group

theorem a2Conj_one (σ : K ≃+* K) (d : Kˣ) : a2Conj σ d (1 : ModGL TwistTag.D4.tag K) = 1 := by
  simp [a2Conj]

end CFSG.GH74.GLS.Stage2.Bender.Thm1

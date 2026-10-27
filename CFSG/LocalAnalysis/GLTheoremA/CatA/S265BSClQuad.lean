module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.S265BSClComp
public import CFSG.LocalAnalysis.GLTheoremA.CatA.S265BSClPrim
public import CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.Basic
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma28
public import CFSG.HardMathSupport.Solomon.LocalBalance.Sec5Statements
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcInnerResiduals
public import CFSG.LieType.Chevalley.EvenTrialityOuterInvolutions
public import CFSG.LieType.Chevalley.OddTrialityCosetInvolutions
public import CFSG.LieType.SeitzGeneration.ExtSeitzReeF4Cyclic
public import CFSG.LocalAnalysis.AGLEmbedding.CaseThreeFamilies
public import CFSG.LocalAnalysis.AGLEmbedding.ResidualTools
public import CFSG.LocalAnalysis.ComponentClassification.AutL2FactsCentModel
public import CFSG.LocalAnalysis.ComponentClassification.AutL2FactsFieldAut
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueUStatement
public import CFSG.LocalAnalysis.ComponentClassification.GSLitType
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCorrCentralSylowMaximality
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedGSAContainedSource
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedLayerOddCoreUnbalancingTriple
public import CFSG.LocalAnalysis.GL83PartI.I_22_5.Setup
public import CFSG.LocalAnalysis.GLTheoremB.Lemma99Core
public import CFSG.LocalAnalysis.QuasithinUnique.SQTK.TypeB2
public import CFSG.LocalAnalysis.QuasithinUnique.SQTK.Unitary
public import CFSG.RankThree.CentralLiftSO.SplitTorusWeyl
public import CFSG.RankThree.PartOne.BRANCH.RankRee
public import CFSG.RankThree.PartOne.CTP.StrongPBridgeRest
public import CFSG.RankThree.PartOne.KC.LinearCommutatorOdd
public import CFSG.RankThree.PartOne.KC.LinearDegreeFive
public import CFSG.RankThree.PartOne.KC.UnitaryHigherCrossPrimeTorus
public import CFSG.RankThree.PartOne.KC.UnitaryPlaneEndpoints
public import CFSG.RankThree.PartOne.KD4T.Certs
public import CFSG.RankThree.PartOne.KE.StabGeneral
public import CFSG.RankThree.PartOne.N143.Weyl613Defs
public import CFSG.RankThree.PartOne.N143X.KF64WSimple
public import CFSG.RankThree.PartOne.S11d.OutExceptional
public import CFSG.RankThree.PartOne.S11d.OutLinear
public import CFSG.RankThree.PartTwo.KFacts.KS14SzLie
public import CFSG.RankThree.SteinbergR3EOrthogonalCoprimeCyclic
public import CFSG.SignalizerFunctorTheorem.Nonsolvable.SolComponent
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.IV.theorem_3_3
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.IG1114
public import CFSG.ThirdParty.QiuzhenCFSG.Glauberman.TheoremB
public import CFSG.ThirdParty.QiuzhenCFSG.Glauberman.TheoremC
public import CFSG.ThirdParty.QiuzhenCFSG.Glauberman.ZJTheorem
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.GW1965RemarkDGroup
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.Lemma29
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.Lemma29Helpers
public import Certificates.Certificate1
public import Certificates.Certificate2

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S265.BSCl

open Module QuadraticMap CFSG.Open CFSG.RankThree.PartOne CFSG.RankThree.PartOne.KCPrimary
  CFSG.RankThree.PartOne.KCOrthogonal CFSG.HardMathSupport.Timmesfeld.CrossChar
open CFSG.LocalAnalysis.GLTheoremA.Y10F.HypBlocks (fixedByEnd mem_fixedByEnd)

variable {F V : Type} [Field F] [Finite F] [AddCommGroup V] [Module F V] [FiniteDimensional F V]

theorem glaPLayer_inf_ne_bot_of_quadratic (hF : Nat.card F = 2) (hV : finrank F V = 10)
    {Q : QuadraticForm F V} (hQ : (polarBilin Q).Nondegenerate)
    {d e : V ≃ₗ[F] V} (hd3 : d ^ 3 = 1) (he3 : e ^ 3 = 1) (hde : d * e = e * d)
    (hdQ : ∀ v, Q (d v) = Q v) (heQ : ∀ v, Q (e v) = Q v)
    (hd : fixedByEnd d = ⊥) (he : finrank F ↥(fixedByEnd e) = 8)
    {X : Subgroup (V ≃ₗ[F] V)}
    (hX : ∀ a : V ≃ₗ[F] V, (∀ v, Q (a v) = Q v) → a ^ 3 = 1 → finrank F ↥(fixedSpace a) = 2 →
      specialBlock Q a (cyc3 F) ≤ X)
    (hXQ : ∀ g ∈ X, g * d = d * g → g * e = e * g → ∀ v, Q (g v) = Q v) :
    GLAPLayer 3 (X ⊓ Subgroup.centralizer ({d} : Set (V ≃ₗ[F] V)) ⊓
      Subgroup.centralizer ({e} : Set (V ≃ₗ[F] V))) ≠ ⊥ := by
  obtain ⟨k, hk2, hkp⟩ := exists_pow_mul_fixedSpace_eq_two hF hV he3 hde hd he
  have hdc : Commute d (e ^ k) := (show Commute d e from hde).pow_right k
  have hepow : ∀ (n : ℕ) (v : V), Q ((e ^ n) v) = Q v := fun n => by
    induction n with
    | zero => intro v; rfl
    | succ n ih => intro v; rw [pow_succ, LinearEquiv.mul_apply, ih, heQ]
  have hae : (d * e ^ k) * e = e * (d * e ^ k) :=
    ((show Commute d e from hde).mul_left ((Commute.refl e).pow_left k)).eq
  have ha3 : (d * e ^ k) ^ 3 = 1 := by
    rw [Commute.mul_pow hdc, hd3, one_mul, ← pow_mul, mul_comm, pow_mul, he3, one_pow]
  have haQ : ∀ v, Q ((d * e ^ k) v) = Q v := fun v => by
    rw [LinearEquiv.mul_apply, hdQ, hepow]
  have hgd : ∀ g : V ≃ₗ[F] V, g * (d * e ^ k) = (d * e ^ k) * g → g * e = e * g → g * d = d * g :=
    fun g hga hge => by
      have hgek : Commute g (e ^ k) := (show Commute g e from hge).pow_right k
      have h : d = (d * e ^ k) * (e ^ k)⁻¹ := (mul_inv_cancel_right d (e ^ k)).symm
      rw [h]
      exact (show Commute g (d * e ^ k) from hga).mul_right hgek.inv_right
  have hsub : X ⊓ Subgroup.centralizer ({d * e ^ k} : Set (V ≃ₗ[F] V)) ⊓
      Subgroup.centralizer ({e} : Set (V ≃ₗ[F] V)) =
      X ⊓ Subgroup.centralizer ({d} : Set (V ≃ₗ[F] V)) ⊓
        Subgroup.centralizer ({e} : Set (V ≃ₗ[F] V)) := by
    ext g
    simp only [Subgroup.mem_inf, Subgroup.mem_centralizer_singleton_iff]
    refine ⟨fun ⟨⟨hgX, hga⟩, hge⟩ => ⟨⟨hgX, hgd g hga hge⟩, hge⟩,
      fun ⟨⟨hgX, hgd'⟩, hge⟩ => ⟨⟨hgX, ?_⟩, hge⟩⟩
    exact (show Commute g (d * e ^ k) from (show Commute g d from hgd').mul_right
      ((show Commute g e from hge).pow_right k)).eq
  rw [← hsub]
  exact glaPLayer_inf_ne_bot_of_specialBlock hF hQ haQ ha3 hae (by omega) hkp
    (hX _ haQ ha3 hk2) fun g hg hga hge => hXQ g hg (hgd g hga hge) hge

end CFSG.LocalAnalysis.GLTheoremA.S265.BSCl

end

module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34FactsGMStep
public import CFSG.LocalAnalysis.ComponentClassification.GoldschmidtTDGriess
public import CFSG.LocalAnalysis.EvenSporadicStandard.CentralTwoFinal
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34REvenOut
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34RSuz
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34FactsPFHolds
public import CFSG.GH74.GLS.C3.Layer1.St1RigOrd
import CFSG.LocalAnalysis.ComponentClassification.Walter86.GLSPumpupFoote
import CFSG.RankThree.PartOne.SPOR.Final
import CFSG.GH74.GLS.C3.Layer1.St1RigMain

public section

namespace CFSG.ComponentClassification.GrSLit.L34Terminal

open CFSG Subgroup
open scoped commutatorElement

theorem exists_twoTerminal_same_full_cover
    (X : Type) [Group X] [Finite X]
    (hKProper : CFSG.Assembly.KProper CFSG.Blueprint.Catalog X)
    (hNoncentral : ∀ z : X, orderOf z = 2 → z ∉ Subgroup.center X)
    (hRank : ∀ z : X, orderOf z = 2 →
      3 ≤ CFSG.pRank 2 ↥(Subgroup.centralizer ({z} : Set X)))
    (b : X) (K : Subgroup X)
    (hIL2 : CFSG.GH74.GLS.IsIL2Pair b K)
    (hLie : CFSG.Blueprint.LieModel (↥K ⧸ CFSG.Open.fusionZStar ↥K) .PSL 3 2 2)
    (hIndex : (CFSG.pPrimeCore 2 ↥K).index = 322560) :
(CFSG.pPrimeCore 2 ↥K).index = 322560 ∧
    CFSG.GH74.GLS.IsPRigid 2 b K ∧
    ∃ (t : X) (L : Subgroup X),
      CFSG.GH74.GLS.LongPumpUp 2 b K t L ∧
      CFSG.GH74.GLS.IsPRigid 2 t L ∧
      CFSG.GH74.GLS.C3.Layer1.PumpRigid.IsGilmanMax t L ∧
      CFSG.GH74.GLS.IsTwoTerminal t L ∧
      Nonempty ((↥L ⧸ CFSG.pPrimeCore 2 ↥L) ≃*
        (↥K ⧸ CFSG.pPrimeCore 2 ↥K)) ∧
      (CFSG.pPrimeCore 2 ↥L).index = 322560 ∧
      CFSG.Blueprint.LieModel (↥L ⧸ CFSG.Open.fusionZStar ↥L) .PSL 3 2 2 ∧
      Nat.card ↥(Subgroup.center (↥L ⧸ CFSG.pPrimeCore 2 ↥L)) = 16 := by
  classical
  have hS : CFSG.LocalAnalysis.ComponentInitial.SchreierFor CFSG.Blueprint.Catalog :=
    CFSG.RankThree.PartOne.SPOR.schreierFor_catalog
  have hCT : CFSG.ComponentClassification.GrSLit.L34ProperFixedCenterTrivial :=
    l34ProperFixedCenterTrivial_of_inputs
        CFSG.ComponentClassification.TBLit.griessMultipliersAllModels_holds
        CFSG.EvenSporadicStandard.centralTwoBound gls3OddLieAutComponentsInput_holds
        evenLieExcOuterL34Input_holds suzDoubleCoverL34Input_holds
  have hPFS : CFSG.ComponentClassification.GrSLit.L34ProperFixedSimpleRank :=
    CFSG.ComponentClassification.GrSLit.l34ProperFixedSimpleRank_holds
  have hILo : CFSG.GH74.GLS.IsILo 2 b K :=
    ⟨hIL2.1, by simpa [CFSG.GH74.GLS.oBound] using hRank b hIL2.1, hIL2.2⟩
  have hchainAux : ∀ (p q : X × Subgroup X),
      Relation.ReflTransGen
        (fun c d : X × Subgroup X => CFSG.GH74.GLS.PumpUpLT 2 c.1 c.2 d.1 d.2) p q →
      p = (b, K) →
      (CFSG.pPrimeCore 2 ↥q.2).index = 322560 ∧
        CFSG.ComponentClassification.GrSLit.IsL34Type
          (q.2 ⧸ CFSG.Open.fusionZStar q.2) := by
    intro p q h
    induction h with
    | refl =>
        intro hp
        subst hp
        exact ⟨hIndex, hLie⟩
    | tail _ hstep ih =>
        intro hp
        obtain ⟨hidxprev, htypeprev⟩ := ih hp
        have hcorr := CFSG.ComponentClassification.Walter86.gsWeakCorr_of_pumpUpLT hstep
        obtain ⟨⟨e⟩, hidxnext⟩ :=
          CFSG.ComponentClassification.GrSLit.L34GM.step_of_gsWeakCorr hS hCT hPFS hKProper
            hcorr (hNoncentral _ hstep.2.1.1) htypeprev hidxprev
        exact ⟨hidxnext, CFSG.LieType.CurtisTits.lieModel_of_mulEquiv e htypeprev⟩
  have hchain : ∀ (t : X) (L : Subgroup X),
      Relation.ReflTransGen
        (fun c d : X × Subgroup X => CFSG.GH74.GLS.PumpUpLT 2 c.1 c.2 d.1 d.2)
        (b, K) (t, L) →
      (CFSG.pPrimeCore 2 ↥L).index = 322560 ∧
        CFSG.ComponentClassification.GrSLit.IsL34Type (L ⧸ CFSG.Open.fusionZStar L) := by
    intro t L h
    exact hchainAux (b, K) (t, L) h rfl
  have hrig : CFSG.GH74.GLS.IsPRigid 2 b K := by
    refine ⟨hILo, ?_⟩
    intro t L hlong
    have hle : CFSG.GH74.GLS.TwoThin.hatCard L ≤ CFSG.GH74.GLS.TwoThin.hatCard K := by
      obtain ⟨hidxL, -⟩ := hchain t L hlong.2
      have hLcard : CFSG.GH74.GLS.TwoThin.hatCard L = 322560 := by
        show Nat.card (↥L ⧸ CFSG.pPrimeCore 2 ↥L) = 322560
        rw [← Subgroup.index_eq_card, hidxL]
      have hKcard : CFSG.GH74.GLS.TwoThin.hatCard K = 322560 := by
        show Nat.card (↥K ⧸ CFSG.pPrimeCore 2 ↥K) = 322560
        rw [← Subgroup.index_eq_card, hIndex]
      rw [hLcard, hKcard]
    exact CFSG.GH74.GLS.C3.Layer1.PumpRigid.hat_equiv_of_chain hlong.2 hle
  obtain ⟨t, L, hlong, hrigL, hgm⟩ :=
    CFSG.GH74.GLS.C3.Layer1.PumpRigid.exists_rigid_gilman hrig
  have hT2 : CFSG.GH74.GLS.IsTwoTerminal t L :=
    CFSG.GH74.GLS.C3.Layer1.PumpRigid.isTwoTerminal_of_noDiag hrigL hgm
      (CFSG.GH74.GLS.C3.Layer1.PumpRigid.noDiag_of_rigid_gilman hRank hrigL hgm)
  obtain ⟨eFull⟩ := hrig.2 t L hlong
  obtain ⟨hidxL, htypeL⟩ := hchain t L hlong.2
  have hILoL : CFSG.GH74.GLS.IsILo 2 t L :=
    CFSG.GH74.GLS.C3.Layer1.PumpRigid.LongPumpUp.isILo_right hlong
  have hperf : ⁅L, L⁆ = L :=
    CFSG.ComponentClassification.UnbalancedCorr.commutator_eq_of_isPComponent
      hILoL.2.2.1 hILoL.2.2.2
  have hcenter16 : Nat.card ↥(Subgroup.center (↥L ⧸ CFSG.pPrimeCore 2 ↥L)) = 16 :=
    (CFSG.ComponentClassification.GrSLit.L34GM.card_center_of_index hperf htypeL).mp hidxL
  exact ⟨hIndex, hrig, t, L, hlong, hrigL, hgm, hT2, ⟨eFull⟩, hidxL, htypeL, hcenter16⟩

end CFSG.ComponentClassification.GrSLit.L34Terminal

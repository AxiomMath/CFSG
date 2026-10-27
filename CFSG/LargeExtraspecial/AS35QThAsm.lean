module

public import CFSG.LargeExtraspecial.AS35QThCompl
public import CFSG.LargeExtraspecial.AS35QThPhi
public import Certificates.Kernel.ThCent.Leaves
public import CFSG.Fischer.NoF25.Local
public import CFSG.Goldschmidt.Statements
public import CFSG.Goldschmidt.StatementsG4
public import CFSG.Goldschmidt.StatementsH
public import CFSG.GroupTheory.ABGLocalTools.PStabilityDefs
public import CFSG.LargeExtraspecial.AS35HInd
public import CFSG.LargeExtraspecial.AS35HMain
public import CFSG.LargeExtraspecial.AS35LMain
public import CFSG.LargeExtraspecial.BridgeSetting
public import CFSG.LargeExtraspecial.GLRElimInv
public import CFSG.LargeExtraspecial.GLRTransfer
public import CFSG.LargeExtraspecial.OrthoF2
public import CFSG.LargeExtraspecial.S10Five
public import CFSG.LargeExtraspecial.S10FourA
public import CFSG.LargeExtraspecial.S10SixA
public import CFSG.LargeExtraspecial.S10Three
public import CFSG.LargeExtraspecial.S12InspSplit
public import CFSG.LargeExtraspecial.S14W4LocInst
public import CFSG.LargeExtraspecial.S14W4LocRed
public import CFSG.LargeExtraspecial.S4EightA
public import CFSG.LargeExtraspecial.S4EightB
public import CFSG.LargeExtraspecial.S4EightC
public import CFSG.LargeExtraspecial.S4EightD
public import CFSG.LargeExtraspecial.S4EightE
public import CFSG.LargeExtraspecial.S5Three
public import CFSG.LargeExtraspecial.S6SevenC
public import CFSG.LargeExtraspecial.S8FusE
public import CFSG.LargeExtraspecial.S8Lin
public import CFSG.LieType.Chevalley.RootCommutator
public import CFSG.LinearAlgebra.LinearGroups.CoordinateData
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBDerivedNormalSectionBound
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointActionModels
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointDataModelWitness
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalSemilinearDataCompatibility
public import CFSG.LocalAnalysis.ComponentClassification.CentralCoverLemmasAFaithful
public import CFSG.LocalAnalysis.ComponentInitial.CentralCoverAbelian
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherEvenOrthogonalModel
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.AschbacherCanonicalRemaining
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.ExceptionalEightPlaneCentralizer
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.UnitaryRootAutomorphism
public import CFSG.Milestones.CL_LIT_Goldschmidt_strongly_closed_abelian_models
public import CFSG.Open.QuasithinDefs
public import CFSG.Permutation.BurnsideSchur
public import CFSG.RankThree.Literature.FSmithTheorem2
public import CFSG.Sporadic.Co2Smith.CClosure
public import CFSG.Sporadic.Co2Smith.CTree
public import CFSG.Sporadic.Co2Smith.ClassCountFin
public import CFSG.Sporadic.Co2Smith.GlAssembly
public import CFSG.Sporadic.Co2Smith.HPTree
public import CFSG.Sporadic.FischerOddCore.Fi24AlmostSimple
public import CFSG.Sporadic.FischerOddCore.Fi24R2CompBase
public import CFSG.Sporadic.FischerOddCore.FischerOuterBasic
public import CFSG.Sporadic.Schreier.MathieuOddCoreWords
public import CFSG.Sporadic.Th.KernelCentralizer
public import CFSG.Sporadic.ThSchreier.GlobalData
public import CFSG.Sporadic.ThSchreier.LocalOrbitBase1
public import CFSG.Sporadic.ThSchreier.Max3Action
public import CFSG.Sporadic.ThSchreier.Max3ActionBase1
public import CFSG.Sporadic.ThSchreier.Rigidity
public import CFSG.Timmesfeld.RankOne
public import CFSG.Timmesfeld.Special.TwoCore
public import CFSG.Walter.J1Recog
public import CFSG.Walter.Ree.Thompson2.BaseFin
public import CFSG.Walter.ReeOrder.WardLocal
public import CFSG.Walter.W67.Section8.Prop83
public import Certificates.Certificate7000
public import Certificates.Certificate7001
public import Certificates.Certificate7002
public import Certificates.Certificate7003
public import Certificates.Certificate7004
public import Certificates.Certificate7005
public import Certificates.Certificate7006
public import Certificates.Certificate7007
public import Certificates.Certificate7008
public import Certificates.Certificate7009
public import Certificates.Certificate7010
public import Certificates.Certificate7011
public import Certificates.Certificate8046
public import Certificates.Certificate8049
public import Certificates.Certificate8052
public import Certificates.Data.CFSGNative.Co2Smith.Orbit8
public import TauCeti.LinearAlgebra.QuadraticForm.OrthogonalBasis

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.AS35QTh

open Subgroup CFSG.Fischer.Classification.Unitary CFSG.ClassicalGroups.Unitary
open CFSG.Blueprint.Fischer (K)

variable {G : Type} [Group G] [Finite G] {S : Setting G}

namespace ThLift

variable (T : ThLift S)

theorem exists_mem_compl {Kc : Subgroup G} (hKC : Kc ≤ T.CZ)
    (hKc : ∀ c ∈ T.CZ, c ∈ Kc ∨ c * S.z ∈ Kc) (σ : S.Mbar) :
    ∃ k : Kc, T.rhoC (inclusion hKC k) = σ := by
  obtain ⟨c, hc⟩ := T.rhoC_surjective σ
  rcases hKc c c.2 with h | h
  · exact ⟨⟨c, h⟩, hc⟩
  · refine ⟨⟨c * S.z, h⟩, ?_⟩
    have e : inclusion hKC ⟨(c : G) * S.z, h⟩ = c * ⟨S.z, T.z_mem_CZ⟩ := rfl
    have hz1 : T.rhoC ⟨S.z, T.z_mem_CZ⟩ = 1 :=
      Subtype.ext ((S.ρ_eq_one_iff ⟨S.z, (T.mem_CZ.mp T.z_mem_CZ).2⟩).mpr S.z_mem_QG)
    rw [e, map_mul, hz1, mul_one, hc]

include T in
theorem nonempty_thData (hP : S14.Asc512PbarStmt) (hS : S.SixHyp) : Nonempty (ThData S) := by
  obtain ⟨Kc, hKC, hzK, hKc⟩ := T.exists_compl hP hS
  set rK : Kc →* GU3 := T.theta.comp (T.rhoC.comp (inclusion hKC)) with hrK
  have hinj : Function.Injective rK := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro k hk
    rw [MonoidHom.mem_ker, hrK, MonoidHom.comp_apply] at hk
    have h1 : T.rhoC (inclusion hKC k) = 1 :=
      (T.theta_bijective hP hS).1 (by rw [map_one]; exact hk)
    have hkM := (T.mem_CZ.mp (hKC k.2)).2
    have h2 : S.ρ ⟨k, hkM⟩ = 1 := congrArg Subtype.val h1
    have hkQ := (S.ρ_eq_one_iff ⟨k, hkM⟩).mp h2
    rcases T.eq_one_or_z_of_commute hkQ (T.mem_CZ.mp (hKC k.2)).1 with h | h
    · exact Subgroup.mem_bot.mpr (Subtype.ext h)
    · exact absurd (h ▸ k.2) hzK
  have hsurj : Function.Surjective rK := by
    intro A
    obtain ⟨σ, hσ⟩ := (T.theta_bijective hP hS).2 A
    obtain ⟨k, hk⟩ := T.exists_mem_compl hKC hKc σ
    exact ⟨k, by rw [hrK, MonoidHom.comp_apply, MonoidHom.comp_apply, hk, hσ]⟩
  set e := MulEquiv.ofBijective rK ⟨hinj, hsurj⟩ with he
  set κ : GU3 →* G := Kc.subtype.comp e.symm.toMonoidHom with hκ
  have hκM : ∀ A, κ A ∈ S.M := fun A => (T.mem_CZ.mp (hKC (e.symm A).2)).2
  have hκv : ∀ A, κ A = (e.symm A : G) := fun A => rfl
  have hrKe : ∀ A, rK (e.symm A) = A := fun A => e.apply_symm_apply A
  refine ⟨{
    toSecData := T.secData
    κ := κ
    hκM := hκM
    hκ := fun A x => ?_
    hκZ := fun A => (T.mem_CZ.mp (hKC (e.symm A).2)).1
    hall := fun m hm => ?_ }⟩
  · change S.rhoL (hκM A) (T.l x) = T.l (gv A x)
    have h1 : T.theta (T.rhoC (inclusion hKC (e.symm A))) = A := hrKe A
    conv_rhs => rw [← h1, T.l_gv_theta]
    rfl
  · obtain ⟨k, hk⟩ := T.exists_mem_compl hKC hKc ⟨S.ρ ⟨m, hm⟩, ⟨_, rfl⟩⟩
    refine ⟨rK k, fun v => ?_⟩
    have hek : e.symm (rK k) = k := e.symm_apply_apply k
    have e1 : (⟨κ (rK k), hκM (rK k)⟩ : S.M) = ⟨k, (T.mem_CZ.mp (hKC k.2)).2⟩ :=
      Subtype.ext (by change κ (rK k) = (k : G); rw [hκv, hek])
    have e2 : S.ρ ⟨k, (T.mem_CZ.mp (hKC k.2)).2⟩ = S.ρ ⟨m, hm⟩ := congrArg Subtype.val hk
    simp only [Setting.rhoL]
    rw [e1, e2]

end ThLift

end CFSG.LargeExtraspecial.AS35QTh

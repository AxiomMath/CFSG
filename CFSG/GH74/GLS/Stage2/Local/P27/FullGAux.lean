module

public import CFSG.GH74.GLS.Stage2.Local.P27.FullFBuild
import CFSG.RankThree.Transfer.Yoshida
import CFSG.GH74.GLS.Stage2.Signalizer.L52TwoCov
public import CFSG.CGT.Timmesfeld75.L2Pair
public import CFSG.CGT.Timmesfeld75.ListWCBasic
public import CFSG.CharacterTheory.CyclicBlocks.Family
public import CFSG.CharacterTheory.Semidihedral.Principal.LargePrimeTorusSylowCentralizers
public import CFSG.CharacterTheory.Semidihedral.Principal.PrimeTorusBlockAlignment
public import CFSG.CharacterTheory.Wreathed.FourPointInvolutionHexagon
public import CFSG.CharacterTheory.Wreathed.OrderThirtyTwoWreathFusion
public import CFSG.ClassicalGroups
public import CFSG.Combinatorics.AperiodicCentralInvolution
public import CFSG.Combinatorics.AperiodicFiveOfSix
public import CFSG.Combinatorics.AperiodicOppositeComponents
public import CFSG.Combinatorics.AperiodicSixteenGraphDistances
public import CFSG.Combinatorics.OuterLayerPredecessors
public import CFSG.GH74.BNPair.Defs
public import CFSG.GH74.GLS.C3.Layer1.Split
public import CFSG.GH74.GLS.C3.Layer3.Main
public import CFSG.GH74.GLS.Defs
public import CFSG.GH74.GLS.Stage1.Thm3.Sec5.Closed
public import CFSG.GH74.GLS.Stage1.Thm3.Sec5.Statements
public import CFSG.GH74.GLS.Stage1.Thm6.Sec12.Defs
public import CFSG.GH74.GLS.Stage1.Thm6.Sec12.Ext
public import CFSG.GH74.GLS.Stage2.Local.P34Main
public import CFSG.GH74.GLS.Stage2.Local.P34Perf
public import CFSG.GH74.GLS.Stage2.Local.P34S5SE
public import CFSG.GH74.GLS.Stage2.Local.Prop22
public import CFSG.GroupTheory.PCore.PrimeSetCore
public import CFSG.LinearAlgebra.LinearGroups.UnitaryThreeOverNine
public import CFSG.LinearAlgebra.LinearGroups.UnitaryThreeOverNineInvolutions
public import CFSG.LocalAnalysis.ComponentClassification.GSThmB58Section
public import CFSG.LocalAnalysis.ComponentClassification.GSThmB58SubBasic
public import CFSG.LocalAnalysis.ComponentClassification.GSThmBCentral
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec4Transfer
public import CFSG.LocalAnalysis.LargeEvenClassification.Delta
public import CFSG.LocalAnalysis.LargeEvenClassification.NormalCoreIntersection
public import CFSG.LocalAnalysis.LargeEvenClassification.WeakCoreAbsorption
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.AschbacherCanonicalRemaining
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.ExceptionalEightPlaneCentralizer
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.Lemma37.JOneRoute
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.Lemma37.NonSquare
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.Lemma37.Remaining
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.Lemma37.WalterRoute
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.TheoremC.TheoremC
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.UnitaryRootAutomorphism
public import CFSG.Permutation.BurnsideSchur
public import CFSG.Permutation.UnitaryThreeRecognition.Model
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PSL2NormalizedRootSylowCount
public import CFSG.Timmesfeld.Final.Simple
import CFSG.GH74.GLS.Stage2.Local.Statements

public section

namespace CFSG.GH74.GLS.Stage2.Local.P27

open Subgroup CFSG CFSG.ABGLocalTools CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.GLS.Stage12
  CFSG.GH74.GLS.Stage2.Local
open scoped Pointwise

theorem IsDihedral.of_mulEquiv {Y Y' : Type} [Group Y] [Group Y'] (e : Y ≃* Y') (h : IsDihedral Y) :
    IsDihedral Y' := by
  obtain ⟨m, k, hm, hk, ⟨e'⟩⟩ := h
  exact ⟨m, k, hm, hk, ⟨e.symm.trans e'⟩⟩

theorem mem_normalizer_of_normal {X : Type} [Group X] (K : Subgroup X) [hK : K.Normal] (g : X) :
    g ∈ normalizer (K : Set X) := by
  rw [Subgroup.mem_normalizer_iff]
  intro h
  refine ⟨fun hh => hK.conj_mem h hh g, fun hh => ?_⟩
  have := hK.conj_mem _ hh g⁻¹
  simpa [mul_assoc] using this

theorem inf_sup_normal_le {X : Type} [Group X] {O K T : Subgroup X} [K.Normal]
    (hO : Odd (Nat.card ↥O)) (hT : IsPGroup 2 ↥T) : T ⊓ (O ⊔ K) ≤ K := by
  rintro u ⟨huT, huOK⟩
  obtain ⟨o, ho, k, hk, hou⟩ := Subgroup.mem_sup_of_normal_right.1 huOK
  have hzp : IsPGroup 2 ↥(zpowers u) := hT.to_le ((Subgroup.zpowers_le).2 huT)
  have hmem : o ∈ K ⊔ zpowers u := by
    have h1 : u * k⁻¹ ∈ zpowers u ⊔ K :=
      Subgroup.mul_mem_sup (Subgroup.mem_zpowers u) (K.inv_mem hk)
    have h2 : o = u * k⁻¹ := by rw [← hou]; group
    rw [h2, sup_comm]
    exact h1
  obtain ⟨j, hj⟩ := Signalizer.L52Two.exists_pow_mem_of_sup (L := K) (T := zpowers u) hzp
    (fun g _ => mem_normalizer_of_normal K g) hmem
  have hodd : Odd (orderOf o) := by
    have h1 : orderOf o ∣ Nat.card O := by
      have := orderOf_dvd_natCard (⟨o, ho⟩ : ↥O)
      rwa [Subgroup.orderOf_mk] at this
    exact Odd.of_dvd_nat hO h1
  have hoK : o ∈ K := Signalizer.L52Two.mem_of_odd_orderOf_of_pow_mem hodd hj
  rw [← hou]
  exact K.mul_mem hoK hk

theorem O2Of_le {G : Type} [Group G] (X : Subgroup G) : O2Of X ≤ X := Subgroup.map_subtype_le _

theorem le_normalizer_O2Of {G : Type} [Group G] (X : Subgroup G) :
    X ≤ normalizer ((O2Of X : Subgroup G) : Set G) := by
  intro n hn
  rw [Subgroup.mem_normalizer_iff]
  have key : ∀ m ∈ X, ∀ a ∈ O2Of X, m * a * m⁻¹ ∈ O2Of X := by
    intro m hm a ha
    obtain ⟨a', ha', rfl⟩ := ha
    refine ⟨⟨m, hm⟩ * a' * ⟨m, hm⟩⁻¹,
      (CFSG.RankThree.Transfer.oResidual_normal 2 ↥X).conj_mem a' ha' ⟨m, hm⟩, ?_⟩
    simp
  intro h
  exact ⟨fun hh => key n hn h hh, fun hh => by
    have := key n⁻¹ (X.inv_mem hn) _ hh
    simpa [mul_assoc] using this⟩

theorem le_O2Of_of_perfect {G : Type} [Group G] [Finite G] {X P : Subgroup G} (hPX : P ≤ X)
    (hP : ⁅P, P⁆ = P) : P ≤ O2Of X := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set M : Subgroup ↥X := oResidual 2 ↥X with hM
  have hq : IsPGroup 2 (↥X ⧸ M) :=
    CFSG.RankThree.Transfer.isPGroup_quotient_of_oResidual_le M le_rfl
  have hPperf : Group.IsPerfect ↥P := Subgroup.isPerfect_iff.mpr hP
  have hP'perf : Group.IsPerfect ↥(P.subgroupOf X) :=
    Group.IsPerfect.ofSurjective (f := (Subgroup.subgroupOfEquivOfLe hPX).symm.toMonoidHom)
      (Subgroup.subgroupOfEquivOfLe hPX).symm.surjective
  let q : ↥X →* ↥X ⧸ M := QuotientGroup.mk' M
  let I : Subgroup (↥X ⧸ M) := (P.subgroupOf X).map q
  have hIp : IsPGroup 2 ↥I := hq.to_subgroup I
  have hIperf : Group.IsPerfect ↥I := by
    dsimp [I]
    exact Group.IsPerfect.map q
  have hIbot : I = ⊥ := by
    by_contra hIne
    have : Nontrivial ↥I := (Subgroup.nontrivial_iff_ne_bot I).2 hIne
    exact (Group.IsPerfect.not_isNilpotent (G := ↥I)) hIp.isNilpotent
  intro p hp
  have hpX : p ∈ X := hPX hp
  have hqp : q ⟨p, hpX⟩ = 1 := by
    have hmem : q ⟨p, hpX⟩ ∈ I :=
      Subgroup.mem_map.mpr ⟨⟨p, hpX⟩, Subgroup.mem_subgroupOf.mpr hp, rfl⟩
    exact Subgroup.mem_bot.mp (by simpa [hIbot] using hmem)
  have hpM : (⟨p, hpX⟩ : ↥X) ∈ M := (QuotientGroup.eq_one_iff (N := M) (x := ⟨p, hpX⟩)).1 hqp
  exact ⟨⟨p, hpX⟩, hpM, rfl⟩

theorem isDihedral_sylow_of_inf {G : Type} [Group G] [Finite G] {C T N : Subgroup G}
    (hT : IsSylowOf 2 T C) (hNC : N ≤ C) (hnorm : C ≤ normalizer (N : Set G))
    (hD : IsDihedral ↥(T ⊓ N)) (P : Sylow 2 ↥N) : IsDihedral ↥P := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hTN : IsSylowOf 2 (T ⊓ N) N := hT.inf_of_le_normalizer hNC hnorm
  obtain ⟨Q, hQ⟩ := hTN.exists_sylow_eq_subgroupOf
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq ↥N Q P
  have hPQ : (P : Subgroup ↥N) = (MulAut.conj g) • (Q : Subgroup ↥N) := by
    rw [← hg]; rfl
  let e1 : ↥(P : Subgroup ↥N) ≃* ↥(Q : Subgroup ↥N) :=
    (MulEquiv.subgroupCongr hPQ).trans (Subgroup.equivSMul (MulAut.conj g) (Q : Subgroup ↥N)).symm
  let e2 : ↥(Q : Subgroup ↥N) ≃* ↥(T ⊓ N) :=
    (MulEquiv.subgroupCongr hQ).trans (Subgroup.subgroupOfEquivOfLe inf_le_right)
  exact IsDihedral.of_mulEquiv (e1.trans e2).symm hD

end CFSG.GH74.GLS.Stage2.Local.P27

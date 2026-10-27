module

public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P4S55BTOutS
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87L34Out
public import CFSG.LocalAnalysis.ComponentInitial.LinearModelOuterTwoPart
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryModelOuterTwoPart
public import CFSG.RankThree.SteinbergR3ESuzukiFieldSplitting
public import CFSG.RankThree.PartOne.S11c.Sec66TModelsTw
public import Certificates.Certificate113
public import Certificates.Certificate2022
public import CFSG.GH74.GLS.IVK.Lifted.GroupAux
public import CFSG.GH74.GLS.IVK.Lifted.IIAutB
public import CFSG.GH74.GLS.IVK.Lifted.Outer14
public import CFSG.GH74.GLS.IVK.Lifted.SolvAut
public import CFSG.GH74.GLS.IVK.Lifted.Strong
public import CFSG.GH74.GLS.IVK.Proofs2.OddTools
public import CFSG.GH74.GLS.Stage1.Main.BrFusedBase
public import CFSG.GH74.GLS.Stage1.Main.BrG2Base
public import CFSG.GH74.GLS.Stage1.Main.BrIndex
public import CFSG.GH74.GLS.Stage1.Main.BrTwoClassA
public import CFSG.GH74.GLS.Stage1.Main.BrTwoClassI
public import CFSG.GH74.GLS.Stage1.Main.II4Proof
public import CFSG.GH74.GLS.Stage1.Thm2.Recip.L284
public import CFSG.GH74.GLS.Stage1.Thm3.Sec6.R1Glue2
public import CFSG.GH74.GLS.Stage1.Thm3.Sec6.R1Lem47c
public import CFSG.GH74.GLS.Stage1.Thm3.Sec7.LeafC1
public import CFSG.GH74.GLS.Stage1.Thm3.Sec8.Ctx64
public import CFSG.GH74.GLS.Stage1.Thm3.Sec8.GrpBasic25
public import CFSG.GH74.GLS.Stage1.Thm3.Sec8.Statements
public import CFSG.GH74.GLS.Stage2.Local.P27.FullFBuild
public import CFSG.GH74.GLS.Stage2.Local.P27.L4LayerA
public import CFSG.GH74.GLS.Stage2.Local.P34Main
public import CFSG.GH74.GLS.Stage2.Local.P34Perf
public import CFSG.GH74.GLS.Stage2.Local.P34S5SE
public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P4Merge
public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P4S55BrGH
public import CFSG.GH74.GLS.Stage2.Signalizer.L52One
public import CFSG.GH74.GLS.Stage2.Signalizer.L52TwoI1
public import CFSG.GH74.GLS.Stage2.Signalizer.Prop41
public import CFSG.GH74.GLS.Stage2.Signalizer.Prop43
public import CFSG.GH74.GLS.Stage2.Signalizer.Prop47
public import CFSG.GH74.GLS.TwoThin.KGroupCore
public import CFSG.GH74.Generic.S3.B2Tab1
public import CFSG.GH74.KGroups.L3EpsInvLin
public import CFSG.GH74.Uniqueness.SU.SU13TA1Class
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
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.InnerCoverBase
public import CFSG.Permutation.BurnsideSchur
public import CFSG.RankThree.PartOne.S10.PlaneContract
public import CFSG.RankThree.PartOne.S11c.Sec66TModels
public import CFSG.Sporadic.Th.Max3.Packet
public import CFSG.Sporadic.Th.Simple
public import CFSG.Sporadic.ThSchreier.AutCore

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Ivk8.BT

open Subgroup CFSG CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.ComponentClassification.OuterAutomorphisms CFSG.GH74.GLS.Stage2.Signalizer.Odd87
  CFSG.ComponentClassification.PSL3Four CFSG.GH74.GLS.Stage2.Signalizer.Odd87L34Out

namespace OutS

theorem classical_of_lieModel {Y : Type} [Group Y] {t : StatedLieTag} {n p f : ℕ} (hn : n ≠ 0)
    (h : LieModel Y t n p f) : StatedClassicalModel Y t n p f :=
  CFSG.Blueprint.LieModel.statedClassicalModel_of_ne_zero hn h

theorem cube_mem_S {n : Equiv.Perm (Fin 42)} (hn : n ∈ NN) : n ^ 3 ∈ S := by
  obtain ⟨s, hs, h, hh, rfl⟩ := mem_NN_iff.mp hn
  have hhN : h ∈ normalizer (S : Set (Equiv.Perm (Fin 42))) := zpowers_g₄_le_normalizer hh
  have hh3 : h ^ 3 = 1 := by
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hh
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, g₄_pow_three, one_zpow]
  have e : (s * h) ^ 3 = s * (h * s * h⁻¹) * ((h * h) * s * (h * h)⁻¹) * h ^ 3 := by
    simp only [pow_three]
    group
  rw [e, hh3, mul_one]
  refine S.mul_mem (S.mul_mem hs ?_) ?_
  · exact (mem_normalizer_iff.mp hhN s).mp hs
  · exact (mem_normalizer_iff.mp (mul_mem hhN hhN) s).mp hs

theorem outTwoNilp_S : OutTwoNilp ↥S := by
  obtain ⟨e, -, hinn⟩ := full_automorphism_action
  have hNNn : (NN.subgroupOf R).Normal := ⟨fun n hn g => by
    rw [mem_subgroupOf] at hn ⊢
    exact normalized_NN g.2 hn⟩
  refine ⟨(NN.subgroupOf R).map e.toMonoidHom, Subgroup.Normal.map hNNn _ e.surjective, ?_, ?_, ?_⟩
  · rw [← hinn]
    refine Subgroup.map_mono fun x hx => ?_
    rw [mem_subgroupOf] at hx ⊢
    exact le_sup_left (a := S) hx
  · rintro _ ⟨n, hn, rfl⟩
    refine ⟨3, by decide, ?_⟩
    rw [← hinn, ← map_pow]
    refine Subgroup.mem_map_of_mem _ ?_
    rw [SetLike.mem_coe, mem_subgroupOf] at hn
    rw [mem_subgroupOf, SubgroupClass.coe_pow]
    exact cube_mem_S hn
  · intro y
    obtain ⟨r, rfl⟩ := e.surjective y
    refine ⟨1, ?_⟩
    rw [pow_one, ← map_pow]
    refine Subgroup.mem_map_of_mem _ ?_
    rw [mem_subgroupOf, SubgroupClass.coe_pow, pow_two]
    exact sq_mem_NN r.2

end OutS

open OutS

theorem outCell_two : OutCell FTwo := by
  intro Y _ _ _ hY
  rcases hY with h | h | h | h | h
  · have hd := (LocalAnalysis.ComponentInitial.linear_model_outer_two_part_bound Y 2 2 3
      (classical_of_lieModel (by norm_num) h)).2.2.2.1 rfl
    exact outTwoNilp_of_odd_card_outer (Odd.of_dvd_nat (by decide) hd)
  · have hd := (LocalAnalysis.ComponentInitial.linear_model_outer_two_part_bound Y 2 2 4
      (classical_of_lieModel (by norm_num) h)).2.2.2.1 rfl
    exact outTwoNilp_of_card_outer_dvd (k := 2) (hd.trans (by decide))
  · obtain ⟨e⟩ := CFSG.ComponentClassification.CatFactsSmall.nonempty_equiv_psl34_of_lieModel h
    exact OutTwoNilp.of_mulEquiv e outTwoNilp_S
  · have h4 := (LocalAnalysis.ComponentInitial.unitary_model_outer_two_part_bound Y 3 2 2
      (classical_of_lieModel (by norm_num) h)).2.2.1
    exact outTwoNilp_of_card_outer_dvd (k := 2) (by rw [h4]; decide)
  · obtain ⟨-, -, a, ha, K, _, _, hfa, hK, ⟨e⟩⟩ :=
      RankThree.PartOne.Sec66T.lieModel_twistedB2_iff.mp h
    have hK' : Nat.card K = 2 ^ (2 * a + 1) := by rw [← hfa]; exact hK
    have hodd := (RankThree.Automorphisms.Suzuki_full_field_automorphism_splitting a ha K
      hK').2.2.2.2.2.2
    exact outTwoNilp_of_odd_card_outer (by rw [Nat.card_congr (equivalence e).toEquiv]; exact hodd)

end CFSG.GH74.GLS.Stage2.Signalizer.Ivk8.BT

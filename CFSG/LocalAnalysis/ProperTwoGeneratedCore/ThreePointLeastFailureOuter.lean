module

public import CFSG.LocalAnalysis.ComponentInitial.PerfectCentralQuotientOuter
public import CFSG.LocalAnalysis.ComponentInitial.SuzukiModelSchreier
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherRankOneSchreier
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueSchreierLinearTwoAllFields
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.RankOneModelTransport
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.SuzukiCentralCover
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionClassFreeAffineHullAutomorphisms
public import CFSG.LieType.BorelTits.Suzuki
public import CFSG.StronglyEmbedded.MatrixGroups.PSU3Model
public import Certificates.Certificate113
import CFSG.Models.BenderSuzuki
public import CFSG.CharacterTheory.Semidihedral.DihedralQuaternion
public import CFSG.LieType.BorelTits.CompleteFlag
public import CFSG.LieType.Ree.SuzukiSimple
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Defs

public noncomputable section

namespace CFSG.ProperTwoGeneratedCore.RankOnePair

open CFSG.Open CFSG.BenderSuzuki CFSG.BenderSuzuki.MatrixGroups CFSG.BenderSuzuki.PFAppendixIII
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)
open CFSG.ProperTwoGeneratedCore.LocalCriterionClassFreeAffineHull

universe u

theorem linear_model_outer_solvable (f : ℕ) :
    Group.IsSolvable (Outer (PSL2BinaryMatrixGroup f)) :=
  CFSG.ComponentClassification.CatalogueSchreierLinearTwo.outer_solvable (BinaryGaloisField f)

theorem suzukiMatrixGroup_suzukiModel (m : ℕ) (hm : 1 ≤ m) :
    CFSG.Blueprint.SuzukiModel (SuzukiMatrixGroup m) 2 (2 * m + 1) := by
  have hcard : Nat.card (BinaryGaloisField (2 * m + 1)) = 2 ^ (2 * m + 1) :=
    GaloisField.card 2 _ (by omega)
  refine ⟨rfl, m, hm, BinaryGaloisField (2 * m + 1), inferInstance, inferInstance, rfl, hcard,
    ⟨?_⟩⟩
  exact ((MulEquiv.subgroupCongr
    (CFSG.LieType.BorelTits.suzukiGroup_eq_glaSzGroup m (BinaryGaloisField (2 * m + 1)))).trans
    ((CFSG.ShultStronglyClosedTI.glaSzEquivNative m hm hcard).trans
      (CFSG.ShultStronglyClosedTI.suzukiCoverNativeEquiv m))).symm

theorem suzuki_model_outer_solvable (m : ℕ) (hm : 1 ≤ m) :
    Group.IsSolvable (Outer (SuzukiMatrixGroup m)) :=
  (CFSG.LocalAnalysis.ComponentInitial.Suzuki_model_Schreier _ 2 (2 * m + 1)
    (suzukiMatrixGroup_suzukiModel m hm)).2

theorem unitary_model_statedClassicalModel {k : Type} [Field k] [Finite k]
    (J : HermitianForm 3 k) (f : ℕ) (hf : 2 ≤ f)
    (hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0]) (hcard : Nat.card k = (2 ^ f) ^ 2)
    (hfixed : Nat.card {x : k // J.conj x = x} = 2 ^ f) :
    CFSG.Assembly.LowTwoRank.StatedClassicalModel (ProjectiveSpecialUnitaryMatrixGroup J)
      .PSU 3 2 f := by
  obtain ⟨e⟩ := projectiveSpecialUnitary_equiv_PSU3Model J f hf hJ hcard hfixed
  have hmodel : PSU3Model f = PSU3 2 f := CFSG.Models.benderPSU3Model_eq_psu3 f
  have hq : 2 < 2 ^ f := lt_of_lt_of_le (by norm_num) (Nat.pow_le_pow_right (by norm_num) hf)
  refine ⟨⟨Nat.prime_two, by omega, le_rfl, fun heq => hq.ne' (congrArg Prod.snd heq)⟩,
    GaloisField 2 (2 * f), inferInstance, inferInstance, ?_, ⟨?_⟩⟩
  · rw [GaloisField.card 2 (2 * f) (by omega), ← pow_mul, mul_comm]
  · exact (e.trans (MulEquiv.subgroupCongr hmodel)).trans
      (CFSG.ShultStronglyClosedTI.glaSUCanonicalEquivNative f).symm

theorem unitary_model_outer_solvable {k : Type} [Field k] [Finite k]
    (J : HermitianForm 3 k) (f : ℕ) (hf : 2 ≤ f)
    (hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0]) (hcard : Nat.card k = (2 ^ f) ^ 2)
    (hfixed : Nat.card {x : k // J.conj x = x} = 2 ^ f) :
    Group.IsSolvable (Outer (ProjectiveSpecialUnitaryMatrixGroup J)) :=
  (CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher.unitary_rank_one_classical_model_schreier
    (unitary_model_statedClassicalModel J f hf hJ hcard hfixed)).2

theorem center_eq_bot_of_simple_perfect (Q : Type u) [Group Q] [IsSimpleGroup Q]
    [Group.IsPerfect Q] : Subgroup.center Q = ⊥ := by
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center Q) with h | h
  · exact h
  · exfalso
    have : IsMulCommutative Q := ⟨⟨fun a b => by
      have hb : b ∈ Subgroup.center Q := h ▸ Subgroup.mem_top b
      exact (Subgroup.mem_center_iff.mp hb a)⟩⟩
    exact Group.IsPerfect.not_isMulCommutative Q this

theorem center_eq_oddCore_of_simple_quotient {L : Type u} [Group L] [Group.IsPerfect L]
    (hcore : CFSG.oddCore L ≤ Subgroup.center L)
    (hsimple : IsSimpleGroup (L ⧸ CFSG.oddCore L)) :
    Subgroup.center L = CFSG.oddCore L := by
  refine le_antisymm (fun x hx => ?_) hcore
  have hQ := center_eq_bot_of_simple_perfect (L ⧸ CFSG.oddCore L)
  have hxQ : (QuotientGroup.mk x : L ⧸ CFSG.oddCore L) ∈ Subgroup.center (L ⧸ CFSG.oddCore L) := by
    refine Subgroup.mem_center_iff.mpr fun q => ?_
    obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective q
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, Subgroup.mem_center_iff.mp hx y]
  rw [hQ, Subgroup.mem_bot] at hxQ
  exact (QuotientGroup.eq_one_iff x).mp hxQ

theorem outer_solvable_of_simple_oddCore_quotient {L : Type u} [Group L] [Group.IsPerfect L]
    (hcore : CFSG.oddCore L ≤ Subgroup.center L)
    (hsimple : IsSimpleGroup (L ⧸ CFSG.oddCore L))
    (hout : Group.IsSolvable (Outer (L ⧸ CFSG.oddCore L))) :
    Group.IsSolvable (outerAutomorphismGroup L) := by
  have hcenter := center_eq_oddCore_of_simple_quotient hcore hsimple
  exact (CFSG.LocalAnalysis.ComponentInitial.perfect_central_quotient_Schreier L).2.2
    ((CFSG.LocalAnalysis.ComponentInitial.outer_isomorphism
      (QuotientGroup.quotientMulEquivOfEq hcenter.symm)).2.mp hout)

end CFSG.ProperTwoGeneratedCore.RankOnePair

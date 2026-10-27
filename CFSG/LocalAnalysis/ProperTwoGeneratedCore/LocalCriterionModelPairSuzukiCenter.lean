module

public import CFSG.LocalAnalysis.ShultStronglyClosedTI.SuzukiCoverRootData
public import CFSG.StronglyEmbedded.TheoremSE.BenderLowRank
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.IV.ComplementTransfer
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter1section3.Basic
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter2.Basic
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.InvolutionCore
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.RankOne
public import Mathlib.Algebra.GroupWithZero.TransferInstance

public noncomputable section

namespace CFSG.ProperTwoGeneratedCore.LocalCriterionModelPair

open CFSG.ShultStronglyClosedTI CFSG.BenderSuzuki
open CFSG.BenderSuzuki.MatrixGroups CFSG.BenderSuzuki.PFAppendixIII

universe u

theorem sylow_involutions_central_of_one
    {G : Type u} [Group G] [Finite G] (Q : Sylow 2 G)
    (hQ : ∀ x : (Q : Subgroup G), IsInvolution x →
      x ∈ Subgroup.center (Q : Subgroup G)) :
    ∀ S : Sylow 2 G, ∀ x : (S : Subgroup G), IsInvolution x →
      x ∈ Subgroup.center (S : Subgroup G) := by
  intro S x hx
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G Q S
  have hmap : (Q : Subgroup G).map (MulAut.conj g).toMonoidHom = S := by
    change (g • Q : Sylow 2 G).toSubgroup = S.toSubgroup
    rw [hg]
  let e : (Q : Subgroup G) ≃* (S : Subgroup G) :=
    ((MulAut.conj g).subgroupMap (Q : Subgroup G)).trans (MulEquiv.subgroupCongr hmap)
  have hpreI : IsInvolution (e.symm x) :=
    IsInvolution.map_of_injective hx e.symm.toMonoidHom e.symm.injective
  have hpre := hQ (e.symm x) hpreI
  rw [← Subgroup.map_center_eq e]
  have hmem := Subgroup.mem_map_of_mem e.toMonoidHom hpre
  change e (e.symm x) ∈ _ at hmem
  simpa only [MulEquiv.toMonoidHom_eq_coe, e.apply_symm_apply] using hmem

theorem suzuki_root_involution_mem_center
    (m : ℕ) (hm : 1 ≤ m) (x : suzukiCoverRoot m) (hx : IsInvolution x) :
    x ∈ Subgroup.center (suzukiCoverRoot m) := by
  obtain ⟨a, b, rfl⟩ := suzukiCoverRootElement_surjective m x
  have hsq : suzukiCoverRootElement m 0 (a * suzukiCoverTits m a) = 1 := by
    have h := hx.sq_eq_one
    rw [pow_two, suzukiCoverRootElement_mul m (by omega)] at h
    simpa only [CharTwo.add_self_eq_zero, zero_add] using h
  have hcoord : a * suzukiCoverTits m a = 0 := by
    have h := suzukiCoverRootElement_injective m 0 (a * suzukiCoverTits m a) 0 0
      (hsq.trans (suzukiCoverRootElement_zero_zero m).symm)
    exact h.2
  have ha : a = 0 := by
    rcases mul_eq_zero.mp hcoord with ha | ha
    · exact ha
    · exact (suzukiCoverTits m).injective (by simpa only [map_zero] using ha)
  rw [← (suzukiCoverRoot_structure m (by omega)).2.2.1]
  exact ((suzukiCoverRoot_structure m (by omega)).2.2.2 _).mpr
    ⟨b, by rw [ha]⟩

theorem suzuki_sylow_involutions_mem_center (m : ℕ) (hm : 1 ≤ m) :
    ∀ S : Sylow 2 (SuzukiMatrixGroup m), ∀ x : (S : Subgroup (SuzukiMatrixGroup m)),
      IsInvolution x → x ∈ Subgroup.center (S : Subgroup (SuzukiMatrixGroup m)) := by
  apply sylow_involutions_central_of_one (suzukiCoverSylow m (by omega))
  exact suzuki_root_involution_mem_center m hm

end CFSG.ProperTwoGeneratedCore.LocalCriterionModelPair

module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionProperHullCommutator
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionProperHullConfinement

public noncomputable section

namespace CFSG.ProperTwoGeneratedCore.LocalCriterionProperHull

open CFSG.Open CFSG.ShultStronglyClosedTI
open CFSG.ProperTwoGeneratedCore
open CFSG.ProperTwoGeneratedCore.LocalCriterionGeometry
open CFSG.BenderSuzuki.PFAppendixIII CFSG.BenderSuzuki.PFchapter1section1
open CFSG.RankThreeCoreUniqueness.Helpers

universe u

variable {G : Type u} [Group G]

theorem properHull_commutator_normalized_by_centralizer (P : Subgroup G) (z : G) :
    Subgroup.normalizer (P : Set G) ⊓ Subgroup.centralizer ({z} : Set G) ≤
      Subgroup.normalizer ((⁅P, Subgroup.zpowers z⁆ : Subgroup G) : Set G) := by
  intro w hw
  have hconjz : (MulAut.conj w) z = z := by
    change w * z * w⁻¹ = z
    exact mul_inv_eq_iff_eq_mul.mpr
      (Subgroup.mem_centralizer_singleton_iff.mp hw.2)
  apply Subgroup.mem_normalizer_iff_map_conj_eq.mpr
  rw [Subgroup.map_commutator,
    Subgroup.mem_normalizer_iff_map_conj_eq.mp hw.1, MonoidHom.map_zpowers]
  change ⁅P, Subgroup.zpowers ((MulAut.conj w) z)⁆ = ⁅P, Subgroup.zpowers z⁆
  rw [hconjz]

theorem properHull_self_commutator_right_conjugate
    (X : Subgroup G) (z y : G)
    (hy : y ∈ Subgroup.normalizer (X : Set G))
    (hself : ⁅X, Subgroup.zpowers z⁆ = X) :
    ⁅X, Subgroup.zpowers (rightConjugateElem z y)⁆ = X := by
  have hmap := congrArg (fun A : Subgroup G => A.map (MulAut.conj y⁻¹).toMonoidHom) hself
  have hXmap := Subgroup.mem_normalizer_iff_map_conj_eq.mp
    ((Subgroup.normalizer (X : Set G)).inv_mem hy)
  change X.map (MulAut.conj y⁻¹).toMonoidHom = X at hXmap
  rw [Subgroup.map_commutator, hXmap, MonoidHom.map_zpowers] at hmap
  change ⁅X, Subgroup.zpowers (y⁻¹ * z * (y⁻¹)⁻¹)⁆ = X at hmap
  simpa only [inv_inv, rightConjugateElem] using hmap

theorem properHull_self_commutator_noncentral
    (X : Subgroup G) (z : G) (hXne : X ≠ ⊥)
    (hself : ⁅X, Subgroup.zpowers z⁆ = X) :
    ¬ X ≤ Subgroup.centralizer ({z} : Set G) := by
  intro hcentral
  have hzCX : z ∈ Subgroup.centralizer (X : Set G) := by
    apply Subgroup.mem_centralizer_iff.mpr
    intro x hx
    exact Subgroup.mem_centralizer_singleton_iff.mp (hcentral hx)
  have hCX : Subgroup.zpowers z ≤ Subgroup.centralizer (X : Set G) :=
    Subgroup.zpowers_le.mpr hzCX
  have hbot : ⁅X, Subgroup.zpowers z⁆ = ⊥ :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.mpr (Subgroup.le_centralizer_iff.mpr hCX)
  exact hXne (hself.symm.trans hbot)

theorem properHull_commutator_normalizer_hull_rank [Finite G]
    {H : Subgroup G} {z : G} (h : MinimalInvolutionPointLocalFailure H z)
    (P : Subgroup G) (hzP : z ∈ Subgroup.normalizer (P : Set G))
    (hMproper : Subgroup.normalizer (P : Set G) < ⊤)
    (hMescape : ¬ Subgroup.normalizer (P : Set G) ≤ H)
    (hMrank : 2 ≤ CFSG.Open.pRank 2
      (properHull (Subgroup.normalizer (P : Set G)) z))
    (hXescape : ¬ Subgroup.normalizer
      ((⁅P, Subgroup.zpowers z⁆ : Subgroup G) : Set G) ≤ H) :
    2 ≤ CFSG.Open.pRank 2 (properHull
      (Subgroup.normalizer ((⁅P, Subgroup.zpowers z⁆ : Subgroup G) : Set G)) z) := by
  let M := Subgroup.normalizer (P : Set G)
  let X := ⁅P, Subgroup.zpowers z⁆
  let Y := Subgroup.normalizer (X : Set G)
  have hMtwo : 2 ≤ twoRank (properHull M z) := by
    rw [twoRank, ← pRank_subgroup_eq_internal_top 2 (by decide)]
    exact hMrank
  obtain ⟨w, hwL, _hworder, hwclass, hcomm, hne⟩ :=
    properHull_rank_two_commuting_class h hMproper hzP hMescape hMtwo
  have hwY : w ∈ Y := properHull_commutator_normalized_by_centralizer P z
    ⟨properHull_le M hzP hwL, Subgroup.mem_centralizer_singleton_iff.mpr hcomm.eq.symm⟩
  have hzY : z ∈ Y := (properHull_commutator_normalized P (Subgroup.zpowers z))
    ((le_sup_right : Subgroup.zpowers z ≤ P ⊔ Subgroup.zpowers z) (Subgroup.mem_zpowers z))
  have hYrank := local_involution_hull_two_rank_of_commuting_class h.local_datum
    Y hzY hXescape hwY hwclass hcomm hne
  rw [← properHull_rank_eq_internal Y hzY] at hYrank
  rw [twoRank, ← pRank_subgroup_eq_internal_top 2 (by decide)] at hYrank
  exact hYrank

end CFSG.ProperTwoGeneratedCore.LocalCriterionProperHull

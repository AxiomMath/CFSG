module

public import CFSG.ClassicalInvolution.Balance.Layer
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.GH74.GLS.IVK.Proofs2.Ivk93Lift

public section

namespace CFSG.GH74.GLS.Stage2.Final.Thm6.L2011.Ad

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.Stage2.Local
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem le_pLayerOf_of_comp {H : Subgroup G} {x : G} (hxH : x ∈ H) (hx2 : orderOf x = 2)
    {K : Subgroup G} (hKH : K ≤ H) (hKC : K ≤ centralizer ({x} : Set G)) (hperf : ⁅K, K⁆ = K)
    (hq : IsQuasisimple (↥K ⧸ pPrimeCore 2 ↥K))
    (hsub : (K.subgroupOf (centralizer ({x} : Set G))).IsSubnormal) : K ≤ pLayerOf 2 H := by
  set x' : ↥H := ⟨x, hxH⟩ with hx'
  have hx2' : orderOf x' = 2 := by rw [Subgroup.orderOf_mk]; exact hx2
  have hA : IsPGroup 2 (zpowers x') :=
    IsPGroup.of_card (n := 1) (by simpa only [Nat.card_zpowers, pow_one] using hx2')
  have hcentA : centralizer ((zpowers x' : Subgroup ↥H) : Set ↥H) =
      (centralizer ({x} : Set G)).subgroupOf H := by
    rw [Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure,
      IVK.Proofs2.Ivk93Adapt.centralizer_singleton_subgroupOf hxH]
  have hLA : K.subgroupOf H ≤ centralizer ((zpowers x' : Subgroup ↥H) : Set ↥H) := by
    rw [hcentA]
    intro y hy
    exact hKC (Subgroup.mem_subgroupOf.mp hy)
  have hLsub : CFSG.Open.IsSubnormal (K.subgroupOf H)
      (centralizer ((zpowers x' : Subgroup ↥H) : Set ↥H)) := by
    have h1 : CFSG.Open.IsSubnormal (K.subgroupOf (centralizer ({x} : Set G))) ⊤ :=
      CFSG.ComponentClassification.Components.chain_of_mathlib_subnormal hsub
    have h2 : CFSG.Open.IsSubnormal K (centralizer ({x} : Set G)) :=
      (CFSG.ComponentClassification.LBalance.subnormal_subgroupOf_iff hKC).mp h1
    have h3 := CFSG.ComponentClassification.LBalance.subnormal_subgroupOf h2 H
    rwa [← hcentA] at h3
  have hKperf' : Group.IsPerfect ↥K := Subgroup.isPerfect_iff.mpr hperf
  let e : ↥(K.subgroupOf H) ≃* ↥K := Subgroup.subgroupOfEquivOfLe hKH
  have hLperf' : Group.IsPerfect ↥(K.subgroupOf H) :=
    Group.IsPerfect.ofSurjective (f := e.symm.toMonoidHom) e.symm.surjective
  have hLperf : commutator ↥(K.subgroupOf H) = ⊤ := Group.IsPerfect.commutator_eq_top
  have hq1 : CFSG.IsQuasisimple (↥(K.subgroupOf H) ⧸ pPrimeCore 2 ↥(K.subgroupOf H)) :=
    CFSG.LocalCores.isQuasisimple_of_mulEquiv
      (CFSG.ComponentClassification.UnbalancingLocal.Correspondence.quotientPPrimeCoreCongr 2 e).symm
      hq
  have hq2 : CFSG.Open.IsQuasisimple
      (↥(K.subgroupOf H) ⧸ CFSG.Open.componentClassificationOddCore ↥(K.subgroupOf H)) := by
    have h := CFSG.ComponentClassification.CatalogueBAlternating.quasisimple_iff_native.mp hq1
    have key : ∀ (R : Subgroup ↥(K.subgroupOf H)) [R.Normal],
        R = CFSG.Open.componentClassificationOddCore ↥(K.subgroupOf H) →
        CFSG.Open.IsQuasisimple (↥(K.subgroupOf H) ⧸ R) →
        CFSG.Open.IsQuasisimple
          (↥(K.subgroupOf H) ⧸ CFSG.Open.componentClassificationOddCore ↥(K.subgroupOf H)) := by
      intro R _ hR
      subst hR
      exact id
    exact key _ (CFSG.ComponentClassification.CatalogueBAlternating.primeCore_two_eq_oddCore _) h
  have h1 : K.subgroupOf H ≤ CFSG.ComponentClassification.TwoLayer.subgroup ↥H :=
    CFSG.ClassicalInvolution.Balance.le_twoLayer_of_l2PrimeBalance
      CFSG.ClassicalInvolution.l2PrimeBalance hA hLA hLsub hLperf hq2
  rw [TwoThin.pLayerOf_two_eq_map]
  intro g hg
  exact ⟨⟨g, hKH hg⟩, h1 (Subgroup.mem_subgroupOf.mpr hg), rfl⟩

end CFSG.GH74.GLS.Stage2.Final.Thm6.L2011.Ad

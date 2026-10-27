module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDiscPf11Act

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinMu

namespace Pf3

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Asc77.Thompson
  CFSG.ClassicalInvolution.Disconnected.AschTight CFSG.ClassicalInvolution.Q3
  CFSG.ClassicalInvolution.Asc77.Star3T CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDisc
open CFSG.ClassicalInvolution.Q3.Q3NL

section Odd


variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {c : G}

theorem centralizes_of_mem_oddCoreOf (hΩ : HypOmegaGen Ω) (hc2 : IsPGroup 2 (Subgroup.zpowers c))
    {W : Subgroup G} (hW2 : IsPGroup 2 W) (hWc : W ≤ Subgroup.centralizer ({c} : Set G)) {g : G}
    (hgN : g ∈ Subgroup.normalizer (W : Set G)) (hg : g ∈ oddCoreOf (coreLayer Ω c)) :
    ∀ w ∈ W, g * w = w * g := by
  intro w hw
  have hY : conjSub w (coreLayer Ω c) = coreLayer Ω c := conjSub_coreLayer hΩ hc2 (hWc hw)
  have h1 : w * g * w⁻¹ ∈ oddCoreOf (coreLayer Ω c) := by
    have h := conj_mem_conjSub (n := w) hg
    rwa [← S1916.oddCoreOf_conjSub, hY] at h
  have h2 : w * g * w⁻¹ * g⁻¹ ∈ oddCoreOf (coreLayer Ω c) :=
    Subgroup.mul_mem _ h1 (Subgroup.inv_mem _ hg)
  have h3 : g * w⁻¹ * g⁻¹ ∈ W := (Subgroup.mem_normalizer_iff.mp hgN w⁻¹).mp (W.inv_mem hw)
  have h4 : w * g * w⁻¹ * g⁻¹ ∈ W := by
    have : w * g * w⁻¹ * g⁻¹ = w * (g * w⁻¹ * g⁻¹) := by group
    rw [this]
    exact W.mul_mem hw h3
  have h5 : w * g * w⁻¹ * g⁻¹ = 1 :=
    eq_one_of_isPGroup_of_mem_odd (oddCoreOf_odd_natCard (coreLayer Ω c)) h2
      (hW2.to_le (Subgroup.zpowers_le.mpr h4))
  have h6 : w * g = g * w := by
    have := mul_inv_eq_one.mp (show w * g * w⁻¹ * g⁻¹ = 1 from h5)
    calc w * g = (w * g * w⁻¹) * w := by group
      _ = g * w := by rw [this]
  exact h6.symm

theorem comm_mem_oddCoreOf_of_commutes {J J' : Subgroup G} (hJ : J ∈ tqMembers3 Ω c)
    (hJ' : J' ∈ tqMembers3 Ω c) {r t : G} (hr : r ∈ TwinADescent.coreAt c J)
    (ht : t ∈ TwinADescent.coreAt c J') (hcomm : Commutes (secImg Ω c J) (secImg Ω c J')) :
    r * t * r⁻¹ * t⁻¹ ∈ oddCoreOf (coreLayer Ω c) := by
  set C := Subgroup.centralizer ({c} : Set G) with hC
  have hrC : r ∈ C := TwinADescent.coreAt_le_centralizer c J hr
  have htC : t ∈ C := TwinADescent.coreAt_le_centralizer c J' ht
  have hrH : (⟨r, hrC⟩ : ↥C) ∈ coreHull Ω c := le_coreHull hJ (Subgroup.mem_subgroupOf.mpr hr)
  have htH : (⟨t, htC⟩ : ↥C) ∈ coreHull Ω c := le_coreHull hJ' (Subgroup.mem_subgroupOf.mpr ht)
  set rh : ↥(coreHull Ω c) := ⟨⟨r, hrC⟩, hrH⟩ with hrh
  set th : ↥(coreHull Ω c) := ⟨⟨t, htC⟩, htH⟩ with hth
  have h1 : QuotientGroup.mk rh ∈ secImg Ω c J :=
    Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.mpr (Subgroup.mem_subgroupOf.mpr hr))
  have h2 : QuotientGroup.mk th ∈ secImg Ω c J' :=
    Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.mpr (Subgroup.mem_subgroupOf.mpr ht))
  have h3 := hcomm _ h1 _ h2
  have h4 : QuotientGroup.mk (rh * th * rh⁻¹ * th⁻¹) =
      (1 : ↥(coreHull Ω c) ⧸ classicalInvolutionOddCore ↥(coreHull Ω c)) := by
    rw [QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv,
      QuotientGroup.mk_inv, h3]
    group
  have h5 : rh * th * rh⁻¹ * th⁻¹ ∈ classicalInvolutionOddCore ↥(coreHull Ω c) :=
    (QuotientGroup.eq_one_iff _).mp h4
  exact coe_mem_oddCoreOf_coreLayer h5

end Odd

end Pf3

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinMu

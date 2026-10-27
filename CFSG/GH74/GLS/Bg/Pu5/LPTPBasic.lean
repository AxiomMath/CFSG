module

public import CFSG.GH74.GLS.Bg.Iii2.Basic
public import CFSG.GH74.GLS.Bg.Iii2.CMAux
public import CFSG.GH74.GLS.Bg.Iii2.CMPU

public section

namespace CFSG.GH74.GLS.Bg.Pu5

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Assembly.LowTwoRank CFSG.GH74.GLS.Stage1.Thm2.Recip
  CFSG.GH74.GLS.C3.Layer1.PumpRigid CFSG.GH74.GLS.C3.Layer1.PumpCalc CFSG.GH74.GLS.TwoThin
  CFSG.LocalAnalysis.ComponentInitial CFSG.ComponentClassification CFSG.GH74.GLS.Stage1.Thm3.Sec4
  CFSG.GH74.GLS.Bg.Iii2 CFSG.GH74.GLS.Bg.Iii2.CMEngine
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem le_rigidProduct {b : G} {J : Subgroup G} (hJ : IsRigidRankOneComp b J) : J ≤ rigidProduct b :=
  le_sSup hJ

omit [Finite G] in
theorem rigidProduct_le_centralizer (b : G) : rigidProduct b ≤ centralizer ({b} : Set G) :=
  sSup_le fun _ hJ => (rr_pcomp hJ).1

omit [Finite G] in
theorem bar_mono {u : G} {X X' : Subgroup G} (h : X ≤ X') : bar u X ≤ bar u X' :=
  Subgroup.map_mono fun _ hx => h hx

omit [Finite G] in
theorem rigidProduct_subgroupOf (b : G) :
    (rigidProduct b).subgroupOf (centralizer ({b} : Set G)) =
      sSup ((fun J : Subgroup G => J.subgroupOf (centralizer ({b} : Set G))) ''
        {J | IsRigidRankOneComp b J}) := by
  set Y := centralizer ({b} : Set G) with hY
  set 𝒮 := (fun J : Subgroup G => J.subgroupOf Y) '' {J | IsRigidRankOneComp b J} with h𝒮
  apply le_antisymm
  · have h1 : rigidProduct b ≤ (sSup 𝒮).map Y.subtype := by
      refine sSup_le fun J hJ => ?_
      have hJY : J ≤ Y := (rr_pcomp hJ).1
      have : J = (J.subgroupOf Y).map Y.subtype := (Subgroup.map_subgroupOf_eq_of_le hJY).symm
      rw [this]
      exact Subgroup.map_mono (le_sSup ⟨J, hJ, rfl⟩)
    calc (rigidProduct b).subgroupOf Y ≤ ((sSup 𝒮).map Y.subtype).subgroupOf Y := fun x hx => h1 hx
      _ = sSup 𝒮 := Subgroup.comap_map_eq_self_of_injective Y.subtype_injective _
  · refine sSup_le ?_
    rintro _ ⟨J, hJ, rfl⟩
    exact fun x hx => le_rigidProduct hJ hx

theorem rigidProduct_isSubnormal (b : G) :
    ((rigidProduct b).subgroupOf (centralizer ({b} : Set G))).IsSubnormal := by
  rw [rigidProduct_subgroupOf]
  set 𝒮 := (fun J : Subgroup G => J.subgroupOf (centralizer ({b} : Set G))) ''
    {J | IsRigidRankOneComp b J} with h𝒮
  have hcl : sSup 𝒮 = Subgroup.closure (⋃ A ∈ 𝒮, (A : Set ↥(centralizer ({b} : Set G)))) := by
    rw [Set.biUnion_eq_iUnion, ← Subgroup.iSup_eq_closure, sSup_eq_iSup']
  rw [hcl]
  refine (CFSG.GroupTheory.subnormal_subgroups_generated_join 𝒮 ?_).1
  rintro _ ⟨J, hJ, rfl⟩
  obtain ⟨_, _, hsub, _⟩ := (rr_pcomp hJ).2
  exact hsub

theorem barMk_eq_one_of_mem_pPrimeCoreOf {Y' K' : Subgroup G} (hK'Y : K' ≤ Y')
    (hsub : (K'.subgroupOf Y').IsSubnormal) {k : G} (hk : k ∈ pPrimeCoreOf 2 K') (hkY : k ∈ Y') :
    barMk ↥Y' ⟨k, hkY⟩ = 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [pPrimeCoreOf_eq_map_subgroupOf hK'Y] at hk
  obtain ⟨z, hz, hzk⟩ := hk
  have h1 : z ∈ pPrimeCore 2 ↥Y' := pPrimeCoreOf_le_of_subnormal 2 hsub hz
  have h2 : z = ⟨k, hkY⟩ := Subtype.ext hzk
  rw [← h2]
  exact (QuotientGroup.eq_one_iff _).mpr h1

theorem exists_pump (hG : IsKProperSimple G) (h3 : 3 ≤ pRank 2 G) {a b : G} {K : Subgroup G}
    (hK : IsRigidRankOneComp a K) (hb : orderOf b = 2) (hab : b ∈ centralizer ({a} : Set G))
    (hbK : b ∈ cSec K) :
    ∃ (J Λ : Subgroup G) (hxY : a ∈ centralizer ({b} : Set G)),
      IsRigidRankOneComp b J ∧ StepData a b hxY K J Λ := by
  have hrk3 : ∀ y : G, orderOf y = 2 → 3 ≤ pRank 2 ↥(centralizer ({y} : Set G)) := fun y hy =>
    TwoThin.rankThreeCentralizers G hG.1 hG.2.1 h3 y hy
  obtain ⟨J, hJ⟩ := exists_pumpUpLT hK.1.1 hb (Subgroup.mem_inf.mpr ⟨hab, hbK⟩) (hrk3 b hb)
  have hxY : a ∈ centralizer ({b} : Set G) := mem_centralizer_symm hab
  obtain ⟨Λ, hΛ⟩ := exists_stepData hK hJ hxY
  exact ⟨J, Λ, hxY, isRigidRankOneComp_of_pumpUpLT hK hJ, hΛ⟩

theorem bar_lam_le_rigidProduct {a b : G} {K J Λ : Subgroup G} (hxY : a ∈ centralizer ({b} : Set G))
    (hK : IsRigidRankOneComp a K) (hJ : IsRigidRankOneComp b J) (hΛ : StepData a b hxY K J Λ) :
    bar b Λ ≤ bar b (rigidProduct b) := by
  rcases hΛ.cases with ⟨-, hv⟩ | ⟨-, hAB, hD⟩
  · rw [hv]
    exact bar_mono (le_rigidProduct hJ)
  · rw [hD]
    have hs2 : orderOf (sbar a hxY) = 2 := orderOf_sbar (rr_ord hK) hxY
    have hsinv : (sbar a hxY)⁻¹ = sbar a hxY := inv_eq_self_of_orderOf_eq_two hs2
    have hJ' : IsRigidRankOneComp b (cmap a J) := isRigidRankOneComp_cmap hJ hxY
    have hbarJ' : bar b (cmap a J) = conjSub (sbar a hxY)⁻¹ (bar b J) := by
      rw [bar_cmap hxY, hsinv]
    rintro _ ⟨x, rfl⟩
    have h1 := swapDiag_mem_sup hAB x
    refine (sup_le (bar_mono (le_rigidProduct hJ)) ?_) h1
    rw [← hbarJ']
    exact bar_mono (le_rigidProduct hJ')

end CFSG.GH74.GLS.Bg.Pu5

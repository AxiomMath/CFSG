module

public import CFSG.Open.Defs
import CFSG.LocalAnalysis.ComponentClassification.LocalComponents

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.LieComp

open CFSG.Open

private theorem nontrivial_of_isQuasisimple {K : Type*} [Group K] (h : IsQuasisimple K) :
    Nontrivial K := by
  haveI : IsSimpleGroup (K ⧸ Subgroup.center K) := h.2
  exact (QuotientGroup.mk_surjective (s := Subgroup.center K)).nontrivial

private theorem false_of_isQuasisimple_of_isSolvable {K : Type*} [Group K]
    (h : IsQuasisimple K) (hs : Group.IsSolvable K) : False := by
  haveI := nontrivial_of_isQuasisimple h
  haveI : Group.IsPerfect K := ⟨h.1⟩
  exact Group.IsPerfect.not_isSolvable K hs

private theorem mul_comm_of_components_ne {G : Type*} [Group G] [Finite G] {C K L : Subgroup G}
    (hK : IsComponentOf K C) (hL : IsComponentOf L C) (hne : K ≠ L) {a b : G} (ha : a ∈ K)
    (hb : b ∈ L) : a * b = b * a := by
  have hcomp : ∀ {X : Subgroup G}, IsComponentOf X C → IsComponentOf (X.subgroupOf C) ⊤ := by
    intro X hX
    refine ⟨le_top, ?_, CFSG.Open.IsQuasisimple.of_mulEquiv
      (Subgroup.subgroupOfEquivOfLe hX.1) hX.2.2⟩
    have h1 := hX.2.1.comap C.subtype
    rwa [show C.comap C.subtype = ⊤ from Subgroup.subgroupOf_self C] at h1
  have hne' : K.subgroupOf C ≠ L.subgroupOf C := by
    intro h
    apply hne
    have h' := Subgroup.subgroupOf_inj.mp h
    rwa [inf_eq_left.mpr hK.1, inf_eq_left.mpr hL.1] at h'
  have h := CFSG.ComponentClassification.LocalComponents.commute_of_ne _ _ (hcomp hK) (hcomp hL)
    hne'
  have hmem := Subgroup.commutator_mem_commutator
    (show (⟨a, hK.1 ha⟩ : ↥C) ∈ K.subgroupOf C from ha)
    (show (⟨b, hL.1 hb⟩ : ↥C) ∈ L.subgroupOf C from hb)
  rw [h, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at hmem
  exact congrArg Subtype.val hmem

theorem component_mem_named_factors {G : Type*} [Group G] [Finite G] {C : Subgroup G}
    {ι : Type*} [Finite ι] (F : ι → Subgroup G) (hF : ∀ i, IsComponentOf (F i) C)
    (hperf : ∀ P : Subgroup G, P ≤ C → commutator ↥P = ⊤ → P ≤ ⨆ i, F i)
    {K : Subgroup G} (hK : IsComponentOf K C) : ∃ i, K = F i := by
  by_contra hcon
  push_neg at hcon
  have hKle : K ≤ ⨆ i, F i := hperf K hK.1 hK.2.2.1
  have hcent : (⨆ i, F i) ≤ Subgroup.centralizer (K : Set G) := by
    refine iSup_le fun i y hy => ?_
    rw [Subgroup.mem_centralizer_iff]
    intro k hk
    exact mul_comm_of_components_ne hK (hF i) (hcon i) hk hy
  have hcomm : ∀ a b : ↥K, a * b = b * a := by
    intro a b
    have hb : (b : G) ∈ Subgroup.centralizer (K : Set G) := hcent (hKle b.2)
    rw [Subgroup.mem_centralizer_iff] at hb
    exact Subtype.ext (hb a a.2)
  haveI : Group.IsSolvable ↥K := isSolvable_of_comm hcomm
  exact false_of_isQuasisimple_of_isSolvable hK.2.2 inferInstance

end CFSG.HardMathSupport.Solomon.Coordinator.LieComp

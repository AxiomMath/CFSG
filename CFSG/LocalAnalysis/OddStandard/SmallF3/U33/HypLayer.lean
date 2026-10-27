module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Blocks
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Basic
import CFSG.LocalAnalysis.ComponentInitial.StandardBasics
import CFSG.LocalAnalysis.ComponentClassification.AssemblyBPredicates
import CFSG.GH74.E2.QuasiRank
import CFSG.GroupTheory.LocalCores.Components
public import CFSG.Foundations.Basic

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33

open Subgroup

private lemma rank_le_one_of_isCyclic {A : Type*} [Group A] [Finite A] (h : IsCyclic A) :
    Group.rank A ≤ 1 := by
  classical
  obtain ⟨x, hx⟩ := isCyclic_iff_exists_zpowers_eq_top.mp h
  have hS : Subgroup.closure ({x} : Set A) = ⊤ := by
    rw [← Subgroup.zpowers_eq_closure]
    exact hx
  have hle : Group.rank A ≤ ({x} : Finset A).card :=
    Group.rank_le (S := ({x} : Finset A)) (by simpa using hS)
  simpa using hle

theorem inSubgroup_layer_invCent_eq {G : Type} [Group G] [Finite G] {L : Subgroup G}
    (hC : SmallF3Cyclic G L) {t : G} (ht : orderOf t = 2)
    (htL : t ∈ Subgroup.centralizer (L : Set G)) :
    CFSG.inSubgroup CFSG.layer (invCent t) = L := by
  obtain ⟨-, hLT₀, hLn₀, -, -⟩ :=
    CFSG.LocalAnalysis.ComponentInitial.standard_involution_centralizer_normality
      hC.standard htL ht
  set H : Subgroup G := invCent t with hH
  have hLT : L ≤ H := by rw [hH]; exact hLT₀
  have hLn : (L.subgroupOf H).Normal := by rw [hH]; exact hLn₀
  let L' : Subgroup H := L.subgroupOf H
  have hLcomp : CFSG.IsComponent L' := by
    refine ⟨?_, hLn.isSubnormal⟩
    have e : L' ≃* L := Subgroup.subgroupOfEquivOfLe hLT
    exact (ComponentClassification.AssemblyBPredicates.isQuasisimple_iff_native L').1
      ((ComponentClassification.AssemblyBPredicates.isQuasisimple_iff_open L').2
        (ComponentClassification.Components.quasisimple_of_equiv e hC.standard.1))
  have hL'map : L'.map H.subtype = L := Subgroup.map_subgroupOf_eq_of_le hLT
  have hlayer_le : L' ≤ CFSG.layer ↥H := by
    rw [CFSG.layer.eq_sSup]
    exact le_sSup hLcomp
  have hcomp_le : ∀ K : Subgroup H, CFSG.IsComponent K → K ≤ L' := by
    intro K hK
    by_contra hnotle
    rcases CFSG.LocalCores.distinct_components_commute hK hLcomp with hEq | hcomm
    · exact hnotle (le_of_eq hEq)
    ·
      have hcentral : K ≤ Subgroup.centralizer (L' : Set H) :=
        Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcomm
      obtain ⟨T, hTp, hTrank⟩ :=
        CFSG.GH74.E2.exists_noncyclic_sylow_two_of_quasisimple hK.1
      let f : H →* G := H.subtype
      let fK : K →* G := f.comp K.subtype
      let T₁ : Subgroup G := T.map fK
      have hfKinj : Function.Injective fK := fun a b hab =>
        K.subtype_injective (H.subtype_injective hab)
      have hT₁p : IsPGroup 2 T₁ := hTp.map fK
      have hT₁le : T₁ ≤ Subgroup.centralizer (L : Set G) := by
        rintro g ⟨u, -, rfl⟩
        rw [Subgroup.mem_centralizer_iff]
        intro l hl
        have hlH : l ∈ H := hLT hl
        have hl' : (⟨l, hlH⟩ : H) ∈ L' := hl
        have hcomm' := Subgroup.mem_centralizer_iff.mp
          (hcentral u.property) (⟨l, hlH⟩ : H) hl'
        simpa [fK, f] using congrArg (fun x : H => (x : G)) hcomm'
      let CC : Subgroup G := Subgroup.centralizer (L : Set G)
      have hT₁le' : T₁ ≤ CC := hT₁le
      have hT₂p : IsPGroup 2 (T₁.subgroupOf CC) :=
        hT₁p.of_equiv (Subgroup.subgroupOfEquivOfLe hT₁le').symm
      obtain ⟨S, hS⟩ := hT₂p.exists_le_sylow
      have hScyc : IsCyclic ↥(S : Subgroup CC) := hC.cyclic S
      have hT₂cyc : IsCyclic ↥(T₁.subgroupOf CC) := by
        haveI : IsCyclic ↥(S : Subgroup CC) := hScyc
        exact Subgroup.isCyclic_of_le hS
      have hT₂rank : Group.rank ↥(T₁.subgroupOf CC) ≤ 1 :=
        rank_le_one_of_isCyclic hT₂cyc
      have e₂ : (T₁.subgroupOf CC) ≃* T₁ := Subgroup.subgroupOfEquivOfLe hT₁le'
      have e₁ : T ≃* T₁ := Subgroup.equivMapOfInjective T fK hfKinj
      have hr₁ : Group.rank ↥T₁ = Group.rank ↥T := (Group.rank_congr e₁).symm
      have hr₂ : Group.rank ↥(T₁.subgroupOf CC) = Group.rank ↥T₁ :=
        Group.rank_congr e₂
      omega
  have hlayer_le' : CFSG.layer ↥H ≤ L' := by
    rw [CFSG.layer.eq_sSup]
    exact sSup_le fun K hK => hcomp_le K hK
  change (CFSG.layer ↥H).map H.subtype = L
  refine le_antisymm ?_ ?_
  · rw [← hL'map]
    exact Subgroup.map_mono hlayer_le'
  · rw [← hL'map]
    exact Subgroup.map_mono hlayer_le

end CFSG.OddStandard.SmallF3.HarrisU33

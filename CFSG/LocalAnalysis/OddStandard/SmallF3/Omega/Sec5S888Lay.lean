module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5Statements
import CFSG.GH74.E2.QuasiRank
public import CFSG.GroupTheory.LocalCores.Components

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

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

theorem layerC5_eq_of_setting (h52a : Asc82Lemma52a) {G : Type} [Group G] [Finite G] {d : G}
    {I : Subgroup G} (hs : Sec5Setting G d I) : layerC5 d = I := by
  set H : Subgroup G := centralizer ({d} : Set G) with hH
  have hLT : I ≤ H := hs.component.1
  let L' : Subgroup H := I.subgroupOf H
  have hLcomp : CFSG.IsComponent L' := hs.component.2
  have hL'map : L'.map H.subtype = I := Subgroup.map_subgroupOf_eq_of_le hLT
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
      have hT₁le : T₁ ≤ Subgroup.centralizer (I : Set G) := by
        rintro g ⟨u, -, rfl⟩
        rw [Subgroup.mem_centralizer_iff]
        intro l hl
        have hlH : l ∈ H := hLT hl
        have hl' : (⟨l, hlH⟩ : H) ∈ L' := hl
        have hcomm' := Subgroup.mem_centralizer_iff.mp
          (hcentral u.property) (⟨l, hlH⟩ : H) hl'
        simpa [fK, f] using congrArg (fun x : H => (x : G)) hcomm'
      let CC : Subgroup G := Subgroup.centralizer (I : Set G)
      have hT₁le' : T₁ ≤ CC := hT₁le
      have hT₂p : IsPGroup 2 (T₁.subgroupOf CC) :=
        hT₁p.of_equiv (Subgroup.subgroupOfEquivOfLe hT₁le').symm
      obtain ⟨S, hS⟩ := hT₂p.exists_le_sylow
      have hScyc : IsCyclic ↥(S : Subgroup CC) := h52a G d I hs S
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
  change (CFSG.layer ↥H).map H.subtype = I
  refine le_antisymm ?_ ?_
  · rw [← hL'map]
    exact Subgroup.map_mono hlayer_le'
  · rw [← hL'map]
    exact Subgroup.map_mono hlayer_le

end CFSG.OddStandard.SmallF3.Omega

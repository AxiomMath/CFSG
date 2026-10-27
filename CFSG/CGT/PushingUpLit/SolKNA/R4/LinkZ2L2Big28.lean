module

public import CFSG.CGT.PushingUpLit.SolKNA.R4.LinkZ2L2Big19

public section

namespace CFSG.CGT.PushingUpLit.SolKNA.R4.Z2Big

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.TL4
open CFSG.ClassicalInvolution.Q3.TL4.Z2W CFSG.GorensteinWalter
open CFSG.Blueprint

section SylowIn

variable {G : Type} [Group G] [Finite G]

theorem isSylow2In_subgroupOf_top {P S : Subgroup G} (hS : IsSylow2In S P) :
    IsSylow2In (S.subgroupOf P) ⊤ := by
  refine ⟨le_top, hS.2.1.comap_of_injective P.subtype P.subtype_injective, ?_⟩
  intro V' _ hV'p hS'V'
  let V : Subgroup G := V'.map P.subtype
  have hVP : V ≤ P := Subgroup.map_subtype_le V'
  have hVp : IsPGroup 2 ↥V := hV'p.map P.subtype
  have hSV : S ≤ V := by
    have h := Subgroup.map_mono (f := P.subtype) hS'V'
    have h' : Subgroup.map P.subtype (S.subgroupOf P) = S :=
      Subgroup.map_subgroupOf_eq_of_le hS.1
    rwa [h'] at h
  have hVS : V = S := hS.2.2 V hVP hVp hSV
  have hV'comap : V.comap P.subtype = V' :=
    Subgroup.comap_map_eq_self_of_injective (f := P.subtype) P.subtype_injective V'
  rw [← hV'comap, hVS]
  rfl

theorem exists_conj_le_of_isSylow2In {P S H : Subgroup G} (hS : IsSylow2In S P)
    (hH : IsPGroup 2 ↥H) (hHP : H ≤ P) : ∃ g : G, H ≤ conjSub g S := by
  haveI : Finite ↥P := Subtype.finite
  have hS' : IsSylow2In (S.subgroupOf P) ⊤ := isSylow2In_subgroupOf_top hS
  have hH' : IsPGroup 2 ↥(H.subgroupOf P) :=
    hH.comap_of_injective P.subtype P.subtype_injective
  obtain ⟨g', hg'⟩ := exists_conj_ge_of_isSylow2In hS' hH'
  refine ⟨(g' : G), ?_⟩
  intro h hh
  have hhP : h ∈ P := hHP hh
  have hmem : (⟨h, hhP⟩ : ↥P) ∈ H.subgroupOf P := Subgroup.mem_subgroupOf.mpr hh
  have hconj := hg' hmem
  rw [mem_conjSub_iff] at hconj
  have hconj' : (g' : G)⁻¹ * h * (g' : G) ∈ S := by
    simpa using (Subgroup.mem_subgroupOf.mp hconj)
  rw [mem_conjSub_iff]
  exact hconj'

end SylowIn

end CFSG.CGT.PushingUpLit.SolKNA.R4.Z2Big

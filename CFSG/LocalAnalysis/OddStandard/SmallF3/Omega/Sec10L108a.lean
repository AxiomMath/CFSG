module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec10Sylow

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup

variable {G : Type} [Group G]

theorem sec10_inf_join_le [Finite G] {t : G} {L S : Subgroup G} (hS : IsPGroup 2 S)
    (hP : IsSylow2Of (S ⊓ L) L) (hLC : L ⊓ centralizer (L : Set G) = ⊥)
    (hSC : centralizer (L : Set G) ⊓ S = zpowers t) :
    S ⊓ (L ⊔ centralizer (L : Set G)) ≤ (S ⊓ L) ⊔ zpowers t := by
  let C := centralizer (L : Set G)
  change S ⊓ (L ⊔ C) ≤ (S ⊓ L) ⊔ zpowers t
  have hLC' : L ⊓ C = ⊥ := hLC
  have hSC' : C ⊓ S = zpowers t := hSC
  let comm : ∀ l : ↥L, ∀ c : ↥C, Commute (L.subtype l) (C.subtype c) := fun l c =>
    Subgroup.mem_centralizer_iff.mp (show (c : G) ∈ centralizer (L : Set G) from c.2) l l.2
  let f : ↥L × ↥C →* G := L.subtype.noncommCoprod C.subtype comm
  have hfdef : f = L.subtype.noncommCoprod C.subtype comm := rfl
  have hrange : f.range = L ⊔ C := by
    rw [hfdef, MonoidHom.noncommCoprod_range, Subgroup.range_subtype, Subgroup.range_subtype]
  have hdisj : Disjoint L C := disjoint_iff.mpr hLC'
  have hinj : Function.Injective f := by
    rw [hfdef, MonoidHom.noncommCoprod_injective]
    exact ⟨Subtype.coe_injective, Subtype.coe_injective,
      by simpa only [Subgroup.range_subtype] using hdisj⟩
  let V : Subgroup (↥L × ↥C) := (S ⊓ (L ⊔ C)).comap f
  have hV2 : IsPGroup 2 V := (hS.to_le inf_le_left).comap_of_injective f hinj
  let W : Subgroup G := (V.map (MonoidHom.fst ↥L ↥C)).map L.subtype
  have hW2 : IsPGroup 2 W := (hV2.map (MonoidHom.fst ↥L ↥C)).map L.subtype
  have hWL : W ≤ L := Subgroup.map_subtype_le _
  have hPLW : S ⊓ L ≤ W := by
    intro p hp
    have hpV : ((⟨p, hp.2⟩ : ↥L), 1) ∈ V := by
      have hf : f ((⟨p, hp.2⟩ : ↥L), 1) = p := by
        rw [hfdef, MonoidHom.noncommCoprod_apply]
        simp
      change f ((⟨p, hp.2⟩ : ↥L), 1) ∈ S ⊓ (L ⊔ C)
      rw [hf]
      exact ⟨hp.1, Subgroup.mem_sup_left hp.2⟩
    refine Subgroup.mem_map.mpr ⟨(⟨p, hp.2⟩ : ↥L), ?_, rfl⟩
    exact Subgroup.mem_map.mpr ⟨((⟨p, hp.2⟩ : ↥L), 1), hpV, rfl⟩
  have hWeq : W = S ⊓ L := hP.eq_of_le hWL hW2 hPLW
  intro u hu
  obtain ⟨huS, huI⟩ := hu
  have hurange : u ∈ f.range := hrange.symm ▸ huI
  rw [MonoidHom.mem_range] at hurange
  obtain ⟨⟨l, c⟩, hlc⟩ := hurange
  have hlc' : (l : G) * (c : G) = u := by
    have h := hlc
    rw [hfdef, MonoidHom.noncommCoprod_apply] at h
    simpa using h
  have hlcV : (l, c) ∈ V := by
    change f (l, c) ∈ S ⊓ (L ⊔ C)
    rw [hlc]
    exact ⟨huS, huI⟩
  have hlW : (l : G) ∈ W := by
    refine Subgroup.mem_map.mpr ⟨l, ?_, rfl⟩
    exact Subgroup.mem_map.mpr ⟨(l, c), hlcV, rfl⟩
  have hlSL : (l : G) ∈ S ⊓ L := hWeq ▸ hlW
  have hcS : (c : G) ∈ S := by
    rw [eq_inv_mul_of_mul_eq hlc']
    exact S.mul_mem (S.inv_mem hlSL.1) huS
  have hczt : (c : G) ∈ zpowers t := by
    have : (c : G) ∈ C ⊓ S := ⟨c.2, hcS⟩
    rwa [hSC'] at this
  rw [← hlc']
  exact Subgroup.mul_mem_sup hlSL hczt

end CFSG.OddStandard.SmallF3.Omega

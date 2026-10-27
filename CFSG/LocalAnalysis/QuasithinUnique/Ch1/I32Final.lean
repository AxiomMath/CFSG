module

public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.I32Main

public section

namespace CFSG.QuasithinUnique.I32

open CFSG.ComponentClassification CFSG.QuasithinUnique.Id2519

section Transport

variable {G : Type} [Group G] [Finite G] {H : Subgroup G}

omit [Finite G] in
theorem map_normalClosureLayer (L : Subgroup ↥H) :
    (normalClosureLayer L).map H.subtype =
      ⨆ g ∈ oddLayer H, CFSG.conjugate (L.map H.subtype) g := by
  unfold normalClosureLayer
  rw [Subgroup.map_iSup]
  simp_rw [Subgroup.map_iSup, map_conjugate]
  rw [oddLayer_eq_map]
  apply le_antisymm
  · exact iSup_le fun g => iSup_le fun hg => le_iSup₂_of_le (H.subtype g) ⟨g, hg, rfl⟩ le_rfl
  · refine iSup₂_le fun g' hg' => ?_
    obtain ⟨g, hg, rfl⟩ := hg'
    exact le_iSup_of_le g (le_iSup_of_le hg le_rfl)

theorem isTwoComponentIn_map (A : Subgroup ↥H) :
    IsTwoComponentIn (A.map H.subtype) H ↔ TwoComponents.IsTwoComponent A := by
  have hle : A.map H.subtype ≤ H := Subgroup.map_subtype_le A
  have h : (A.map H.subtype).subgroupOf H = A :=
    Subgroup.comap_map_eq_self_of_injective H.subtype_injective A
  rw [isTwoComponentIn_iff hle, h]

end Transport

theorem lemmaI32 : Id2519.LemmaI32 := by
  intro G _ _ H _hK t htH ht1 ht2 L hL
  have hLZ : L ≤ H ⊓ Subgroup.centralizer ({t} : Set G) := CFSG.Quasithin.le_of_mem_cComp hL.1
  have hLH : L ≤ H := hLZ.trans inf_le_left
  let t' : ↥H := ⟨t, htH⟩
  have ht1' : t' ≠ 1 := fun h => ht1 (congrArg Subtype.val h)
  have ht2' : t' * t' = 1 := Subtype.ext (by simpa [sq] using ht2)
  let C : Subgroup ↥H := (H ⊓ Subgroup.centralizer ({t} : Set G)).subgroupOf H
  have hC : C = Subgroup.centralizer ({t'} : Set ↥H) := by
    ext x
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_inf, Subgroup.mem_centralizer_singleton_iff,
      Subgroup.mem_centralizer_singleton_iff]
    constructor
    · rintro ⟨-, hx⟩
      exact Subtype.ext hx
    · intro hx
      exact ⟨x.2, congrArg Subtype.val hx⟩
  let LX : Subgroup ↥H := L.subgroupOf H
  have hLX : LX.map H.subtype = L := Subgroup.map_subgroupOf_eq_of_le hLH
  have hLXC : LX ≤ C := fun x hx => hLZ hx
  have hLtwo : TwoComponents.IsTwoComponent (LX.subgroupOf C) := by
    let e : ↥C ≃* ↥(H ⊓ Subgroup.centralizer ({t} : Set G)) :=
      Subgroup.subgroupOfEquivOfLe inf_le_left
    have h1 := (isTwoComponentIn_iff hLZ).mp hL
    have hmap : (LX.subgroupOf C).map e.toMonoidHom =
        L.subgroupOf (H ⊓ Subgroup.centralizer ({t} : Set G)) := by
      ext x
      constructor
      · rintro ⟨y, hy, rfl⟩
        exact hy
      · intro hx
        exact ⟨⟨⟨x.1, x.2.1⟩, x.2⟩, hx, rfl⟩
    exact (TwoComponentTransport.equiv_iff e _).mp (by rw [hmap]; exact h1)
  have hcj : ∀ A : Subgroup ↥H, (CFSG.conjugate A t').map H.subtype =
      CFSG.conjugate (A.map H.subtype) t := fun A => map_conjugate H.subtype A t'
  have key := abstract_I32 ht1' ht2' hC hLXC hLtwo
  have hK : (⨆ g ∈ oddLayer H, CFSG.conjugate L g) = (normalClosureLayer LX).map H.subtype := by
    rw [map_normalClosureLayer, hLX]
  rw [hK]
  rcases key with ⟨hK2, hKt⟩ | ⟨JX, hJX, hJne, hKJ, hiso⟩
  · left
    refine ⟨(isTwoComponentIn_map _).mpr hK2, ?_⟩
    rw [← BenderBranch.conjugate_eq_iff_mem_normalizer, ← hcj, hKt]
  · right
    refine ⟨JX.map H.subtype, (isTwoComponentIn_map JX).mpr hJX, ?_, ?_, ?_⟩
    · intro h
      apply hJne
      rw [← hcj] at h
      exact Subgroup.map_injective H.subtype_injective h
    · rw [hKJ, Subgroup.map_sup, hcj]
    · have eA : ↥JX ≃* ↥(JX.map H.subtype) := JX.equivMapOfInjective H.subtype H.subtype_injective
      have eB : ↥LX ≃* ↥L :=
        (LX.equivMapOfInjective H.subtype H.subtype_injective).trans
          (MulEquiv.subgroupCongr hLX)
      exact oddTwoIso_of_mulEquiv eA eB hiso

end CFSG.QuasithinUnique.I32

module

public import CFSG.ClassicalInvolution.SmallCases.Hat2A7EX3

public section

namespace CFSG.ClassicalInvolution.Hat2A7

open CFSG.Open
open CFSG.ClassicalInvolution.Balance (oddCoreIn)
open scoped commutatorElement

section Family

variable {F : Type} [Group F]

@[expose] def restrictTo (Λ : Set (Subgroup F)) (Y : Subgroup F) : Set (Subgroup ↥Y) :=
  (fun L => L.subgroupOf Y) '' Λ

theorem le_of_mem_of_iSup_eq {Y : Subgroup F} {Λ : Set (Subgroup F)} (hY : ⨆ L ∈ Λ, L = Y)
    {L : Subgroup F} (hL : L ∈ Λ) : L ≤ Y :=
  hY ▸ le_iSup₂ (f := fun L (_ : L ∈ Λ) => L) L hL

theorem inClass2A7_restrictTo_rel {Y' Y : Subgroup F} (hYY' : Y ≤ Y') {Λ : Set (Subgroup F)}
    (hne : Λ.Nonempty) (hY : ⨆ L ∈ Λ, L = Y)
    (hinv : ∀ y ∈ Y, ∀ L ∈ Λ, L.map (MulAut.conj y).toMonoidHom ∈ Λ)
    (hcls : ∀ L ∈ Λ, ∃ u : F, IsClassical2A7 Y' L u) : InClass2A7 (restrictTo Λ Y) := by
  have hle : ∀ L ∈ Λ, L ≤ Y := fun L hL => le_of_mem_of_iSup_eq hY hL
  refine ⟨?_, ?_, ?_, ?_⟩
  · obtain ⟨L, hL⟩ := hne
    exact ⟨_, L, hL, rfl⟩
  · rintro g _ ⟨L, hL, rfl⟩
    exact ⟨L.map (MulAut.conj (g : F)).toMonoidHom, hinv g g.2 L hL, (map_conj_subgroupOf g).symm⟩
  · have hmapG : (⨆ N ∈ restrictTo Λ Y, N).map Y.subtype = Y := by
      refine le_antisymm (Subgroup.map_subtype_le _) (hY.symm.le.trans (iSup₂_le fun L hL => ?_))
      have hmem : L.subgroupOf Y ∈ restrictTo Λ Y := ⟨L, hL, rfl⟩
      have h1 : L.subgroupOf Y ≤ ⨆ N ∈ restrictTo Λ Y, N := le_iSup₂_of_le _ hmem le_rfl
      calc L = (L.subgroupOf Y).map Y.subtype := by
            rw [Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr (hle L hL)]
        _ ≤ _ := Subgroup.map_mono h1
    apply Subgroup.map_injective Y.subtype_injective
    rw [hmapG, Subgroup.map_top, Subgroup.range_subtype]
  · rintro _ ⟨L, hL, rfl⟩
    obtain ⟨u, hu⟩ := hcls L hL
    exact ⟨_, hu.subgroupOf (hle L hL) hYY'⟩

theorem inClass2A7_restrictTo {Y : Subgroup F} {Λ : Set (Subgroup F)} (hne : Λ.Nonempty)
    (hY : ⨆ L ∈ Λ, L = Y)
    (hinv : ∀ y ∈ Y, ∀ L ∈ Λ, L.map (MulAut.conj y).toMonoidHom ∈ Λ)
    (hcls : ∀ L ∈ Λ, ∃ u : F, IsClassical2A7 ⊤ L u) : InClass2A7 (restrictTo Λ Y) := by
  exact inClass2A7_restrictTo_rel le_top hne hY hinv hcls

end Family

section Collapse

variable {F : Type} [Group F] [Finite F]

theorem a7SystemMod_restrictTo (hB : CITBelow2A7 (Nat.card F)) {Y : Subgroup F} (hYne : Y ≠ ⊤)
    {Λ : Set (Subgroup F)} (hne : Λ.Nonempty) (hY : ⨆ L ∈ Λ, L = Y)
    (hinv : ∀ y ∈ Y, ∀ L ∈ Λ, L.map (MulAut.conj y).toMonoidHom ∈ Λ)
    (hcls : ∀ L ∈ Λ, ∃ u : F, IsClassical2A7 ⊤ L u) : A7SystemMod (restrictTo Λ Y) :=
  hB ↥Y (card_lt_of_ne_top' hYne) _ (inClass2A7_restrictTo hne hY hinv hcls)

variable (hB : CITBelow2A7 (Nat.card F)) {Y : Subgroup F} (hYne : Y ≠ ⊤)
  {Λ : Set (Subgroup F)} (hne : Λ.Nonempty) (hY : ⨆ L ∈ Λ, L = Y)
  (hinv : ∀ y ∈ Y, ∀ L ∈ Λ, L.map (MulAut.conj y).toMonoidHom ∈ Λ)
  (hcls : ∀ L ∈ Λ, ∃ u : F, IsClassical2A7 ⊤ L u)

include hB hYne hne hY hinv hcls

theorem exists_component_of_collapse {L : Subgroup F} (hL : L ∈ Λ) :
    ∃ (Φ : Set (Subgroup (↥Y ⧸ classicalInvolutionOddCore ↥Y)))
      (D : A7SystemData (↥Y ⧸ classicalInvolutionOddCore ↥Y) Φ) (i : Fin D.card),
      D.comp i = (L.subgroupOf Y).map (QuotientGroup.mk' (classicalInvolutionOddCore ↥Y)) := by
  obtain ⟨D⟩ := a7SystemMod_restrictTo hB hYne hne hY hinv hcls
  have hmem : (L.subgroupOf Y).map (QuotientGroup.mk' (classicalInvolutionOddCore ↥Y)) ∈
      oddQuotientFamily2A7 (restrictTo Λ Y) := ⟨_, ⟨L, hL, rfl⟩, rfl⟩
  rw [D.members] at hmem
  obtain ⟨i, hi⟩ := hmem
  exact ⟨_, D, i, hi⟩

theorem images_eq_or_commute_of_collapse {L M : Subgroup F} (hL : L ∈ Λ) (hM : M ∈ Λ) :
    (L.subgroupOf Y).map (QuotientGroup.mk' (classicalInvolutionOddCore ↥Y)) =
        (M.subgroupOf Y).map (QuotientGroup.mk' (classicalInvolutionOddCore ↥Y)) ∨
      ∀ a ∈ L, ∀ b ∈ M, a * b * a⁻¹ * b⁻¹ ∈ oddCoreIn Y := by
  obtain ⟨D⟩ := a7SystemMod_restrictTo hB hYne hne hY hinv hcls
  have hLY : L ≤ Y := le_of_mem_of_iSup_eq hY hL
  have hMY : M ≤ Y := le_of_mem_of_iSup_eq hY hM
  have hmemL : (L.subgroupOf Y).map (QuotientGroup.mk' (classicalInvolutionOddCore ↥Y)) ∈
      oddQuotientFamily2A7 (restrictTo Λ Y) := ⟨_, ⟨L, hL, rfl⟩, rfl⟩
  have hmemM : (M.subgroupOf Y).map (QuotientGroup.mk' (classicalInvolutionOddCore ↥Y)) ∈
      oddQuotientFamily2A7 (restrictTo Λ Y) := ⟨_, ⟨M, hM, rfl⟩, rfl⟩
  rw [D.members] at hmemL hmemM
  obtain ⟨i, hi⟩ := hmemL
  obtain ⟨j, hj⟩ := hmemM
  by_cases hij : i = j
  · subst hij
    exact Or.inl (hi.symm.trans hj)
  · refine Or.inr fun a ha b hb => ?_
    have hai : QuotientGroup.mk' (classicalInvolutionOddCore ↥Y) ⟨a, hLY ha⟩ ∈ D.comp i := by
      rw [hi]
      exact ⟨⟨a, hLY ha⟩, Subgroup.mem_subgroupOf.mpr ha, rfl⟩
    have hbj : QuotientGroup.mk' (classicalInvolutionOddCore ↥Y) ⟨b, hMY hb⟩ ∈ D.comp j := by
      rw [hj]
      exact ⟨⟨b, hMY hb⟩, Subgroup.mem_subgroupOf.mpr hb, rfl⟩
    have h1 := D.commute i j hij _ hai _ hbj
    refine ⟨⟨a * b * a⁻¹ * b⁻¹, Y.mul_mem (Y.mul_mem (Y.mul_mem (hLY ha) (hMY hb))
      (Y.inv_mem (hLY ha))) (Y.inv_mem (hMY hb))⟩, ?_, rfl⟩
    apply (QuotientGroup.eq_one_iff _).mp
    set π := QuotientGroup.mk' (classicalInvolutionOddCore ↥Y) with hπ
    show π (⟨a, hLY ha⟩ * ⟨b, hMY hb⟩ * (⟨a, hLY ha⟩ : ↥Y)⁻¹ * (⟨b, hMY hb⟩ : ↥Y)⁻¹) = 1
    rw [map_mul, map_mul, map_mul, map_inv, map_inv, h1]
    group

theorem oddCoreIn_le_oddCoreIn_of_collapse {L : Subgroup F} (hL : L ∈ Λ) :
    oddCoreIn L ≤ oddCoreIn Y := by
  obtain ⟨Φ, D, i, hi⟩ := exists_component_of_collapse hB hYne hne hY hinv hcls hL
  have hLY : L ≤ Y := le_of_mem_of_iSup_eq hY hL
  have hrange : ((QuotientGroup.mk' (classicalInvolutionOddCore ↥Y)).comp
      (Subgroup.inclusion hLY)).range =
      (L.subgroupOf Y).map (QuotientGroup.mk' (classicalInvolutionOddCore ↥Y)) := by
    ext q
    rw [MonoidHom.mem_range, Subgroup.mem_map]
    constructor
    · rintro ⟨y, rfl⟩
      exact ⟨Subgroup.inclusion hLY y, Subgroup.mem_subgroupOf.mpr y.2, rfl⟩
    · rintro ⟨a, ha, rfl⟩
      exact ⟨⟨(a : F), Subgroup.mem_subgroupOf.mp ha⟩, rfl⟩
  rintro _ ⟨x, hx, rfl⟩
  exact ⟨Subgroup.inclusion hLY x,
    map_mem_oddCore_of_system D i (Subgroup.inclusion hLY) (hi.trans hrange.symm) hx, rfl⟩

end Collapse

end CFSG.ClassicalInvolution.Hat2A7

module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Harada.Lemma24Ind
public import CFSG.GH74.Uniqueness.SU.SU5A8

public section

namespace CFSG.EvenSporadicStandard.HNRecog.Harada

open Subgroup CFSG.GH74.Uniqueness.SU.SU5

variable {G : Type} [Group G]

abbrev Y24 (a : G) : Type := ↥(centralizer ({a} : Set G))

@[expose] def aY (a : G) : Y24 a :=
  ⟨a, Subgroup.mem_centralizer_singleton_iff.mpr rfl⟩

@[expose] def tY {a t : G} (h : a ∈ centralizer ({t} : Set G)) : Y24 a :=
  ⟨t, Subgroup.mem_centralizer_singleton_iff.mpr
    (Subgroup.mem_centralizer_singleton_iff.mp h).symm⟩

@[expose] def τY (a t : G) (y : Y24 a) : Prop := IsConj t (y : G)

@[expose] def FY (ι : Elem2 6 →* G) (a : G) : Subgroup (Y24 a) :=
  (F24 ι a).subgroupOf (centralizer ({a} : Set G))

@[expose] def PY (ι : Elem2 6 →* G) (a : G) : Subgroup (Y24 a) :=
  (P24 ι a).subgroupOf (centralizer ({a} : Set G))

variable (Y : Subgroup G)

theorem card_subgroupOf_of_le {K : Subgroup G} (hK : K ≤ Y) :
    Nat.card ↥(K.subgroupOf Y) = Nat.card ↥K :=
  Nat.card_congr (Subgroup.subgroupOfEquivOfLe hK).toEquiv

theorem commutator_subgroupOf_of_le {K L : Subgroup G} (hK : K ≤ Y) (hL : L ≤ Y) :
    ⁅K.subgroupOf Y, L.subgroupOf Y⁆ = (⁅K, L⁆).subgroupOf Y := by
  have hKL : ⁅K, L⁆ ≤ Y :=
    (Subgroup.commutator_mono hK hL).trans (Subgroup.commutator_le_self Y)
  apply Subgroup.map_subtype_inj.mp
  rw [Subgroup.map_commutator,
    Subgroup.map_subgroupOf_eq_of_le hK, Subgroup.map_subgroupOf_eq_of_le hL,
    Subgroup.map_subgroupOf_eq_of_le hKL]

theorem map_subtype_centralizer_singleton (y : ↥Y) :
    (centralizer ({y} : Set ↥Y)).map Y.subtype = centralizer ({(y : G)} : Set G) ⊓ Y := by
  ext x
  rw [Subgroup.mem_map, Subgroup.mem_inf]
  constructor
  · rintro ⟨z, hz, rfl⟩
    refine ⟨?_, z.2⟩
    rw [Subgroup.mem_centralizer_singleton_iff] at hz ⊢
    exact congrArg Subtype.val hz
  · rintro ⟨hx, hxY⟩
    refine ⟨⟨x, hxY⟩, ?_, rfl⟩
    rw [Subgroup.mem_centralizer_singleton_iff] at hx ⊢
    exact Subtype.ext hx

theorem map_subtype_closure (S : Set ↥Y) :
    (Subgroup.closure S).map Y.subtype = Subgroup.closure (Subtype.val '' S) :=
  MonoidHom.map_closure Y.subtype S

theorem map_subtype_zpowers (y : ↥Y) : (zpowers y).map Y.subtype = zpowers (y : G) :=
  MonoidHom.map_zpowers Y.subtype y

theorem isA8Type_subgroupOf {K : Subgroup G} (hK : K ≤ Y) (h : IsA8Type ↥K) :
    IsA8Type ↥(K.subgroupOf Y) := by
  obtain ⟨Q, ⟨e⟩⟩ := h
  exact ⟨Q, ⟨(Subgroup.subgroupOfEquivOfLe hK).trans e⟩⟩

theorem ncard_image_val (S : Set ↥Y) : (Subtype.val '' S).ncard = S.ncard :=
  Set.ncard_image_of_injective S Subtype.val_injective

end CFSG.EvenSporadicStandard.HNRecog.Harada

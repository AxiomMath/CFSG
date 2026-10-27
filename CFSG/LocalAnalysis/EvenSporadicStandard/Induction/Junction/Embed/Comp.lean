module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Junction.GroupLemmas
public import CFSG.GroupTheory.ConjugatePairSubnormality

public section

namespace CFSG.EvenSporadicStandard.Induction.Junction

open Subgroup CFSG.EvenSporadicStandard.Induction CFSG.EvenSporadicStandard.Solomon78
open scoped commutatorElement

variable {H : Type} [Group H] (Y : Subgroup H)

theorem map_subtype_centralizer (Ut : Subgroup ↥Y) :
    (centralizer (Ut : Set ↥Y)).map Y.subtype =
      centralizer ((Ut.map Y.subtype : Subgroup H) : Set H) ⊓ Y := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    refine ⟨mem_centralizer_iff.2 ?_, y.2⟩
    rintro _ ⟨u, hu, rfl⟩
    exact congrArg Subtype.val (mem_centralizer_iff.1 hy u hu)
  · rintro ⟨hx, hxY⟩
    refine ⟨⟨x, hxY⟩, mem_centralizer_iff.2 fun u hu => ?_, rfl⟩
    exact Subtype.ext (mem_centralizer_iff.1 hx (u : H) ⟨u, hu, rfl⟩)

theorem map_subtype_conj (Lt : Subgroup ↥Y) (s : ↥Y) :
    (Lt.map (MulAut.conj s).toMonoidHom).map Y.subtype =
      (Lt.map Y.subtype).map (MulAut.conj (s : H)).toMonoidHom := by
  rw [Subgroup.map_map, Subgroup.map_map]
  congr 1

theorem isQuasisimple_map_subtype {Lt : Subgroup ↥Y} (h : CFSG.IsQuasisimple ↥Lt) :
    CFSG.IsQuasisimple ↥(Lt.map Y.subtype) :=
  CFSG.LocalCores.isQuasisimple_of_mulEquiv (Lt.equivMapOfInjective Y.subtype Y.subtype_injective) h

theorem isCompIn_map_subtype {M T : Subgroup H} {Lt Ut : Subgroup ↥Y} (hMY : M ≤ Y)
    (hM : IsCompIn M (centralizer (T : Set H))) (hTU : T ≤ Ut.map Y.subtype)
    (hL : Lt ≤ M.subgroupOf Y) (h : IsCompIn Lt (centralizer (Ut : Set ↥Y))) :
    IsCompIn (Lt.map Y.subtype) (centralizer ((Ut.map Y.subtype : Subgroup H) : Set H)) := by
  set UH : Subgroup H := Ut.map Y.subtype with hUH
  set CH : Subgroup H := centralizer (UH : Set H) with hCH
  set L : Subgroup H := Lt.map Y.subtype with hLdef
  have hCT : CH ≤ centralizer (T : Set H) := Subgroup.centralizer_le (by exact_mod_cast hTU)
  have hLM : L ≤ M := by
    rintro _ ⟨x, hx, rfl⟩
    exact hL hx
  have hLC : L ≤ CH := by
    have := Subgroup.map_mono (f := Y.subtype) h.1
    rw [map_subtype_centralizer] at this
    exact this.trans inf_le_left
  have hLY : L ≤ Y := by
    rintro _ ⟨x, -, rfl⟩
    exact x.2
  set D : Subgroup H := CH ⊓ Y with hD
  have h1 : (L.subgroupOf D).IsSubnormal := by
    have := isSubnormal_subgroupOf_map Y.subtype h.1 h.2.2
    rwa [map_subtype_centralizer] at this
  have h2 : ((M ⊓ CH).subgroupOf CH).IsSubnormal := by
    have : (M ⊓ CH).subgroupOf CH = M.subgroupOf CH := by
      ext x
      simp only [Subgroup.mem_subgroupOf, Subgroup.mem_inf]
      exact ⟨fun hx => hx.1, fun hx => ⟨hx, x.2⟩⟩
    rw [this]
    exact CFSG.GroupTheory.isSubnormal_subgroupOf_of_le hCT hM.2.2
  have hMCD : M ⊓ CH ≤ D := fun x hx => ⟨hx.2, hMY hx.1⟩
  have h3 : (L.subgroupOf (M ⊓ CH)).IsSubnormal :=
    CFSG.GroupTheory.isSubnormal_subgroupOf_of_le hMCD h1
  have h4 : (L.subgroupOf CH).IsSubnormal :=
    CFSG.GroupTheory.isSubnormal_subgroupOf_trans (le_inf hLM hLC) inf_le_right h3 h2
  exact isCompIn_of_subnormal hLC (isQuasisimple_map_subtype Y h.isQuasisimple) h4

theorem isCompIn_comap_subtype {Z : Subgroup H} {Ut : Subgroup ↥Y} (hZ : Z ≤ Y)
    (h : IsCompIn Z (centralizer ((Ut.map Y.subtype : Subgroup H) : Set H) ⊓ Y)) :
    IsCompIn (Z.subgroupOf Y) (centralizer (Ut : Set ↥Y)) := by
  have hD : (centralizer (Ut : Set ↥Y)).map Y.subtype =
      centralizer ((Ut.map Y.subtype : Subgroup H) : Set H) ⊓ Y := map_subtype_centralizer Y Ut
  have hsub : ((Z.comap Y.subtype).subgroupOf (centralizer (Ut : Set ↥Y))).IsSubnormal :=
    isSubnormal_subgroupOf_comap Y.subtype (D := centralizer (Ut : Set ↥Y))
      (N := centralizer ((Ut.map Y.subtype : Subgroup H) : Set H) ⊓ Y) hD.le h.2.2
  have hq : CFSG.IsQuasisimple ↥(Z.subgroupOf Y) :=
    CFSG.LocalCores.isQuasisimple_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hZ).symm
      h.isQuasisimple
  have hZC : Z.subgroupOf Y ≤ centralizer (Ut : Set ↥Y) := by
    intro x hx
    refine mem_centralizer_iff.2 fun u hu => ?_
    have := mem_centralizer_iff.1 (h.1 hx).1 (u : H) ⟨u, hu, rfl⟩
    exact Subtype.ext this
  exact isCompIn_of_subnormal hZC hq hsub

end CFSG.EvenSporadicStandard.Induction.Junction

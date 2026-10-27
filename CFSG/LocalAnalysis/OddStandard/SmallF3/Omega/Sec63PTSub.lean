module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec2OutLift
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec6Defs
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec63PTCover

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {G : Type} [Group G]

theorem sec63PT_isComponentIn_map_iff {X : Type} [Group X] (f : X →* G)
    (hf : Function.Injective f) {K H : Subgroup X} :
    IsComponentIn (K.map f) (H.map f) ↔ IsComponentIn K H := by
  constructor
  · intro h
    have hle : K ≤ H := (Subgroup.map_le_map_iff_of_injective hf).mp h.1
    refine ⟨hle, ?_⟩
    let e : ↥H ≃* ↥(H.map f) := H.equivMapOfInjective f hf
    have heq : (K.subgroupOf H).map e.toMonoidHom = (K.map f).subgroupOf (H.map f) := by
      apply Subgroup.map_injective (Subgroup.subtype_injective (H.map f))
      rw [Subgroup.map_map]
      have hcomp : ((H.map f).subtype).comp e.toMonoidHom = f.comp H.subtype := by
        ext m
        rfl
      rw [hcomp, ← Subgroup.map_map, Subgroup.map_subgroupOf_eq_of_le hle,
        Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr (Subgroup.map_mono hle)]
    have h' : IsComponent ((K.subgroupOf H).map e.toMonoidHom) := by
      rw [heq]
      exact h.2
    have hc := CFSG.LocalCores.isComponent_map_mulEquiv e.symm h'
    have heq' : ((K.map f).subgroupOf (H.map f)).map e.symm.toMonoidHom = K.subgroupOf H := by
      rw [← heq, CFSG.LocalCores.map_map_symm]
    rw [heq] at hc
    rw [heq'] at hc
    exact hc
  · intro h
    refine ⟨Subgroup.map_mono h.1, ?_⟩
    let e : ↥H ≃* ↥(H.map f) := H.equivMapOfInjective f hf
    have heq : (K.subgroupOf H).map e.toMonoidHom = (K.map f).subgroupOf (H.map f) := by
      apply Subgroup.map_injective (Subgroup.subtype_injective (H.map f))
      rw [Subgroup.map_map]
      have hcomp : ((H.map f).subtype).comp e.toMonoidHom = f.comp H.subtype := by
        ext m
        rfl
      rw [hcomp, ← Subgroup.map_map, Subgroup.map_subgroupOf_eq_of_le h.1,
        Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr (Subgroup.map_mono h.1)]
    rw [← heq]
    exact CFSG.LocalCores.isComponent_map_mulEquiv e h.2

theorem sec63PT_map_subtype_centralizer (Y : Subgroup G) (y : ↥Y) :
    (centralizer ({y} : Set ↥Y)).map Y.subtype = Y ⊓ centralizer ({(y : G)} : Set G) := by
  ext g
  simp only [Subgroup.mem_map, Subgroup.mem_inf, Subgroup.mem_centralizer_singleton_iff,
    Subgroup.coe_subtype]
  constructor
  · rintro ⟨u, hu, rfl⟩
    exact ⟨u.2, congrArg Subtype.val hu⟩
  · rintro ⟨hg, hc⟩
    exact ⟨⟨g, hg⟩, Subtype.ext hc, rfl⟩

theorem sec63PT_map_subtype_fixSub (Y : Subgroup G) {s : G} (hs : s * s = 1)
    (hsN : s ∈ normalizer (Y : Set G)) :
    (fixSub (conjAut Y hs hsN)).map Y.subtype = Y ⊓ centralizer ({s} : Set G) := by
  ext g
  simp only [Subgroup.mem_map, Subgroup.mem_inf, Subgroup.mem_centralizer_singleton_iff,
    Subgroup.coe_subtype]
  constructor
  · rintro ⟨p, hp, rfl⟩
    exact ⟨p.2, ((mem_fixSub_conjAut_iff Y hs hsN p).mp hp).symm⟩
  · rintro ⟨hgY, hgs⟩
    exact ⟨⟨g, hgY⟩, (mem_fixSub_conjAut_iff Y hs hsN ⟨g, hgY⟩).mpr hgs.symm, rfl⟩

theorem sec63PT_isL29_map_iff [Finite G] {X : Type} [Group X] (f : X →* G)
    (hf : Function.Injective f) {K : Subgroup X} : IsL29 (K.map f) ↔ IsL29 K := by
  haveI : Finite X := Finite.of_injective f hf
  let e : ↥K ≃* ↥(K.map f) := K.equivMapOfInjective f hf
  have hsurj : Function.Surjective e.toMonoidHom := e.surjective
  have hker : Odd (Nat.card e.toMonoidHom.ker) := by
    rw [(MonoidHom.ker_eq_bot_iff e.toMonoidHom).mpr e.injective, Subgroup.card_bot]
    exact odd_one
  unfold IsL29
  exact (sec63PT_lieModel_psl_iff e.toMonoidHom hsurj hker 2 3 2).symm

theorem sec63PT_isPGroup_subgroupOf {Y P : Subgroup G} (hPY : P ≤ Y) (hP : IsPGroup 2 P) :
    IsPGroup 2 (P.subgroupOf Y) :=
  hP.comap_subtype

theorem sec63PT_card_subgroupOf {Y P : Subgroup G} (hPY : P ≤ Y) :
    Nat.card (P.subgroupOf Y) = Nat.card P :=
  Nat.card_congr (Subgroup.subgroupOfEquivOfLe hPY).toEquiv

theorem sec63PT_map_subtype_closure {Y : Subgroup G} {R : Subgroup ↥Y}
    (hgen : R = closure {r : ↥Y | r ∈ R ∧ orderOf r = 2}) :
    R.map Y.subtype = closure {r : G | r ∈ R.map Y.subtype ∧ orderOf r = 2} := by
  have h1 : R.map Y.subtype =
      closure (Y.subtype '' {r : ↥Y | r ∈ R ∧ orderOf r = 2}) := by
    conv_lhs => rw [hgen]
    exact MonoidHom.map_closure Y.subtype _
  have h2 : Y.subtype '' {r : ↥Y | r ∈ R ∧ orderOf r = 2} =
      {r : G | r ∈ R.map Y.subtype ∧ orderOf r = 2} := by
    ext r
    constructor
    · rintro ⟨p, ⟨hpR, hp2⟩, rfl⟩
      exact ⟨⟨p, hpR, rfl⟩,
        by rw [orderOf_injective Y.subtype Y.subtype_injective p]; exact hp2⟩
    · rintro ⟨⟨p, hpR, hpr⟩, hr2⟩
      refine ⟨p, ⟨hpR, ?_⟩, hpr⟩
      rw [← orderOf_injective Y.subtype Y.subtype_injective p, hpr]
      exact hr2
  calc R.map Y.subtype
      = closure (Y.subtype '' {r : ↥Y | r ∈ R ∧ orderOf r = 2}) := h1
    _ = closure {r : G | r ∈ R.map Y.subtype ∧ orderOf r = 2} := by rw [h2]

end CFSG.OddStandard.SmallF3.Omega

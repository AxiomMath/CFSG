module

public import CFSG.Assembly.Defs
public import CFSG.Open.Defs

public section

namespace CFSG.Assembly

variable {G G' : Type*} [Group G] [Group G']

theorem isSubnormal_iff_open {H K : Subgroup G} : IsSubnormal H K ↔ CFSG.Open.IsSubnormal H K := by
  constructor
  · intro h
    induction h with
    | refl H => exact .refl H
    | step hHM hN _ ih => exact .step hHM hN ih
  · intro h
    induction h with
    | refl H => exact .refl H
    | step hHM hN _ ih => exact .step hHM hN ih

namespace IsSubnormal

theorem le {H K : Subgroup G} (h : IsSubnormal H K) : H ≤ K := by
  induction h with
  | refl => exact le_rfl
  | step hle _ _ ih => exact hle.trans ih

theorem trans {L M K : Subgroup G} (hLM : IsSubnormal L M) (hMK : IsSubnormal M K) :
    IsSubnormal L K := by
  induction hLM with
  | refl => exact hMK
  | step hle hnormal _ ih => exact .step hle hnormal (ih hMK)

theorem map (f : G →* G') {H K : Subgroup G} (h : IsSubnormal H K) :
    IsSubnormal (H.map f) (K.map f) := by
  induction h with
  | refl => exact .refl _
  | @step H M K hle hnormal _ ih =>
    refine .step (Subgroup.map_mono hle) ?_ ih
    rw [Subgroup.normal_subgroupOf_iff (Subgroup.map_mono hle)]
    rintro _ _ ⟨h, hh, rfl⟩ ⟨m, hm, rfl⟩
    rw [Subgroup.normal_subgroupOf_iff hle] at hnormal
    exact ⟨m * h * m⁻¹, hnormal h m hh hm, by simp⟩

theorem comap (f : G →* G') {H K : Subgroup G'} (h : IsSubnormal H K) :
    IsSubnormal (H.comap f) (K.comap f) := by
  induction h with
  | refl => exact .refl _
  | @step H M K hle hnormal _ ih =>
    refine .step (Subgroup.comap_mono hle) ?_ ih
    rw [Subgroup.normal_subgroupOf_iff (Subgroup.comap_mono hle)]
    intro h m hh hm
    rw [Subgroup.normal_subgroupOf_iff hle] at hnormal
    change f (m * h * m⁻¹) ∈ H
    rw [map_mul, map_mul, map_inv]
    exact hnormal _ _ hh hm

theorem inf {L K : Subgroup G} (h : IsSubnormal L K) (H : Subgroup G) :
    IsSubnormal (L ⊓ H) (K ⊓ H) := by
  induction h with
  | refl => exact .refl _
  | @step L M K hle hnormal _ ih =>
    refine .step (inf_le_inf_right H hle) ?_ ih
    rw [Subgroup.normal_subgroupOf_iff (inf_le_inf_right H hle)]
    intro x g hx hg
    exact ⟨(Subgroup.normal_subgroupOf_iff hle).1 hnormal x g hx.1 hg.1,
      H.mul_mem (H.mul_mem hg.2 hx.2) (H.inv_mem hg.2)⟩

theorem subgroupOf {L K : Subgroup G} (h : IsSubnormal L K) : (L.subgroupOf K).IsSubnormal := by
  induction h with
  | refl H =>
    rw [Subgroup.subgroupOf_self]
    exact Subgroup.IsSubnormal.top
  | @step L M K hle hnormal _ ih =>
    have hle' : L.subgroupOf K ≤ M.subgroupOf K := Subgroup.comap_mono hle
    refine Subgroup.IsSubnormal.step (L.subgroupOf K) (M.subgroupOf K) hle' ih ?_
    rw [Subgroup.normal_subgroupOf_iff hle']
    intro x g hx hg
    exact (Subgroup.normal_subgroupOf_iff hle).1 hnormal x g hx hg

theorem of_mathlib {L : Subgroup G} (h : L.IsSubnormal) : IsSubnormal L ⊤ := by
  induction h with
  | top => exact .refl ⊤
  | step lower upper hle _ hnormal ih => exact .step hle hnormal ih

theorem mathlib {L K : Subgroup G} (h : IsSubnormal L K) (hK : K.IsSubnormal) :
    L.IsSubnormal := by
  induction h with
  | refl => exact hK
  | @step L M K hle hnormal _ ih => exact Subgroup.IsSubnormal.step L M hle (ih hK) hnormal

theorem top_iff {L : Subgroup G} : IsSubnormal L ⊤ ↔ L.IsSubnormal :=
  ⟨fun h => h.mathlib Subgroup.IsSubnormal.top, of_mathlib⟩

theorem iff_subgroupOf {L K : Subgroup G} (hLK : L ≤ K) :
    IsSubnormal L K ↔ (L.subgroupOf K).IsSubnormal := by
  refine ⟨subgroupOf, fun h => ?_⟩
  simpa only [Subgroup.map_subgroupOf_eq_of_le hLK, Subgroup.map_top, Subgroup.range_subtype]
    using (of_mathlib h).map K.subtype

theorem eq_bot_or_eq_of_isSimpleGroup {K H : Subgroup G} (h : IsSubnormal K H)
    (hH : IsSimpleGroup H) : K = ⊥ ∨ K = H := by
  rcases Subgroup.IsSubnormal.eq_bot_or_top_of_isSimpleGroup hH h.subgroupOf with h1 | h1
  · exact Or.inl ((Subgroup.subgroupOf_eq_bot.1 h1).eq_bot_of_le h.le)
  · exact Or.inr (le_antisymm h.le (Subgroup.subgroupOf_eq_top.1 h1))

theorem eq_bot_or_top [IsSimpleGroup G] {H : Subgroup G} (h : IsSubnormal H ⊤) :
    H = ⊥ ∨ H = ⊤ :=
  Subgroup.IsSubnormal.eq_bot_or_top_of_isSimpleGroup inferInstance (top_iff.1 h)

theorem inf_of_le {H K L : Subgroup G} (h : IsSubnormal H K) (hL : L ≤ K) :
    IsSubnormal (H ⊓ L) L := by
  have h' := h.inf L
  rwa [inf_eq_right.2 hL] at h'

end IsSubnormal

theorem isComponentOf_iff_open {L K : Subgroup G} :
    IsComponentOf L K ↔ CFSG.Open.IsComponentOf L K :=
  and_congr_right' (and_congr_left' isSubnormal_iff_open)

theorem IsComponentOf.of_le_of_le {L K H : Subgroup G} (hL : IsComponentOf L K) (hLH : L ≤ H)
    (hHK : H ≤ K) : IsComponentOf L H := by
  refine ⟨hLH, ?_, hL.2.2⟩
  have h := hL.2.1.inf H
  rwa [inf_eq_left.2 hLH, inf_eq_right.2 hHK] at h

end CFSG.Assembly

namespace CFSG.Open.IsSubnormal

open CFSG.Assembly (isSubnormal_iff_open)

variable {G G' : Type*} [Group G] [Group G']

theorem le {H K : Subgroup G} (h : IsSubnormal H K) : H ≤ K :=
  (isSubnormal_iff_open.2 h).le

theorem trans {L M K : Subgroup G} (hLM : IsSubnormal L M) (hMK : IsSubnormal M K) :
    IsSubnormal L K :=
  isSubnormal_iff_open.1 ((isSubnormal_iff_open.2 hLM).trans (isSubnormal_iff_open.2 hMK))

theorem map (f : G →* G') {H K : Subgroup G} (h : IsSubnormal H K) :
    IsSubnormal (H.map f) (K.map f) :=
  isSubnormal_iff_open.1 ((isSubnormal_iff_open.2 h).map f)

theorem comap (f : G →* G') {H K : Subgroup G'} (h : IsSubnormal H K) :
    IsSubnormal (H.comap f) (K.comap f) :=
  isSubnormal_iff_open.1 ((isSubnormal_iff_open.2 h).comap f)

theorem inf {L K : Subgroup G} (h : IsSubnormal L K) (H : Subgroup G) :
    IsSubnormal (L ⊓ H) (K ⊓ H) :=
  isSubnormal_iff_open.1 ((isSubnormal_iff_open.2 h).inf H)

theorem subgroupOf {L K : Subgroup G} (h : IsSubnormal L K) : (L.subgroupOf K).IsSubnormal :=
  (isSubnormal_iff_open.2 h).subgroupOf

theorem of_mathlib {L : Subgroup G} (h : L.IsSubnormal) : IsSubnormal L ⊤ :=
  isSubnormal_iff_open.1 (Assembly.IsSubnormal.of_mathlib h)

theorem mathlib {L K : Subgroup G} (h : IsSubnormal L K) (hK : K.IsSubnormal) :
    L.IsSubnormal :=
  (isSubnormal_iff_open.2 h).mathlib hK

theorem top_iff {L : Subgroup G} : IsSubnormal L ⊤ ↔ L.IsSubnormal :=
  isSubnormal_iff_open.symm.trans Assembly.IsSubnormal.top_iff

theorem iff_subgroupOf {L K : Subgroup G} (hLK : L ≤ K) :
    IsSubnormal L K ↔ (L.subgroupOf K).IsSubnormal :=
  isSubnormal_iff_open.symm.trans (Assembly.IsSubnormal.iff_subgroupOf hLK)

theorem eq_bot_or_eq_of_isSimpleGroup {K H : Subgroup G} (h : IsSubnormal K H)
    (hH : IsSimpleGroup H) : K = ⊥ ∨ K = H :=
  (isSubnormal_iff_open.2 h).eq_bot_or_eq_of_isSimpleGroup hH

theorem eq_bot_or_top [IsSimpleGroup G] {H : Subgroup G} (h : IsSubnormal H ⊤) :
    H = ⊥ ∨ H = ⊤ :=
  (isSubnormal_iff_open.2 h).eq_bot_or_top

theorem inf_of_le {H K L : Subgroup G} (h : IsSubnormal H K) (hL : L ≤ K) :
    IsSubnormal (H ⊓ L) L :=
  isSubnormal_iff_open.1 ((isSubnormal_iff_open.2 h).inf_of_le hL)

end CFSG.Open.IsSubnormal


namespace CFSG

variable {G H : Type*} [Group G] [Group H]

theorem Open.IsQuasisimple.of_mulEquiv (e : G ≃* H) (h : Open.IsQuasisimple H) :
    Open.IsQuasisimple G := by
  have : Group.IsPerfect H := ⟨h.1⟩
  have : IsSimpleGroup (H ⧸ Subgroup.center H) := h.2
  have hperfect : Group.IsPerfect G :=
    Group.IsPerfect.ofSurjective (f := e.symm.toMonoidHom) e.symm.surjective
  exact ⟨hperfect.commutator_eq_top,
    (QuotientGroup.congr (Subgroup.center G) (Subgroup.center H) e
      (Subgroup.map_center_eq e)).isSimpleGroup⟩

theorem Open.IsQuasisimple.congr (e : G ≃* H) : Open.IsQuasisimple G ↔ Open.IsQuasisimple H :=
  ⟨fun h => h.of_mulEquiv e.symm, fun h => h.of_mulEquiv e⟩

theorem Assembly.IsQuasisimple.of_mulEquiv (e : G ≃* H) (h : Assembly.IsQuasisimple H) :
    Assembly.IsQuasisimple G :=
  Open.IsQuasisimple.of_mulEquiv e h

theorem Assembly.IsQuasisimple.congr (e : G ≃* H) :
    Assembly.IsQuasisimple G ↔ Assembly.IsQuasisimple H :=
  Open.IsQuasisimple.congr e

end CFSG

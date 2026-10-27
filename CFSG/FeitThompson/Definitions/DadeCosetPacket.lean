module

public import CFSG.FeitThompson.Definitions.DadeData
import Mathlib.Tactic.Group

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

namespace CFSG.FeitThompson

open Pointwise

variable {G : Type*} [Group G]

def dadeCoset (H : G → Subgroup G) (a : G) : Set G := (H a : Set G) * {a}

def dadeSupport (H : G → Subgroup G) (a : G) : Set G :=
  ⋃ g : G, (fun x => g⁻¹ * x * g) '' dadeCoset H a

theorem dadeCoset_eq_image (H : G → Subgroup G) (a : G) :
    dadeCoset H a = (· * a) '' (H a : Set G) := Set.mul_singleton

theorem mem_dadeCoset_iff {H : G → Subgroup G} {a x : G} :
    x ∈ dadeCoset H a ↔ x * a⁻¹ ∈ H a := by
  simp only [dadeCoset_eq_image, Set.mem_image, SetLike.mem_coe]
  constructor
  · rintro ⟨u, hu, rfl⟩; simpa using hu
  · intro h; exact ⟨x * a⁻¹, h, by group⟩

theorem dadeCoset_eq_op_smul (H : G → Subgroup G) (a : G) :
    dadeCoset H a = MulOpposite.op a • (H a : Set G) := by
  ext x
  simp only [dadeCoset_eq_image, Set.mem_image, Set.mem_smul_set]
  constructor
  · rintro ⟨u, hu, rfl⟩; exact ⟨u, hu, rfl⟩
  · rintro ⟨u, hu, rfl⟩; exact ⟨u, hu, rfl⟩

theorem mul_mem_dadeCoset {H : G → Subgroup G} {a u : G} (hu : u ∈ H a) :
    u * a ∈ dadeCoset H a := mem_dadeCoset_iff.2 (by simpa using hu)

theorem self_mem_dadeCoset (H : G → Subgroup G) (a : G) : a ∈ dadeCoset H a := by
  simpa using mul_mem_dadeCoset (one_mem (H a))

theorem natCard_dadeCoset (H : G → Subgroup G) (a : G) :
    Nat.card (dadeCoset H a) = Nat.card (H a) := by
  rw [dadeCoset_eq_image]
  exact Nat.card_congr (Equiv.Set.image _ _ (mul_left_injective a)).symm

theorem mem_dadeSupport_iff {H : G → Subgroup G} {a x : G} :
    x ∈ dadeSupport H a ↔ ∃ y ∈ dadeCoset H a, IsConj y x := by
  simp only [dadeSupport, Set.mem_iUnion, Set.mem_image]
  constructor
  · rintro ⟨g, y, hy, rfl⟩
    exact ⟨y, hy, isConj_iff.2 ⟨g⁻¹, by group⟩⟩
  · rintro ⟨y, hy, hc⟩
    obtain ⟨c, hc⟩ := isConj_iff.1 hc
    exact ⟨c⁻¹, y, hy, by simpa using hc⟩

theorem dadeSupport_eq_conjugatesOfSet (H : G → Subgroup G) (a : G) :
    dadeSupport H a = Group.conjugatesOfSet (dadeCoset H a) := by
  ext x
  simp [mem_dadeSupport_iff, Group.mem_conjugatesOfSet_iff]

theorem dadeCoset_subset_dadeSupport (H : G → Subgroup G) (a : G) :
    dadeCoset H a ⊆ dadeSupport H a := by
  rw [dadeSupport_eq_conjugatesOfSet]; exact Group.subset_conjugatesOfSet

theorem self_mem_dadeSupport (H : G → Subgroup G) (a : G) : a ∈ dadeSupport H a :=
  dadeCoset_subset_dadeSupport H a (self_mem_dadeCoset H a)

theorem conj_mem_dadeSupport {H : G → Subgroup G} {a x : G} (hx : x ∈ dadeSupport H a) (g : G) :
    g⁻¹ * x * g ∈ dadeSupport H a := by
  obtain ⟨y, hy, hc⟩ := mem_dadeSupport_iff.1 hx
  exact mem_dadeSupport_iff.2 ⟨y, hy, hc.trans (isConj_iff.2 ⟨g⁻¹, by group⟩)⟩

theorem dadeSupport_finite [Finite G] (H : G → Subgroup G) (a : G) :
    (dadeSupport H a).Finite := Set.toFinite _

namespace IsDadeData

variable [Finite G] {L : Subgroup G} {A : Set G} {H : G → Subgroup G} {a : G}

theorem dadeCoset_eq_smul (hD : IsDadeData L A H) (ha : a ∈ A) :
    dadeCoset H a = a • (H a : Set G) := by
  ext x
  simp only [dadeCoset_eq_image, Set.mem_image, Set.mem_smul_set, smul_eq_mul]
  constructor
  · rintro ⟨u, hu, rfl⟩
    exact ⟨u, hu, (hD.le_centralizer ha hu) a rfl⟩
  · rintro ⟨u, hu, rfl⟩
    exact ⟨u, hu, ((hD.le_centralizer ha hu) a rfl).symm⟩

theorem one_notMem_dadeSupport (hD : IsDadeData L A H) (ha : a ∈ A) :
    (1 : G) ∉ dadeSupport H a := by
  intro h
  obtain ⟨y, hy, hc⟩ := mem_dadeSupport_iff.1 h
  have hy1 : y = 1 := isConj_one_right.1 hc.symm
  have hmem : a⁻¹ ∈ H a ⊓ L := by
    refine ⟨?_, L.inv_mem (hD.mem_of_mem ha)⟩
    have := mem_dadeCoset_iff.1 hy
    rwa [hy1, one_mul] at this
  rw [hD.inf_eq_bot_left ha] at hmem
  exact hD.ne_one ha (by simpa using hmem)

end IsDadeData

end CFSG.FeitThompson

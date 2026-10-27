module

public import CFSG.FeitThompson.Definitions.DadeCosetPacket

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

namespace CFSG.FeitThompson

variable {G : Type*} [Group G]

def totalDadeSupport (A : Set G) (H : G → Subgroup G) : Set G := ⋃ a ∈ A, dadeSupport H a

theorem mem_totalDadeSupport_iff {A : Set G} {H : G → Subgroup G} {x : G} :
    x ∈ totalDadeSupport A H ↔ ∃ a ∈ A, x ∈ dadeSupport H a := by
  simp [totalDadeSupport]

theorem dadeSupport_subset_totalDadeSupport {A : Set G} {H : G → Subgroup G} {a : G} (ha : a ∈ A) :
    dadeSupport H a ⊆ totalDadeSupport A H := fun _ hx => mem_totalDadeSupport_iff.2 ⟨a, ha, hx⟩

theorem mem_totalDadeSupport_iff_exists_isConj {A : Set G} {H : G → Subgroup G} {x : G} :
    x ∈ totalDadeSupport A H ↔ ∃ a ∈ A, ∃ y ∈ dadeCoset H a, IsConj y x := by
  simp [mem_totalDadeSupport_iff, mem_dadeSupport_iff]

theorem totalDadeSupport_eq_conjugatesOfSet (A : Set G) (H : G → Subgroup G) :
    totalDadeSupport A H = Group.conjugatesOfSet (⋃ a ∈ A, dadeCoset H a) := by
  ext x
  simp only [mem_totalDadeSupport_iff_exists_isConj, Group.mem_conjugatesOfSet_iff,
    Set.mem_iUnion, exists_prop]
  constructor
  · rintro ⟨a, ha, y, hy, hc⟩; exact ⟨y, ⟨a, ha, hy⟩, hc⟩
  · rintro ⟨y, ⟨a, ha, hy⟩, hc⟩; exact ⟨a, ha, y, hy, hc⟩

theorem conj_mem_totalDadeSupport {A : Set G} {H : G → Subgroup G} {x : G}
    (hx : x ∈ totalDadeSupport A H) (g : G) : g⁻¹ * x * g ∈ totalDadeSupport A H := by
  obtain ⟨a, ha, hx⟩ := mem_totalDadeSupport_iff.1 hx
  exact mem_totalDadeSupport_iff.2 ⟨a, ha, conj_mem_dadeSupport hx g⟩

theorem subset_totalDadeSupport (A : Set G) (H : G → Subgroup G) : A ⊆ totalDadeSupport A H :=
  fun _ ha => mem_totalDadeSupport_iff.2 ⟨_, ha, self_mem_dadeSupport H _⟩

theorem totalDadeSupport_mono {A B : Set G} (h : A ⊆ B) (H : G → Subgroup G) :
    totalDadeSupport A H ⊆ totalDadeSupport B H :=
  Set.biUnion_subset_biUnion_left h

@[simp]
theorem totalDadeSupport_empty (H : G → Subgroup G) : totalDadeSupport (∅ : Set G) H = ∅ := by
  simp [totalDadeSupport]

theorem totalDadeSupport_union (A B : Set G) (H : G → Subgroup G) :
    totalDadeSupport (A ∪ B) H = totalDadeSupport A H ∪ totalDadeSupport B H :=
  Set.biUnion_union _ _ _

theorem totalDadeSupport_finite [Finite G] (A : Set G) (H : G → Subgroup G) :
    (totalDadeSupport A H).Finite := Set.toFinite _

namespace IsDadeData

variable [Finite G] {L : Subgroup G} {A : Set G} {H : G → Subgroup G}

theorem one_notMem_totalDadeSupport (hD : IsDadeData L A H) :
    (1 : G) ∉ totalDadeSupport A H := by
  intro h
  obtain ⟨a, ha, h⟩ := mem_totalDadeSupport_iff.1 h
  exact hD.one_notMem_dadeSupport ha h

end IsDadeData

end CFSG.FeitThompson

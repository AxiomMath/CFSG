module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.Classes

public section

namespace CFSG.EvenSporadicStandard.HNRecog.Section3

open CFSG.EvenSporadicStandard.HNRecog

private theorem commutator_le_of_index_eq_two' {Y : Type*} [Group Y] {N : Subgroup Y}
    (hN : N.index = 2) : _root_.commutator Y ≤ N := by
  rw [_root_.commutator_def, Subgroup.commutator_le]
  intro g₁ _ g₂ _
  rw [commutatorElement_def, Subgroup.mul_mem_iff_of_index_two hN,
    Subgroup.mul_mem_iff_of_index_two hN, Subgroup.mul_mem_iff_of_index_two hN, inv_mem_iff,
    inv_mem_iff]
  tauto

private theorem mul_inv_mem_of_index_eq_two' {H : Type*} [Group H] {E : Subgroup H}
    (hi : E.index = 2) {x a : H} (hx : x ∉ E) (ha : a ∉ E) : x * a⁻¹ ∈ E := by
  obtain ⟨b, hb⟩ := Subgroup.index_eq_two_iff.1 hi
  have hxb : x * b ∈ E := by
    rcases hb x with h | h
    · exact h.1
    · exact absurd h.1 hx
  have hab : a * b ∈ E := by
    rcases hb a with h | h
    · exact h.1
    · exact absurd h.1 ha
  have := E.mul_mem hxb (E.inv_mem hab)
  simpa [mul_assoc] using this

theorem mul_mem_derivedOf_of_not_mem {G : Type} [Group G] {a z : G} (h : IsF5Type a z) {x y : G}
    (hx : x ∈ Gx a) (hy : y ∈ Gx a) (hx' : x ∉ derivedOf (Gx a)) (hy' : y ∉ derivedOf (Gx a)) :
    x * y ∈ derivedOf (Gx a) := by
  obtain ⟨E, hE⟩ := h.cent_a
  have hEcomm : E = _root_.commutator ↥(Gx a) := by
    refine le_antisymm ?_ (commutator_le_of_index_eq_two' hE.index_eq_two)
    intro e he
    have he' : (⟨e, he⟩ : ↥E) ∈ _root_.commutator ↥E := by
      rw [hE.perfect.commutator_eq_top]
      exact Subgroup.mem_top _
    have h1 := Subgroup.mem_map_of_mem E.subtype he'
    rw [_root_.commutator_def, Subgroup.map_commutator, ← MonoidHom.range_eq_map,
      Subgroup.range_subtype] at h1
    rw [_root_.commutator_def]
    exact Subgroup.commutator_mono le_top le_top h1
  have hxE : (⟨x, hx⟩ : ↥(Gx a)) ∉ E := fun hmem =>
    hx' (Subgroup.mem_map.mpr ⟨⟨x, hx⟩, by rw [← hEcomm]; exact hmem, rfl⟩)
  have hyE : (⟨y, hy⟩ : ↥(Gx a)) ∉ E := fun hmem =>
    hy' (Subgroup.mem_map.mpr ⟨⟨y, hy⟩, by rw [← hEcomm]; exact hmem, rfl⟩)
  have hyinvE : (⟨y, hy⟩ : ↥(Gx a))⁻¹ ∉ E := fun hmem => hyE (inv_mem_iff.mp hmem)
  have hprodE : (⟨x, hx⟩ : ↥(Gx a)) * (⟨y, hy⟩ : ↥(Gx a)) ∈ E := by
    simpa using mul_inv_mem_of_index_eq_two' hE.index_eq_two hxE hyinvE
  rw [derivedOf]
  refine Subgroup.mem_map.mpr ⟨(⟨x, hx⟩ : ↥(Gx a)) * ⟨y, hy⟩, ?_, rfl⟩
  rw [← hEcomm]
  exact hprodE

end CFSG.EvenSporadicStandard.HNRecog.Section3

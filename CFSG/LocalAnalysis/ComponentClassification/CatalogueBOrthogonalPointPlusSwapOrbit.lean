module

public import Mathlib.Data.Set.Card
public import Mathlib.GroupTheory.GroupAction.Defs

public section

namespace CFSG.ComponentClassification.CatalogueBOrthogonalPointPlusSwap

universe u v

variable {A : Type u} {T : Type v} [Group A] [MulAction A T] {x y z : T}

theorem ne_of_smul_swap_left {κ : A} (hx : κ • x = x) (hy : κ • y = z) (hyz : y ≠ z) :
    x ≠ y := by
  rintro rfl
  exact hyz (hx.symm.trans hy)

theorem ne_of_smul_swap_right {κ : A} (hx : κ • x = x) (hz : κ • z = y) (hyz : y ≠ z) :
    x ≠ z := by
  rintro rfl
  exact hyz (hz.symm.trans hx)

theorem orbit_eq_singleton_or_eq_triple (hO : MulAction.orbit A x ⊆ {x, y, z}) {κ : A}
    (hy : κ • y = z) (hz : κ • z = y) :
    MulAction.orbit A x = {x} ∨ MulAction.orbit A x = {x, y, z} := by
  by_cases hyO : y ∈ MulAction.orbit A x
  · right
    obtain ⟨g, hg⟩ := MulAction.mem_orbit_iff.mp hyO
    have hzO : z ∈ MulAction.orbit A x :=
      MulAction.mem_orbit_iff.mpr ⟨κ * g, by rw [mul_smul, hg, hy]⟩
    refine Set.Subset.antisymm hO ?_
    rintro w (rfl | rfl | rfl)
    · exact MulAction.mem_orbit_self _
    · exact hyO
    · exact hzO
  · left
    have hzO : z ∉ MulAction.orbit A x := by
      intro hzO
      obtain ⟨g, hg⟩ := MulAction.mem_orbit_iff.mp hzO
      exact hyO (MulAction.mem_orbit_iff.mpr ⟨κ * g, by rw [mul_smul, hg, hz]⟩)
    refine Set.Subset.antisymm (fun w hw => ?_)
      (Set.singleton_subset_iff.mpr (MulAction.mem_orbit_self _))
    rcases hO hw with h | h | h
    · exact h
    · exact absurd (h ▸ hw) hyO
    · exact absurd (h ▸ hw) hzO

theorem orbit_ncard_eq_one_or_three (hO : MulAction.orbit A x ⊆ {x, y, z}) {κ : A}
    (hx : κ • x = x) (hy : κ • y = z) (hz : κ • z = y) (hyz : y ≠ z) :
    (MulAction.orbit A x).ncard = 1 ∨ (MulAction.orbit A x).ncard = 3 := by
  rcases orbit_eq_singleton_or_eq_triple hO hy hz with h | h
  · exact Or.inl (by rw [h, Set.ncard_singleton])
  · refine Or.inr (Set.ncard_eq_three.mpr ⟨x, y, z, ?_, ?_, hyz, h⟩)
    · exact ne_of_smul_swap_left hx hy hyz
    · exact ne_of_smul_swap_right hx hz hyz

theorem orbit_card_eq_one_or_three (hO : MulAction.orbit A x ⊆ {x, y, z}) {κ : A}
    (hx : κ • x = x) (hy : κ • y = z) (hz : κ • z = y) (hyz : y ≠ z) :
    Nat.card (MulAction.orbit A x) = 1 ∨ Nat.card (MulAction.orbit A x) = 3 := by
  rw [Nat.card_coe_set_eq]
  exact orbit_ncard_eq_one_or_three hO hx hy hz hyz

theorem conj_smul_eq_self_of_smul_eq {α β : A} {w : T} (hβ : β • x = w) (hα : α • w = w) :
    (β⁻¹ * α * β) • x = x := by
  rw [mul_smul, mul_smul, hβ, hα, ← hβ, inv_smul_smul]

theorem smul_eq_self_of_involution {α : A} (hα : α * α = 1) {u w : T} (hu : α • x = u)
    (hw : α • w = x ∨ α • w = u ∨ α • w = w) (hwu : w ≠ u) (hwx : w ≠ x) : α • w = w := by
  rcases hw with h | h | h
  · refine absurd ?_ hwu
    calc w = (α * α) • w := by rw [hα, one_smul]
      _ = u := by rw [mul_smul, h, hu]
  · exact absurd (smul_left_cancel α (h.trans hu.symm)) hwx
  · exact h

theorem exists_conj_smul_eq_self_of_orbit_swap (hO : MulAction.orbit A x ⊆ {x, y, z}) {κ : A}
    (hx : κ • x = x) (hy : κ • y = z) (hz : κ • z = y) (hyz : y ≠ z) (α : A)
    (hα : α * α = 1) : ∃ β : A, (β⁻¹ * α * β) • x = x := by
  by_cases h0 : α • x = x
  · exact ⟨1, by rw [inv_one, one_mul, mul_one, h0]⟩
  rcases hO (MulAction.mem_orbit x α) with h | h | h
  · exact absurd h h0
  · have hzO : α • z ∈ MulAction.orbit A x :=
      MulAction.mem_orbit_iff.mpr ⟨α * (κ * α), by rw [mul_smul, mul_smul, h, hy]⟩
    refine ⟨κ * α, conj_smul_eq_self_of_smul_eq (by rw [mul_smul, h, hy]) ?_⟩
    exact smul_eq_self_of_involution hα h (hO hzO) hyz.symm
      (ne_of_smul_swap_right hx hz hyz).symm
  · have hyO : α • y ∈ MulAction.orbit A x :=
      MulAction.mem_orbit_iff.mpr ⟨α * (κ * α), by rw [mul_smul, mul_smul, h, hz]⟩
    refine ⟨κ * α, conj_smul_eq_self_of_smul_eq (by rw [mul_smul, h, hz]) ?_⟩
    exact smul_eq_self_of_involution hα h ((hO hyO).imp_right Or.symm) hyz
      (ne_of_smul_swap_left hx hy hyz).symm

end CFSG.ComponentClassification.CatalogueBOrthogonalPointPlusSwap

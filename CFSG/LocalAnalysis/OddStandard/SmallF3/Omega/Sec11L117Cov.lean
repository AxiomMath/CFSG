module

public import Mathlib.Algebra.Group.Subgroup.Pointwise
public import Mathlib.Tactic.Group

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup

variable {G : Type} [Group G]

theorem sec11_cover_T {T C Q W : Subgroup G} {a x : G}
    (hgen : T = Subgroup.closure ((C : Set G) ∪ (Q : Set G) ∪ ({a, x} : Set G)))
    (hCW : C ≤ W) (hQW : Q ≤ W) (hWn : ∀ g ∈ T, ∀ w ∈ W, g * w * g⁻¹ ∈ W)
    (ha2 : a * a = 1) (hx2 : x * x = 1) (hax : a * x * a⁻¹ * x⁻¹ ∈ W) :
    ∀ g ∈ T, g ∈ W ∨ ∃ w ∈ W, g = a * w ∨ g = x * w ∨ g = a * x * w := by
  let good : G → Prop := fun g => g ∈ W ∨ ∃ w ∈ W, g = a * w ∨ g = x * w ∨ g = a * x * w
  have hgood : ∀ g, good g ↔ g ∈ W ∨ ∃ w ∈ W, g = a * w ∨ g = x * w ∨ g = a * x * w :=
    fun g => Iff.rfl
  have ha_inv : a⁻¹ = a := inv_eq_of_mul_eq_one_right ha2
  have hx_inv : x⁻¹ = x := inv_eq_of_mul_eq_one_right hx2
  have haT : a ∈ T := by rw [hgen]; exact Subgroup.subset_closure (by simp)
  have hxT : x ∈ T := by rw [hgen]; exact Subgroup.subset_closure (by simp)
  have haxT : a * x ∈ T := T.mul_mem haT hxT
  have hconj_a : ∀ w ∈ W, a⁻¹ * w * a ∈ W := fun w hw => by
    simpa only [inv_inv] using hWn a⁻¹ (T.inv_mem haT) w hw
  have hconj_x : ∀ w ∈ W, x⁻¹ * w * x ∈ W := fun w hw => by
    simpa only [inv_inv] using hWn x⁻¹ (T.inv_mem hxT) w hw
  have hconj_ax : ∀ w ∈ W, (a * x)⁻¹ * w * (a * x) ∈ W := fun w hw => by
    simpa only [inv_inv] using hWn (a * x)⁻¹ (T.inv_mem haxT) w hw
  have hw0 : (a * x)⁻¹ * (x * a) ∈ W := by
    have h : (a * x)⁻¹ * (x * a) = (a * x * a⁻¹ * x⁻¹)⁻¹ := by
      simp only [mul_inv_rev, inv_inv, ha_inv, hx_inv]
      group
    rw [h]
    exact W.inv_mem hax
  have hL1 : ∀ s ∈ W, ∀ y, good y → good (s * y) := by
    intro s hs y hy
    rw [hgood y] at hy
    rcases hy with hyW | ⟨w, hw, hrep⟩
    · exact Or.inl (W.mul_mem hs hyW)
    · rcases hrep with h | h | h
      · refine Or.inr ⟨a⁻¹ * s * a * w, W.mul_mem (hconj_a s hs) hw, Or.inl ?_⟩
        rw [h]
        group
      · refine Or.inr ⟨x⁻¹ * s * x * w, W.mul_mem (hconj_x s hs) hw,
          Or.inr (Or.inl ?_)⟩
        rw [h]
        group
      · refine Or.inr ⟨(a * x)⁻¹ * s * (a * x) * w,
          W.mul_mem (hconj_ax s hs) hw, Or.inr (Or.inr ?_)⟩
        rw [h]
        group
  have hL2 : ∀ y, good y → good (a * y) := by
    intro y hy
    rw [hgood y] at hy
    rcases hy with hyW | ⟨w, hw, hrep⟩
    · exact Or.inr ⟨y, hyW, Or.inl rfl⟩
    · rcases hrep with h | h | h
      · exact Or.inl (by rw [h, ← mul_assoc, ha2, one_mul]; exact hw)
      · refine Or.inr ⟨w, hw, Or.inr (Or.inr ?_)⟩
        rw [h]
        group
      · refine Or.inr ⟨w, hw, Or.inr (Or.inl ?_)⟩
        rw [h, ← mul_assoc, ← mul_assoc, ha2, one_mul]
  have hL3 : ∀ y, good y → good (x * y) := by
    intro y hy
    rw [hgood y] at hy
    rcases hy with hyW | ⟨w, hw, hrep⟩
    · exact Or.inr ⟨y, hyW, Or.inr (Or.inl rfl)⟩
    · rcases hrep with h | h | h
      · refine Or.inr ⟨(a * x)⁻¹ * (x * a) * w, W.mul_mem hw0 hw,
          Or.inr (Or.inr ?_)⟩
        rw [h]
        group
      · exact Or.inl (by rw [h, ← mul_assoc, hx2, one_mul]; exact hw)
      · have hxw : x * ((a * x)⁻¹ * (x * a)) * x ∈ W := by
          simpa only [hx_inv] using hWn x hxT ((a * x)⁻¹ * (x * a)) hw0
        refine Or.inr ⟨x * ((a * x)⁻¹ * (x * a)) * x * w, W.mul_mem hxw hw,
          Or.inl ?_⟩
        rw [h]
        group
  have hmain :
      ∀ g ∈ Subgroup.closure ((C : Set G) ∪ (Q : Set G) ∪ ({a, x} : Set G)), good g := by
    intro g hg
    refine Subgroup.closure_induction_left (p := fun g _ => good g) ?_ ?_ ?_ hg
    · exact Or.inl W.one_mem
    · intro s hs y _ hygood
      simp only [Set.mem_union, Set.mem_insert_iff, Set.mem_singleton_iff] at hs
      rcases hs with (hsC | hsQ) | (rfl | rfl)
      · exact hL1 s (hCW hsC) y hygood
      · exact hL1 s (hQW hsQ) y hygood
      · exact hL2 y hygood
      · exact hL3 y hygood
    · intro s hs y _ hygood
      simp only [Set.mem_union, Set.mem_insert_iff, Set.mem_singleton_iff] at hs
      rcases hs with (hsC | hsQ) | (rfl | rfl)
      · exact hL1 s⁻¹ (W.inv_mem (hCW hsC)) y hygood
      · exact hL1 s⁻¹ (W.inv_mem (hQW hsQ)) y hygood
      · simpa only [ha_inv] using hL2 y hygood
      · simpa only [hx_inv] using hL3 y hygood
  intro g hg
  rw [hgen] at hg
  exact hmain g hg

end CFSG.OddStandard.SmallF3.Omega

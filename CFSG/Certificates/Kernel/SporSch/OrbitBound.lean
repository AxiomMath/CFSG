module

public import Mathlib.Algebra.Group.Subgroup.Lattice
public import Mathlib.SetTheory.Cardinal.Finite

public section

namespace CFSG.KS.OrbitBound

open Equiv

variable {α : Type*} [Finite α]

theorem ai (g : Perm α) (y : α) : g (g⁻¹ y) = y := by simp

theorem ia (g : Perm α) (y : α) : g⁻¹ (g y) = y := by simp

theorem card_le_orbit (K L : Subgroup (Perm α)) (b : α) (A : Finset α)
    (hL : ∀ g, g ∈ L ↔ g ∈ K ∧ g b = b) (hA : ∀ g ∈ K, g b ∈ A) :
    Nat.card K ≤ A.card * Nat.card L := by
  classical
  have hex : ∀ g : K, ∃ h : K, (h : Perm α) b = (g : Perm α) b := fun g => ⟨g, rfl⟩
  let r : α → Perm α := fun a => if hx : ∃ h : K, (h : Perm α) b = a then hx.choose else 1
  have hr : ∀ g : K, r ((g : Perm α) b) ∈ K ∧ r ((g : Perm α) b) b = (g : Perm α) b := by
    intro g
    have hx : ∃ h : K, (h : Perm α) b = (g : Perm α) b := hex g
    simp only [r, dif_pos hx]
    exact ⟨hx.choose.2, hx.choose_spec⟩
  let f : K → A × L := fun g => (⟨(g : Perm α) b, hA g g.2⟩,
    ⟨(r ((g : Perm α) b))⁻¹ * g, (hL _).2 ⟨K.mul_mem (K.inv_mem (hr g).1) g.2, by
      rw [Perm.mul_apply, Perm.inv_eq_iff_eq, (hr g).2]⟩⟩)
  have hf : Function.Injective f := by
    intro g g' e
    simp only [f, Prod.mk.injEq, Subtype.mk.injEq] at e
    obtain ⟨e1, e2⟩ := e
    rw [e1] at e2
    exact Subtype.ext (mul_left_cancel e2)
  have h := Nat.card_le_card_of_injective f hf
  rwa [Nat.card_prod, Nat.card_eq_finsetCard] at h

theorem card_le_chain {a c : ℕ → ℕ} {n : ℕ} (h : ∀ j < n, a j ≤ c j * a (j + 1)) :
    a 0 ≤ (∏ j ∈ Finset.range n, c j) * a n := by
  have key : ∀ m ≤ n, a 0 ≤ (∏ j ∈ Finset.range m, c j) * a m := by
    intro m
    induction m with
    | zero => intro _; simp
    | succ m ih =>
      intro hm
      rw [Finset.prod_range_succ, mul_assoc]
      exact (ih (by omega)).trans (Nat.mul_le_mul_left _ (h m (by omega)))
  exact key n le_rfl

theorem iff_of_maps (O : Finset α) {g : Perm α} (hg : ∀ y ∈ O, g y ∈ O) (y : α) :
    g y ∈ O ↔ y ∈ O := by
  classical
  refine ⟨fun hy => ?_, hg y⟩
  have hsub : O.image g ⊆ O := fun z hz => by
    obtain ⟨y', hy', rfl⟩ := Finset.mem_image.1 hz
    exact hg y' hy'
  have he : O.image g = O := Finset.eq_of_subset_of_card_le hsub
    (by rw [Finset.card_image_of_injective _ g.injective])
  rw [← he] at hy
  obtain ⟨y', hy', e⟩ := Finset.mem_image.1 hy
  rwa [← g.injective e]

theorem iff_of_closed (O : Finset α) (X : Set (Perm α)) (hX : ∀ g ∈ X, ∀ y ∈ O, g y ∈ O) :
    ∀ g ∈ Subgroup.closure X, ∀ y, g y ∈ O ↔ y ∈ O := by
  intro g hg
  induction hg using Subgroup.closure_induction with
  | mem g hg => exact iff_of_maps O (hX g hg)
  | one => intro y; rfl
  | mul g g' _ _ ih ih' =>
    intro y
    rw [Perm.mul_apply, ih, ih']
  | inv g _ ih =>
    intro y
    rw [← ih (g⁻¹ y), ai]

theorem card_filter_conj [DecidableEq α] (F O : Finset α) {h s : Perm α}
    (hF : ∀ y, h y ∈ F ↔ y ∈ F) (hO : ∀ y, s y ∈ O ↔ y ∈ O) :
    (F.filter fun y => (h * s⁻¹)⁻¹ y ∈ O).card = (F.filter fun y => y ∈ O).card := by
  have e1 : ∀ y, (h * s⁻¹)⁻¹ y ∈ O ↔ h⁻¹ y ∈ O := fun y => by
    rw [mul_inv_rev, inv_inv, Perm.mul_apply, hO]
  have himg : (F.filter fun y => h⁻¹ y ∈ O).image (⇑(h⁻¹ : Perm α)) =
      F.filter fun y => y ∈ O := by
    ext z
    simp only [Finset.mem_image, Finset.mem_filter]
    constructor
    · rintro ⟨y, ⟨hy, hyO⟩, rfl⟩
      refine ⟨?_, hyO⟩
      rw [← hF, ai]
      exact hy
    · rintro ⟨hz, hzO⟩
      refine ⟨h z, ⟨(hF z).2 hz, by rwa [ia]⟩, ia h z⟩
  rw [← himg, Finset.card_image_of_injective _ (Equiv.injective h⁻¹)]
  congr 1
  ext y
  simp only [Finset.mem_filter, e1]

end CFSG.KS.OrbitBound

end

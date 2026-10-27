module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y6Q8a
public import Mathlib.GroupTheory.Commutator.Basic

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

open Subgroup
open scoped commutatorElement

variable {G : Type} [Group G] {a₁ b₁ a₂ b₂ z : G}

private lemma sq_z (h : Y6ARel a₁ b₁ a₂ b₂ z) : z * z = 1 := by
  simpa [pow_two] using h.z_sq

private lemma commute_pair
    (hz : ∀ a ∈ (closure {a₁, b₁, a₂, b₂} : Subgroup G), a * z = z * a)
    {x : G} (hx : x ∈ (closure {a₁, b₁, a₂, b₂} : Subgroup G)) {c : G}
    (hc : c = 1 ∨ c = z) : Commute c x := by
  rcases hc with rfl | rfl
  · exact Commute.one_left x
  · exact (hz x hx).symm

private lemma mem_pair_mul {z : G} (hzz : z * z = 1) {c d : G} (hc : c = 1 ∨ c = z)
    (hd : d = 1 ∨ d = z) : c * d = 1 ∨ c * d = z := by
  rcases hc with rfl | rfl <;> rcases hd with rfl | rfl <;> simp [hzz]

private lemma conj_mem_pair
    (hz : ∀ a ∈ (closure {a₁, b₁, a₂, b₂} : Subgroup G), a * z = z * a)
    {x : G} (hx : x ∈ (closure {a₁, b₁, a₂, b₂} : Subgroup G)) {c : G}
    (hc : c = 1 ∨ c = z) : x * c * x⁻¹ = 1 ∨ x * c * x⁻¹ = z := by
  rcases hc with rfl | rfl
  · left; group
  · right; rw [hz x hx]; group

private lemma inv_mem_pair {z c : G} (hzz : z * z = 1) (hc : c = 1 ∨ c = z) :
    c⁻¹ = 1 ∨ c⁻¹ = z := by
  rcases hc with rfl | rfl
  · left; simp
  · right; rw [inv_eq_iff_mul_eq_one]; exact hzz

private lemma comm_gen_z (h : Y6ARel a₁ b₁ a₂ b₂ z) :
    ∀ x ∈ ({a₁, b₁, a₂, b₂} : Set G), ∀ y ∈ ({a₁, b₁, a₂, b₂} : Set G),
      ⁅x, y⁆ = 1 ∨ ⁅x, y⁆ = z := by
  have hzi : z⁻¹ = z := inv_eq_of_mul_eq_one_right (sq_z h)
  intro x hx y hy
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx hy
  rcases hx with rfl | rfl | rfl | rfl <;> rcases hy with rfl | rfl | rfl | rfl <;>
    first
      | exact Or.inl (by simp)
      | exact Or.inr h.comm1
      | exact Or.inr h.comm2
      | exact Or.inl h.a1a2
      | exact Or.inl h.a1b2
      | exact Or.inl h.b1a2
      | exact Or.inl h.b1b2
      | exact Or.inr (by rw [← commutatorElement_inv, h.comm1, hzi])
      | exact Or.inr (by rw [← commutatorElement_inv, h.comm2, hzi])
      | exact Or.inl (by rw [← commutatorElement_inv, h.a1a2, inv_one])
      | exact Or.inl (by rw [← commutatorElement_inv, h.a1b2, inv_one])
      | exact Or.inl (by rw [← commutatorElement_inv, h.b1a2, inv_one])
      | exact Or.inl (by rw [← commutatorElement_inv, h.b1b2, inv_one])

private lemma comm_mem_fixed (h : Y6ARel a₁ b₁ a₂ b₂ z)
    (hz : ∀ a ∈ (closure {a₁, b₁, a₂, b₂} : Subgroup G), a * z = z * a)
    {a : G} (ha : a ∈ (closure {a₁, b₁, a₂, b₂} : Subgroup G))
    (hagen : ∀ y ∈ ({a₁, b₁, a₂, b₂} : Set G), ⁅a, y⁆ = 1 ∨ ⁅a, y⁆ = z) :
    ∀ b ∈ (closure {a₁, b₁, a₂, b₂} : Subgroup G), ⁅a, b⁆ = 1 ∨ ⁅a, b⁆ = z := by
  intro b hb
  refine Subgroup.closure_induction ?_ ?_ ?_ ?_ hb
  · intro y hy
    exact hagen y hy
  · exact Or.inl (commutatorElement_one_right a)
  · intro y y' hy _ ih1 ih2
    rw [commutatorElement_mul_right_eq_mul_conj]
    have hmem := mem_pair_mul (sq_z h) ih1 (conj_mem_pair hz hy ih2)
    simpa only [mul_assoc] using hmem
  · intro y hy ih
    rw [commutatorElement_inv_right, ← commutatorElement_inv]
    simpa using conj_mem_pair hz (inv_mem hy) (inv_mem_pair (sq_z h) ih)

theorem y6q8_comm_mem (h : Y6ARel a₁ b₁ a₂ b₂ z) :
    ∀ a ∈ (closure {a₁, b₁, a₂, b₂} : Subgroup G), ∀ b ∈ (closure {a₁, b₁, a₂, b₂} : Subgroup G),
      ⁅a, b⁆ = 1 ∨ ⁅a, b⁆ = z := by
  have hz := y6q8_z_central h
  intro a ha
  refine Subgroup.closure_induction ?_ ?_ ?_ ?_ ha
  · intro x hx
    exact comm_mem_fixed h hz (subset_closure hx) (fun y hy => comm_gen_z h x hx y hy)
  · intro b _
    exact Or.inl (commutatorElement_one_left b)
  · intro x y hx hy ihx ihy b hb
    rw [commutatorElement_mul_left_eq_conj_mul]
    exact mem_pair_mul (sq_z h) (conj_mem_pair hz hx (ihy b hb)) (ihx b hb)
  · intro x hx ih b hb
    rw [commutatorElement_inv_left, ← commutatorElement_inv]
    simpa using conj_mem_pair hz (inv_mem hx) (inv_mem_pair (sq_z h) (ih b hb))

theorem y6q8_sq_mul (h : Y6ARel a₁ b₁ a₂ b₂ z) :
    ∀ a ∈ (closure {a₁, b₁, a₂, b₂} : Subgroup G), ∀ b ∈ (closure {a₁, b₁, a₂, b₂} : Subgroup G),
      (a * b) ^ 2 = a ^ 2 * b ^ 2 * ⁅b, a⁆ := by
  have hz := y6q8_z_central h
  intro a ha b hb
  have hc : ⁅b, a⁆ = 1 ∨ ⁅b, a⁆ = z := y6q8_comm_mem h b hb a ha
  have hca : Commute ⁅b, a⁆ a := commute_pair hz ha hc
  have hcb : Commute ⁅b, a⁆ b := commute_pair hz hb hc
  have hcbb : Commute ⁅b, a⁆ (b * b) := hcb.mul_right hcb
  have hba : b * a = ⁅b, a⁆ * a * b := by simp only [commutatorElement_def]; group
  calc (a * b) ^ 2 = a * (b * a) * b := by rw [pow_two]; group
    _ = a * (⁅b, a⁆ * a * b) * b := by rw [hba]
    _ = a * a * (⁅b, a⁆ * (b * b)) := by rw [hca.eq]; group
    _ = a * a * ((b * b) * ⁅b, a⁆) := by rw [hcbb.eq]
    _ = a ^ 2 * b ^ 2 * ⁅b, a⁆ := by rw [pow_two, pow_two, ← mul_assoc]

private lemma commute_closure_of_gens {x : G} (hxa : ⁅x, a₂⁆ = 1) (hxb : ⁅x, b₂⁆ = 1) :
    ∀ w ∈ (closure {a₂, b₂} : Subgroup G), x * w = w * x := by
  intro w hw
  refine Subgroup.closure_induction ?_ ?_ ?_ ?_ hw
  · intro y hy
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
    rcases hy with rfl | rfl
    · exact commutatorElement_eq_one_iff_mul_comm.mp hxa
    · exact commutatorElement_eq_one_iff_mul_comm.mp hxb
  · simp
  · intro y y' _ _ ih1 ih2
    exact (Commute.mul_right ih1 ih2).eq
  · intro y _ ih
    exact (Commute.inv_right ih).eq

private lemma commute_UW (h : Y6ARel a₁ b₁ a₂ b₂ z) :
    ∀ u ∈ (closure {a₁, b₁} : Subgroup G), ∀ w ∈ (closure {a₂, b₂} : Subgroup G),
      u * w = w * u := by
  intro u hu
  refine Subgroup.closure_induction ?_ ?_ ?_ ?_ hu
  · intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl
    · exact commute_closure_of_gens h.a1a2 h.a1b2
    · exact commute_closure_of_gens h.b1a2 h.b1b2
  · intro w _; simp
  · intro x y _ _ ihx ihy w hw
    rw [mul_assoc, ihy w hw, ← mul_assoc, ihx w hw, mul_assoc]
  · intro x _ ih w hw
    calc x⁻¹ * w = x⁻¹ * (w * x) * x⁻¹ := by group
      _ = x⁻¹ * (x * w) * x⁻¹ := by rw [← ih w hw]
      _ = w * x⁻¹ := by group

theorem y6q8_A_elems (h : Y6ARel a₁ b₁ a₂ b₂ z) :
    ∀ a ∈ (closure {a₁, b₁, a₂, b₂} : Subgroup G),
      ∃ u ∈ (closure {a₁, b₁} : Subgroup G), ∃ w ∈ (closure {a₂, b₂} : Subgroup G), a = u * w := by
  intro a ha
  refine Subgroup.closure_induction ?_ ?_ ?_ ?_ ha
  · intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with hx | hx | hx | hx
    · rw [hx]; exact ⟨a₁, subset_closure (by simp), 1, one_mem _, by simp⟩
    · rw [hx]; exact ⟨b₁, subset_closure (by simp), 1, one_mem _, by simp⟩
    · rw [hx]; exact ⟨1, one_mem _, a₂, subset_closure (by simp), by simp⟩
    · rw [hx]; exact ⟨1, one_mem _, b₂, subset_closure (by simp), by simp⟩
  · exact ⟨1, one_mem _, 1, one_mem _, by simp⟩
  · intro x y _ _ hx hy
    obtain ⟨u, hu, w, hw, rfl⟩ := hx
    obtain ⟨u', hu', w', hw', rfl⟩ := hy
    refine ⟨u * u', mul_mem hu hu', w * w', mul_mem hw hw', ?_⟩
    calc (u * w) * (u' * w') = u * (w * u') * w' := by group
      _ = u * (u' * w) * w' := by rw [(commute_UW h u' hu' w hw).symm]
      _ = (u * u') * (w * w') := by group
  · intro x _ hx
    obtain ⟨u, hu, w, hw, rfl⟩ := hx
    refine ⟨u⁻¹, inv_mem hu, w⁻¹, inv_mem hw, ?_⟩
    rw [mul_inv_rev]
    exact (commute_UW h u⁻¹ (inv_mem hu) w⁻¹ (inv_mem hw)).symm

end CFSG.OddStandard.HigherRank.YamadaG23

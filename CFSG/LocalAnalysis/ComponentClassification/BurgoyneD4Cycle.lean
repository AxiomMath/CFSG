module

public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointPlusSwapOrbit
public import Mathlib.GroupTheory.OrderOfElement

public section

namespace CFSG.ComponentClassification.Burgoyne.D4

open CFSG.ComponentClassification.CatalogueBOrthogonalPointPlusSwap
open scoped Pointwise

section Action

variable {A T : Type*} [Group A] [MulAction A T] {x y z : T}

theorem pow_odd_smul_of_sq_smul {α : A} {w : T} (h : (α * α) • w = w) (k : ℕ) :
    α ^ (2 * k + 1) • w = α • w := by
  induction k with
  | zero => simp
  | succ k ih =>
    have e : α ^ (2 * (k + 1) + 1) = α ^ (2 * k + 1) * (α * α) := by
      rw [show 2 * (k + 1) + 1 = (2 * k + 1) + 2 from by omega, pow_add, pow_two]
    rw [e, mul_smul, h, ih]

theorem smul_eq_of_odd_of_sq {α : A} (hα : Odd (orderOf α)) {w : T} (h : (α * α) • w = w) :
    α • w = w := by
  obtain ⟨k, hk⟩ := hα
  have h1 := pow_odd_smul_of_sq_smul h k
  rw [← hk, pow_orderOf_eq_one, one_smul] at h1
  exact h1.symm

theorem smul_mem_orbit {α : A} {w : T} (hw : w ∈ MulAction.orbit A x) :
    α • w ∈ MulAction.orbit A x := by
  obtain ⟨g, rfl⟩ := MulAction.mem_orbit_iff.mp hw
  exact MulAction.mem_orbit_iff.mpr ⟨α * g, mul_smul _ _ _⟩

theorem cycle_of_smul_eq {α : A} (hα : Odd (orderOf α)) (hxy : x ≠ y) (hxz : x ≠ z)
    (hyz : y ≠ z) (hmem : ∀ w, w = x ∨ w = y ∨ w = z → α • w = x ∨ α • w = y ∨ α • w = z)
    (h1 : α • x = y) : α • y = z ∧ α • z = x := by
  have hy : α • y ≠ y := fun h => hxy (smul_left_cancel α (h1.trans h.symm))
  have hyz' : α • y = z := by
    rcases hmem y (Or.inr (Or.inl rfl)) with h | h | h
    ·
      have hsq : (α * α) • x = x := by rw [mul_smul, h1, h]
      exact absurd (smul_eq_of_odd_of_sq hα hsq) (by rw [h1]; exact hxy.symm)
    · exact absurd h hy
    · exact h
  refine ⟨hyz', ?_⟩
  rcases hmem z (Or.inr (Or.inr rfl)) with h | h | h
  · exact h
  · exact absurd (smul_left_cancel α (h.trans h1.symm)) hxz.symm
  · exact absurd (smul_left_cancel α (h.trans hyz'.symm)) hyz.symm

theorem cycle_of_odd (hO : MulAction.orbit A x ⊆ {x, y, z}) {κ : A} (hx : κ • x = x)
    (hy : κ • y = z) (hz : κ • z = y) (hyz : y ≠ z) {α : A} (hα : Odd (orderOf α))
    (hαx : α • x ≠ x) :
    (α • x = y ∧ α • y = z ∧ α • z = x) ∨ (α • x = z ∧ α • z = y ∧ α • y = x) := by
  have hxy := ne_of_smul_swap_left hx hy hyz
  have hxz := ne_of_smul_swap_right hx hz hyz
  have hαxO : α • x ∈ MulAction.orbit A x := MulAction.mem_orbit x α
  have hO' : MulAction.orbit A x = {x, y, z} := by
    rcases orbit_eq_singleton_or_eq_triple hO hy hz with h | h
    · rw [h] at hαxO
      exact absurd hαxO hαx
    · exact h
  have hmem : ∀ w, w = x ∨ w = y ∨ w = z → α • w = x ∨ α • w = y ∨ α • w = z := by
    intro w hw
    have hwO : w ∈ MulAction.orbit A x := by rw [hO']; exact hw
    have h := smul_mem_orbit (α := α) hwO
    rw [hO'] at h
    exact h
  rcases hmem x (Or.inl rfl) with h | h | h
  · exact absurd h hαx
  · exact Or.inl ⟨h, cycle_of_smul_eq hα hxy hxz hyz hmem h⟩
  · have hmem' : ∀ w, w = x ∨ w = z ∨ w = y → α • w = x ∨ α • w = z ∨ α • w = y := by
      intro w hw
      have h' := hmem w (hw.imp_right Or.symm)
      exact h'.imp_right Or.symm
    exact Or.inr ⟨h, cycle_of_smul_eq hα hxz hxy hyz.symm hmem' h⟩

end Action

section Family

variable {G : Type*} [Group G]

@[expose] def IsCycle3 (α : MulAut G) (F₁ F₂ F₃ : Set (Subgroup G)) : Prop :=
  (α • F₁ = F₂ ∧ α • F₂ = F₃ ∧ α • F₃ = F₁) ∨ (α • F₁ = F₃ ∧ α • F₃ = F₂ ∧ α • F₂ = F₁)

theorem map_mem_smul {α : MulAut G} {F : Set (Subgroup G)} {M : Subgroup G} (hM : M ∈ F) :
    M.map α.toMonoidHom ∈ α • F :=
  ⟨M, hM, rfl⟩

theorem exists_smul_of_cycle {α : MulAut G} {F₁ F₂ F₃ : Set (Subgroup G)}
    (hc : IsCycle3 α F₁ F₂ F₃) :
    ((α • F₁ = F₂ ∨ (α * α) • F₁ = F₂) ∧ (α • F₁ = F₃ ∨ (α * α) • F₁ = F₃)) := by
  rcases hc with ⟨h1, h2, -⟩ | ⟨h1, h2, -⟩
  · exact ⟨Or.inl h1, Or.inr (by rw [mul_smul, h1, h2])⟩
  · exact ⟨Or.inr (by rw [mul_smul, h1, h2]), Or.inl h1⟩

theorem map_eq_of_fix {β : MulAut G} {H : Subgroup G} (hH : ∀ h ∈ H, β h = h) :
    H.map β.toMonoidHom = H := by
  ext x
  constructor
  · rintro ⟨h, hh, rfl⟩
    change β h ∈ H
    rw [hH h hh]
    exact hh
  · intro hx
    exact ⟨x, hx, hH x hx⟩

theorem exists_le_of_smul {β : MulAut G} {F F' : Set (Subgroup G)} (hβ : β • F = F')
    {H : Subgroup G} (hH : ∀ h ∈ H, β h = h) {M : Subgroup G} (hM : M ∈ F) (hHM : H ≤ M) :
    ∃ M' ∈ F', H ≤ M' := by
  refine ⟨M.map β.toMonoidHom, hβ ▸ map_mem_smul hM, ?_⟩
  rw [← map_eq_of_fix hH]
  exact Subgroup.map_mono hHM

theorem exists_le_of_cycle {α : MulAut G} {F₁ F₂ F₃ : Set (Subgroup G)}
    (hc : IsCycle3 α F₁ F₂ F₃) {H : Subgroup G} (hH : ∀ h ∈ H, α h = h) {M : Subgroup G}
    (hM : M ∈ F₁) (hHM : H ≤ M) : (∃ M' ∈ F₂, H ≤ M') ∧ (∃ M' ∈ F₃, H ≤ M') := by
  have hH2 : ∀ h ∈ H, (α * α) h = h := fun h hh => by
    rw [MulAut.mul_apply, hH h hh, hH h hh]
  obtain ⟨h2, h3⟩ := exists_smul_of_cycle hc
  refine ⟨?_, ?_⟩
  · rcases h2 with h | h
    · exact exists_le_of_smul h hH hM hHM
    · exact exists_le_of_smul h hH2 hM hHM
  · rcases h3 with h | h
    · exact exists_le_of_smul h hH hM hHM
    · exact exists_le_of_smul h hH2 hM hHM

theorem exists_map_eq_of_smul {β t : MulAut G} (hβt : t * β = β * t) {F F' : Set (Subgroup G)}
    (hβ : β • F = F') {M : Subgroup G} (hM : M ∈ F) (htM : M.map t.toMonoidHom = M) :
    ∃ M' ∈ F', M'.map t.toMonoidHom = M' := by
  refine ⟨M.map β.toMonoidHom, hβ ▸ map_mem_smul hM, ?_⟩
  rw [Subgroup.map_map]
  have h : t.toMonoidHom.comp β.toMonoidHom = β.toMonoidHom.comp t.toMonoidHom := by
    ext x
    change (t * β) x = (β * t) x
    rw [hβt]
  rw [h, ← Subgroup.map_map, htM]

theorem exists_map_eq_of_cycle {α t : MulAut G} {F₁ F₂ F₃ : Set (Subgroup G)}
    (hc : IsCycle3 α F₁ F₂ F₃) (hαt : t * α = α * t) {M : Subgroup G} (hM : M ∈ F₁)
    (htM : M.map t.toMonoidHom = M) :
    (∃ M' ∈ F₂, M'.map t.toMonoidHom = M') ∧ (∃ M' ∈ F₃, M'.map t.toMonoidHom = M') := by
  have hαt2 : t * (α * α) = (α * α) * t := by
    rw [← mul_assoc, hαt, mul_assoc, hαt, mul_assoc]
  obtain ⟨h2, h3⟩ := exists_smul_of_cycle hc
  refine ⟨?_, ?_⟩
  · rcases h2 with h | h
    · exact exists_map_eq_of_smul hαt h hM htM
    · exact exists_map_eq_of_smul hαt2 h hM htM
  · rcases h3 with h | h
    · exact exists_map_eq_of_smul hαt h hM htM
    · exact exists_map_eq_of_smul hαt2 h hM htM

theorem IsCycle3.rotate {α : MulAut G} {F₁ F₂ F₃ : Set (Subgroup G)}
    (hc : IsCycle3 α F₁ F₂ F₃) : IsCycle3 α F₂ F₃ F₁ := by
  rcases hc with ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩
  · exact Or.inl ⟨h2, h3, h1⟩
  · exact Or.inr ⟨h3, h1, h2⟩

end Family

end CFSG.ComponentClassification.Burgoyne.D4

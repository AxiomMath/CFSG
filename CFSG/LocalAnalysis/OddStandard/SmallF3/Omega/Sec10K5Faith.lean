module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec10K5Theta

public section

namespace CFSG.OddStandard.SmallF3.Omega.K5

theorem k5g_two : k5g 2 = k5g 0 * k5g 1 * (k5g 0)⁻¹ := by decide +kernel

theorem SL23_induction {P : SL23 → Prop} (h1 : P 1) (hmul : ∀ a b, P a → P b → P (a * b))
    (hinv : ∀ a, P a → P a⁻¹) (h0 : P (k5g 0)) (h0' : P (k5g 1)) (s : SL23) : P s := by
  let E : Subgroup SL23 :=
    { carrier := {s | P s}
      mul_mem' := fun {a b} ha hb => hmul a b ha hb
      one_mem' := h1
      inv_mem' := fun {a} ha => hinv a ha }
  have hsub : ({k5g 0, k5g 1} : Set SL23) ⊆ E := by
    intro t ht
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ht
    rcases ht with rfl | rfl
    · exact h0
    · exact h0'
  exact (Subgroup.closure_le E).mpr hsub (closure_k5g s)

theorem fix_of_signs {K : Type} [Group K] (ψ : SL23 →* K) (hψ : Function.Injective ψ)
    (α : MulAut K)
    (h0 : α (ψ (k5g 0)) = ψ (k5g 0) ∨ α (ψ (k5g 0)) = (ψ (k5g 0))⁻¹)
    (h1 : α (ψ (k5g 1)) = ψ (k5g 1) ∨ α (ψ (k5g 1)) = (ψ (k5g 1))⁻¹)
    (h2 : α (ψ (k5g 2)) = ψ (k5g 2) ∨ α (ψ (k5g 2)) = (ψ (k5g 2))⁻¹) (s : SL23) :
    α (ψ s) = ψ s := by
  have sign : ∀ t : SL23, (α (ψ t) = ψ t ∨ α (ψ t) = (ψ t)⁻¹) →
      ∃ x : SL23, (x = t ∨ x = t⁻¹) ∧ α (ψ t) = ψ x := by
    intro t ht
    rcases ht with e | e
    · exact ⟨t, Or.inl rfl, e⟩
    · exact ⟨t⁻¹, Or.inr rfl, by rw [e, map_inv]⟩
  obtain ⟨x, hx, hxψ⟩ := sign _ h0
  obtain ⟨y, hy, hyψ⟩ := sign _ h1
  obtain ⟨z, hz, hzψ⟩ := sign _ h2
  have hxyz : x * y * x⁻¹ = z := by
    apply hψ
    rw [map_mul, map_mul, map_inv, ← hxψ, ← hyψ, ← hzψ, k5g_two]
    simp only [map_mul, map_inv]
  have h2' : x * y * x⁻¹ = k5g 2 ∨ x * y * x⁻¹ = (k5g 2)⁻¹ := by
    rw [hxyz]
    exact hz
  have e4 : ψ ((x * y) ^ 4) = α (ψ ((k5g 0 * k5g 1) ^ 4)) := by
    simp only [map_pow, map_mul, ← hxψ, ← hyψ]
  have h4 : (x * y) ^ 4 = 1 ↔ (k5g 0 * k5g 1) ^ 4 = 1 := by
    constructor
    · intro h
      have h' : α (ψ ((k5g 0 * k5g 1) ^ 4)) = 1 := by rw [← e4, h, map_one]
      have h'' : ψ ((k5g 0 * k5g 1) ^ 4) = 1 := α.injective (by rw [h', map_one])
      exact hψ (by rw [h'', map_one])
    · intro h
      apply hψ
      rw [e4, h, map_one, map_one]
  obtain ⟨hx0, hy1⟩ := faith_k5g hx hy h2' h4
  have f0 : α (ψ (k5g 0)) = ψ (k5g 0) := by rw [hxψ, hx0]
  have f1 : α (ψ (k5g 1)) = ψ (k5g 1) := by rw [hyψ, hy1]
  refine SL23_induction (P := fun s => α (ψ s) = ψ s) ?_ ?_ ?_ f0 f1 s
  · simp
  · intro a b ha hb
    have ha' : α (ψ a) = ψ a := ha
    have hb' : α (ψ b) = ψ b := hb
    show α (ψ (a * b)) = ψ (a * b)
    rw [map_mul, map_mul, ha', hb']
  · intro a ha
    have ha' : α (ψ a) = ψ a := ha
    show α (ψ a⁻¹) = ψ a⁻¹
    rw [map_inv, map_inv, ha']

namespace SL23Pair

variable {K : Type} [Group K] [Finite K] {A B : Subgroup K} (h : SL23Pair K A B)

theorem fix_A {α : MulAut K} (hα : ∀ i, h.theta α (Sum.inl i) = Sum.inl i) {a : K}
    (ha : a ∈ A) : α a = a := by
  obtain ⟨s, rfl⟩ := h.exists_embA ha
  have key : ∀ i, α (h.embA (k5g i)) = h.embA (k5g i) ∨
      α (h.embA (k5g i)) = (h.embA (k5g i))⁻¹ := by
    intro i
    rw [h.embA_k5g]
    have := h.theta_spec α (Sum.inl i)
    rwa [hα i] at this
  exact fix_of_signs h.embA h.embA_injective α (key 0) (key 1) (key 2) s

theorem fix_B {α : MulAut K} (hα : ∀ i, h.theta α (Sum.inr i) = Sum.inr i) {b : K}
    (hb : b ∈ B) : α b = b := by
  obtain ⟨s, rfl⟩ := h.exists_embB hb
  have key : ∀ i, α (h.embB (k5g i)) = h.embB (k5g i) ∨
      α (h.embB (k5g i)) = (h.embB (k5g i))⁻¹ := by
    intro i
    rw [h.embB_k5g]
    have := h.theta_spec α (Sum.inr i)
    rwa [hα i] at this
  exact fix_of_signs h.embB h.embB_injective α (key 0) (key 1) (key 2) s

theorem theta_injective : Function.Injective h.theta := by
  rw [injective_iff_map_eq_one]
  intro α hα
  have hl : ∀ i, h.theta α (Sum.inl i) = Sum.inl i := fun i => by simp [hα]
  have hr : ∀ i, h.theta α (Sum.inr i) = Sum.inr i := fun i => by simp [hα]
  ext k
  obtain ⟨a, ha, b, hb, rfl⟩ := h.exists_mul k
  rw [map_mul, h.fix_A hl ha, h.fix_B hr hb]
  rfl

theorem map_mem_A {α : MulAut K} (h0 : α (h.gen (Sum.inl 0)) ∈ A)
    (h1 : α (h.gen (Sum.inl 1)) ∈ A) {a : K} (ha : a ∈ A) : α a ∈ A := by
  obtain ⟨s, rfl⟩ := h.exists_embA ha
  refine SL23_induction (P := fun s => α (h.embA s) ∈ A) ?_ ?_ ?_ ?_ ?_ s
  · show α (h.embA 1) ∈ A
    rw [map_one, map_one]
    exact one_mem A
  · intro a b ha hb
    have ha' : α (h.embA a) ∈ A := ha
    have hb' : α (h.embA b) ∈ A := hb
    show α (h.embA (a * b)) ∈ A
    rw [map_mul, map_mul]
    exact mul_mem ha' hb'
  · intro a ha
    have ha' : α (h.embA a) ∈ A := ha
    show α (h.embA a⁻¹) ∈ A
    rw [map_inv, map_inv]
    exact inv_mem ha'
  · show α (h.embA (k5g 0)) ∈ A
    rw [h.embA_k5g]
    exact h0
  · show α (h.embA (k5g 1)) ∈ A
    rw [h.embA_k5g]
    exact h1

end SL23Pair

end CFSG.OddStandard.SmallF3.Omega.K5

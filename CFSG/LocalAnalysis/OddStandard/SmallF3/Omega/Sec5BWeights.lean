module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5BA6Comb
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec4Comb

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup

variable {G : Type} [Group G]

@[expose] def IsPerm6 (φ : (Fin 6 → ZMod 2) → G) (A H : Subgroup G) : Prop :=
  IsPermModuleVia (n := 6) (fun _ => True) φ A H (alternatingGroup (Fin 6))

@[expose] def wclass (φ : (Fin 6 → ZMod 2) → G) (k : ℕ) : Set G :=
  φ '' {v | vecWeight v = k}

variable {φ : (Fin 6 → ZMod 2) → G} {A H : Subgroup G}

theorem IsPerm6.map_add (h : IsPerm6 φ A H) (v w : Fin 6 → ZMod 2) : φ (v + w) = φ v * φ w :=
  h.1 v w trivial trivial

theorem IsPerm6.injective (h : IsPerm6 φ A H) : Function.Injective φ :=
  fun v w hvw => h.2.1 v w trivial trivial hvw

theorem IsPerm6.mem_iff (h : IsPerm6 φ A H) (x : G) : x ∈ A ↔ ∃ v, φ v = x := by
  simpa using h.2.2.1 x

theorem IsPerm6.mem (h : IsPerm6 φ A H) (v : Fin 6 → ZMod 2) : φ v ∈ A :=
  (h.mem_iff (φ v)).mpr ⟨v, rfl⟩

theorem IsPerm6.map_zero (h : IsPerm6 φ A H) : φ 0 = 1 := by
  have hmul : φ 0 * φ 0 = φ 0 := by simpa using (h.map_add 0 0).symm
  exact mul_eq_right.mp hmul

theorem IsPerm6.card_A (h : IsPerm6 φ A H) : Nat.card A = 64 := by
  let f : (Fin 6 → ZMod 2) → A := fun v => ⟨φ v, h.mem v⟩
  have hf : Function.Bijective f := by
    constructor
    · intro v w hvw
      exact h.injective (Subtype.ext_iff.mp hvw)
    · rintro ⟨x, hx⟩
      obtain ⟨v, rfl⟩ := (h.mem_iff x).mp hx
      exact ⟨v, rfl⟩
  rw [← Nat.card_congr (Equiv.ofBijective f hf), Nat.card_eq_fintype_card]
  decide

theorem IsPerm6.wclass_subset (h : IsPerm6 φ A H) (k : ℕ) : wclass φ k ⊆ (A : Set G) := by
  rintro x ⟨v, _hv, rfl⟩
  exact h.mem v

theorem IsPerm6.exists_wclass (h : IsPerm6 φ A H) {x : G} (hx : x ∈ A) :
    ∃ k, k ≤ 6 ∧ x ∈ wclass φ k := by
  obtain ⟨v, rfl⟩ := (h.mem_iff x).mp hx
  exact ⟨vecWeight v, sec5b6_weight_le_six v, v, rfl, rfl⟩

theorem IsPerm6.exists_wclass_pos (h : IsPerm6 φ A H) {x : G} (hx : x ∈ A) (hx1 : x ≠ 1) :
    ∃ k, 1 ≤ k ∧ k ≤ 6 ∧ x ∈ wclass φ k := by
  obtain ⟨v, rfl⟩ := (h.mem_iff x).mp hx
  have hv0 : v ≠ 0 := by
    intro hv
    exact hx1 (by rw [hv, h.map_zero])
  have hpos : 1 ≤ vecWeight v := by
    rcases Nat.eq_zero_or_pos (vecWeight v) with h0 | hp
    · exact absurd (eq_zero_of_vecWeight_eq_zero h0) hv0
    · exact hp
  exact ⟨vecWeight v, hpos, sec5b6_weight_le_six v, v, rfl, rfl⟩

theorem IsPerm6.ncard_wclass (h : IsPerm6 φ A H) (k : ℕ) :
    (wclass φ k).ncard = Nat.choose 6 k := by
  rw [wclass, Set.ncard_image_of_injective _ h.injective]
  exact sec5b6_ncard_weight k

theorem IsPerm6.disjoint_wclass (h : IsPerm6 φ A H) {j k : ℕ} (hjk : j ≠ k) :
    Disjoint (wclass φ j) (wclass φ k) := by
  rw [Set.disjoint_left]
  rintro x ⟨v, hv, rfl⟩ ⟨w, hw, hwv⟩
  exact hjk (by rw [← hv, ← hw, h.injective hwv])

theorem IsPerm6.wclass_zero (h : IsPerm6 φ A H) : wclass φ 0 = {1} := by
  ext x
  constructor
  · rintro ⟨v, hv, rfl⟩
    rw [Set.mem_singleton_iff, eq_zero_of_vecWeight_eq_zero hv, h.map_zero]
  · intro hx
    rw [Set.mem_singleton_iff] at hx
    subst hx
    exact ⟨0, sec5b6_vecWeight_zero, h.map_zero⟩

theorem IsPerm6.wclass_six (h : IsPerm6 φ A H) : wclass φ 6 = {φ 1} := by
  ext x
  constructor
  · rintro ⟨v, hv, rfl⟩
    rw [Set.mem_singleton_iff, sec5b6_eq_one_of_weight_six hv]
  · intro hx
    rw [Set.mem_singleton_iff] at hx
    subst hx
    exact ⟨1, sec5b6_vecWeight_one, rfl⟩

theorem IsPerm6.exists_conj (h : IsPerm6 φ A H) {k : ℕ} {x y : G} (hx : x ∈ wclass φ k)
    (hy : y ∈ wclass φ k) : ∃ a ∈ H, a * x * a⁻¹ = y := by
  obtain ⟨v, hv, rfl⟩ := hx
  obtain ⟨w, hw, rfl⟩ := hy
  obtain ⟨σ, hσ, hσv⟩ := sec5b6_exists_alt (v := v) (w := w) (by rw [hv, hw])
  obtain ⟨a, ha, haσ⟩ := h.2.2.2.2 σ hσ
  exact ⟨a, ha, by rw [haσ v trivial, hσv]⟩

theorem IsPerm6.wclass_subset_of_inter (h : IsPerm6 φ A H) {T : Set G}
    (hT : ∀ a ∈ H, ∀ x ∈ T, a * x * a⁻¹ ∈ T) {k : ℕ} (hne : (T ∩ wclass φ k).Nonempty) :
    wclass φ k ⊆ T := by
  obtain ⟨x, hxT, hxk⟩ := hne
  intro y hyk
  obtain ⟨a, ha, hay⟩ := h.exists_conj hxk hyk
  rw [← hay]
  exact hT a ha x hxT

theorem IsPerm6.mul_mem_wclass (h : IsPerm6 φ A H) {k : ℕ} (hk : k ≤ 6) {x : G}
    (hx : x ∈ wclass φ k) : φ 1 * x ∈ wclass φ (6 - k) := by
  obtain ⟨v, hv, rfl⟩ := hx
  refine ⟨(1 : Fin 6 → ZMod 2) + v, ?_, h.map_add 1 v⟩
  show vecWeight ((1 : Fin 6 → ZMod 2) + v) = 6 - k
  rw [add_comm, sec5b6_vecWeight_add_one, hv]

end CFSG.OddStandard.SmallF3.Omega

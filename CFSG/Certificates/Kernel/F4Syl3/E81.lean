module

public import Mathlib.GroupTheory.Index

public section

namespace CFSG.KC.F4Syl3

variable {G : Type*} [Group G] [Finite G]

theorem eq_of_comm_of_card (V B : Subgroup G) [V.Normal] (hV : Nat.card V = 81)
    (hidx : V.index ≤ 9) (hcube : ∀ g : G, g ^ 3 ∈ V)
    (h1 : ∀ g : G, g ∉ V → Nat.card {v : G // v ∈ V ∧ g * v = v * g} ≤ 9)
    (h2 : ∀ g h : G, g ∉ V → (∀ (k : ℕ), ∀ v ∈ V, h ≠ v * g ^ k) →
      Nat.card {v : G // v ∈ V ∧ g * v = v * g ∧ h * v = v * h} ≤ 3)
    (hB : ∀ x ∈ B, ∀ y ∈ B, x * y = y * x) (hBcard : Nat.card B = 81) : B = V := by
  have hmul : Nat.card (V.subgroupOf B) * V.relIndex B = 81 := by
    rw [← hBcard]
    exact (V.subgroupOf B).card_mul_index
  have hrel : V.relIndex B ≤ 9 :=
    le_trans (Nat.le_of_dvd (Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite)
      (V.relIndex_dvd_index_of_normal B)) hidx
  have hle : B ≤ V := by
    intro b hb
    by_contra hbV
    have hc1 : Nat.card (V.subgroupOf B) ≤ 9 := by
      refine le_trans (Nat.card_le_card_of_injective
        (fun x : V.subgroupOf B => (⟨(x : B), x.2, hB b hb _ (x : B).2⟩ :
          {v : G // v ∈ V ∧ b * v = v * b})) ?_) (h1 b hbV)
      intro x y hxy
      simp only [Subtype.mk.injEq] at hxy
      exact Subtype.ext (Subtype.ext hxy)
    have hc9 : Nat.card (V.subgroupOf B) = 9 := by
      by_contra hne
      have := Nat.mul_le_mul (show Nat.card (V.subgroupOf B) ≤ 8 by omega) hrel
      omega
    let f : V.subgroupOf B × Fin 3 → B := fun p => ⟨((p.1 : B) : G) * b ^ (p.2 : ℕ),
      B.mul_mem (p.1 : B).2 (B.pow_mem hb _)⟩
    have hf : Nat.card (Set.range f) ≤ 27 := by
      refine le_trans (Nat.card_le_card_of_surjective (fun p => ⟨f p, p, rfl⟩) ?_) ?_
      · rintro ⟨_, p, rfl⟩
        exact ⟨p, rfl⟩
      · rw [Nat.card_prod, hc9, Nat.card_eq_fintype_card, Fintype.card_fin]
    obtain ⟨b', hb'⟩ : ∃ b' : B, b' ∉ Set.range f := by
      by_contra hall
      push Not at hall
      have : Nat.card B ≤ Nat.card (Set.range f) :=
        Nat.card_le_card_of_injective (fun x : B => (⟨x, hall x⟩ : Set.range f))
          (fun x y h => congrArg Subtype.val h)
      omega
    have hout : ∀ (k : ℕ), ∀ v ∈ V, (b' : G) ≠ v * b ^ k := by
      intro k v hv e
      apply hb'
      have hvk : v * (b ^ 3) ^ (k / 3) ∈ V := V.mul_mem hv (V.pow_mem (hcube b) _)
      have e' : (b' : G) = v * (b ^ 3) ^ (k / 3) * b ^ (k % 3) := by
        rw [e, mul_assoc, ← pow_mul, ← pow_add, Nat.div_add_mod]
      have hvB : v * (b ^ 3) ^ (k / 3) ∈ B := by
        have : v * (b ^ 3) ^ (k / 3) = (b' : G) * (b ^ (k % 3))⁻¹ := by
          rw [e', mul_inv_cancel_right]
        rw [this]
        exact B.mul_mem b'.2 (B.inv_mem (B.pow_mem hb _))
      have hk : k % 3 < 3 := Nat.mod_lt _ (by decide)
      let p : V.subgroupOf B × Fin 3 := (⟨⟨_, hvB⟩, hvk⟩, ⟨k % 3, hk⟩)
      exact ⟨p, Subtype.ext e'.symm⟩
    have hc3 : Nat.card (V.subgroupOf B) ≤ 3 := by
      refine le_trans (Nat.card_le_card_of_injective
        (fun x : V.subgroupOf B => (⟨(x : B), x.2, hB b hb _ (x : B).2,
          hB _ b'.2 _ (x : B).2⟩ :
          {v : G // v ∈ V ∧ b * v = v * b ∧ (b' : G) * v = v * b'})) ?_) (h2 b b' hbV hout)
      intro x y hxy
      simp only [Subtype.mk.injEq] at hxy
      exact Subtype.ext (Subtype.ext hxy)
    omega
  exact Subgroup.eq_of_le_of_card_ge hle (by rw [hV, hBcard])

end CFSG.KC.F4Syl3

end

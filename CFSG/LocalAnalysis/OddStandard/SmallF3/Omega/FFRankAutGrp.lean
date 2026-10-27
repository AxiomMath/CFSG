module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FFRankAutDefs

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Matrix

@[expose] def FFRAGroup (n : ℕ) (d : Fin 6 → ZMod 3) (flag : Bool) (bound : ℕ) : Prop :=
  ∃ (T : Fin n → Matrix (Fin 6) (Fin 6) (ZMod 3)) (mul : Fin n → Fin n → Fin n) (one : Fin n),
    T one = 1 ∧
    (∀ i, ∃ c : ZMod 3, (c = 1 ∨ c = -1) ∧ (T i)ᵀ * diagonal d * T i = c • diagonal d) ∧
    (∀ i j, T (mul i j) = T i * T j ∨ T (mul i j) = -(T i * T j)) ∧
    (∀ i j, T i = T j ∨ T i = -T j → i = j) ∧
    ∀ H : Finset (Fin n), one ∈ H → (∀ a ∈ H, ∀ b ∈ H, mul a b ∈ H) →
      (∀ a ∈ H, ∀ b ∈ H, mul a b = mul b a) → (flag = true → ∀ a ∈ H, mul a a = one) →
      H.card ≤ bound

theorem ffRASide_of_group {n : ℕ} {d : Fin 6 → ZMod 3} {flag : Bool} {bound : ℕ}
    (h : FFRAGroup n d flag bound) : FFRASide n d flag bound := by
  obtain ⟨T, mul, one, hone, hsim, hmul, hinj, hb⟩ := h
  have assoc : ∀ a b c, mul (mul a b) c = mul a (mul b c) := by
    intro a b c
    apply hinj
    rcases hmul (mul a b) c with h1 | h1 <;> rcases hmul a b with h2 | h2 <;>
      rcases hmul a (mul b c) with h3 | h3 <;> rcases hmul b c with h4 | h4 <;>
      simp [h1, h2, h3, h4, mul_assoc]
  have one_mul' : ∀ a, mul one a = a := by
    intro a
    apply hinj
    rcases hmul one a with h1 | h1 <;> rw [h1, hone] <;> simp
  refine ⟨T, mul, one, {H | one ∈ H ∧ (∀ a ∈ H, ∀ b ∈ H, mul a b ∈ H) ∧
    (∀ a ∈ H, ∀ b ∈ H, mul a b = mul b a) ∧ (flag = true → ∀ a ∈ H, mul a a = one)},
    hone, hsim, hmul, hinj, ?_, ?_, ?_⟩
  · have h11 : mul one one = one := one_mul' one
    refine ⟨Finset.mem_singleton_self _, ?_, ?_, ?_⟩
    · intro a ha b hb
      rw [Finset.mem_singleton] at ha hb ⊢
      rw [ha, hb, h11]
    · intro a ha b hb
      rw [Finset.mem_singleton] at ha hb
      rw [ha, hb]
    · intro _ a ha
      rw [Finset.mem_singleton] at ha
      rw [ha, h11]
  · rintro H ⟨h1, h2, h3, h4⟩
    exact hb H h1 h2 h3 h4
  · rintro H ⟨h1, h2, h3, h4⟩ x hx hxx hcx
    have hxx' : mul x x ∈ H := by
      cases flag
      · simpa using hxx
      · simp at hxx
        rw [hxx]
        exact h1
    have e1 : ∀ a ∈ H, ∀ b ∈ H, mul a (mul x b) = mul x (mul a b) := by
      intro a ha b _
      rw [← assoc, ← hcx a ha, assoc]
    have e3 : ∀ a ∈ H, ∀ b ∈ H, mul (mul x a) (mul x b) = mul (mul x x) (mul a b) := by
      intro a ha b hb
      rw [assoc, e1 a ha b hb, ← assoc]
    have hmem : ∀ y, y ∈ H ∪ H.image (mul x) ↔ y ∈ H ∨ ∃ a ∈ H, mul x a = y := by
      intro y
      rw [Finset.mem_union, Finset.mem_image]
    refine ⟨Finset.mem_union_left _ h1, ?_, ?_, ?_⟩
    · intro a ha b hb
      rw [hmem] at ha hb ⊢
      rcases ha with ha | ⟨a, ha, rfl⟩ <;> rcases hb with hb | ⟨b, hb, rfl⟩
      · exact Or.inl (h2 a ha b hb)
      · exact Or.inr ⟨mul a b, h2 a ha b hb, (e1 a ha b hb).symm⟩
      · exact Or.inr ⟨mul a b, h2 a ha b hb, (assoc x a b).symm⟩
      · exact Or.inl (by rw [e3 a ha b hb]; exact h2 _ hxx' _ (h2 a ha b hb))
    · intro a ha b hb
      rw [hmem] at ha hb
      rcases ha with ha | ⟨a, ha, rfl⟩ <;> rcases hb with hb | ⟨b, hb, rfl⟩
      · exact h3 a ha b hb
      · rw [e1 a ha b hb, h3 a ha b hb, assoc]
      · rw [e1 b hb a ha, h3 b hb a ha, assoc]
      · rw [e3 a ha b hb, e3 b hb a ha, h3 a ha b hb]
    · intro hf a ha
      rw [hmem] at ha
      rcases ha with ha | ⟨a, ha, rfl⟩
      · exact h4 hf a ha
      · have hx1 : mul x x = one := by
          subst hf
          simpa using hxx
        rw [e3 a ha a ha, hx1, h4 hf a ha, one_mul']

end CFSG.OddStandard.SmallF3.Omega

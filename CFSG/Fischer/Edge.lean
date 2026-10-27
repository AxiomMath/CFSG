module

public import CFSG.Fischer.Pairs

public section

namespace CFSG.Fischer

open CFSG.Blueprint.Fischer

variable {X : Type} [Group X] {E : Set X} (hE : Pair X E) {a b : X} (ha : a ∈ E) (hb : b ∈ E)
  (hab : a ≠ b) (hc : a * b = b * a)

include hE in
theorem exists_not_commute_of_center (hZ : Subgroup.center X = ⊥) {x : X} (hx : x ∈ E) :
    ∃ y ∈ E, x * y ≠ y * x := by
  by_contra h
  push Not at h
  have hcen : x ∈ Subgroup.center X := by
    have hle : Subgroup.closure E ≤ Subgroup.centralizer {x} := by
      rw [Subgroup.closure_le]
      intro y hy
      exact Subgroup.mem_centralizer_singleton_iff.2 (h y hy).symm
    rw [hE.2.2.2.2] at hle
    rw [Subgroup.mem_center_iff]
    intro g
    exact Subgroup.mem_centralizer_singleton_iff.1 (hle (Subgroup.mem_top g))
  rw [hZ, Subgroup.mem_bot] at hcen
  exact Pair.ne_one hE hx hcen

include hE ha hb hab hc

theorem commute_mul_iff {x : X} (hx : x ∈ E) :
    x * (a * b) = a * b * x ↔ x = a ∨ x = b ∨ x ∈ LocalClass E a ∩ LocalClass E b := by
  have ha2 : a * a = 1 := Pair.mul_self hE ha
  have hb2 : b * b = 1 := Pair.mul_self hE hb
  constructor
  · intro h
    by_cases hxa : x * a = a * x
    ·
      have hxb : x * b = b * x := by
        have h1 : a * (x * b) = a * (b * x) := by
          calc a * (x * b) = x * (a * b) := by rw [← mul_assoc, ← hxa, mul_assoc]
            _ = a * b * x := h
            _ = a * (b * x) := mul_assoc _ _ _
        exact mul_left_cancel h1
      by_cases h1 : x = a
      · exact Or.inl h1
      by_cases h2 : x = b
      · exact Or.inr (Or.inl h2)
      exact Or.inr (Or.inr ⟨⟨hx, h1, hxa⟩, ⟨hx, h2, hxb⟩⟩)
    · exfalso
      have h1 : a * x * a = b * x * b := by
        calc a * x * a = a * x * a * (b * b) := by rw [hb2, mul_one]
          _ = a * (x * (a * b)) * b := by group
          _ = a * (a * b * x) * b := by rw [h]
          _ = (a * a) * b * x * b := by group
          _ = b * x * b := by rw [ha2, one_mul]
      have hxb : x * b ≠ b * x := by
        intro hxb
        apply hxa
        have : a * x * a = x := by
          rw [h1, ← hxb, mul_assoc, hb2, mul_one]
        calc x * a = a * x * a * a := by rw [this]
          _ = a * x := by rw [mul_assoc, ha2, mul_one]
      have e1 : x * a * x = x * b * x := by
        rw [← Pair.mul_mul_eq hE ha hx (fun e => hxa e.symm),
          ← Pair.mul_mul_eq hE hb hx (fun e => hxb e.symm)]
        exact h1
      apply hab
      have := mul_left_cancel (mul_right_cancel e1)
      exact this
  · rintro (h | h | ⟨⟨-, -, hxa⟩, ⟨-, -, hxb⟩⟩)
    · rw [h, ← mul_assoc, ha2, one_mul, hc, mul_assoc, ha2, mul_one]
    · rw [h, mul_assoc a, hb2, mul_one, hc, ← mul_assoc, hb2, one_mul]
    · rw [← mul_assoc, hxa, mul_assoc, hxb, mul_assoc]

omit hE ha hb hab hc in
theorem conj_commute_mul {g : X} (hg : g * (a * b) = a * b * g) {x : X}
    (hx : x * (a * b) = a * b * x) : (g * x * g⁻¹) * (a * b) = a * b * (g * x * g⁻¹) := by
  have hgi : g⁻¹ * (a * b) = a * b * g⁻¹ := (Commute.inv_left (hg : Commute g (a * b))).eq
  calc g * x * g⁻¹ * (a * b) = g * x * (a * b) * g⁻¹ := by rw [mul_assoc (g * x), hgi]; group
    _ = g * (a * b) * x * g⁻¹ := by rw [mul_assoc g x, hx]; group
    _ = a * b * (g * x * g⁻¹) := by rw [hg]; group

theorem conj_eq_or_of_commute_mul
    (hW : ∀ w ∈ LocalClass E a ∩ LocalClass E b,
      ∃ w' ∈ LocalClass E a ∩ LocalClass E b, w * w' ≠ w' * w)
    {g : X} (hg : g * (a * b) = a * b * g) :
    (g * a * g⁻¹ = a ∧ g * b * g⁻¹ = b) ∨ (g * a * g⁻¹ = b ∧ g * b * g⁻¹ = a) := by
  have ha2 : a * a = 1 := Pair.mul_self hE ha
  have hb2 : b * b = 1 := Pair.mul_self hE hb
  have hfix := fun (x : X) (hx : x ∈ E) => commute_mul_iff hE ha hb hab hc hx
  have hcomm : ∀ y ∈ ({a, b} : Set X), ∀ x ∈ E, x * (a * b) = a * b * x → y * x = x * y := by
    rintro y hy x hx hxc
    rcases (hfix x hx).1 hxc with rfl | rfl | ⟨⟨-, -, hxa⟩, ⟨-, -, hxb⟩⟩
    · rcases hy with rfl | rfl
      · rfl
      · exact hc.symm
    · rcases hy with rfl | rfl
      · exact hc
      · rfl
    · rcases hy with rfl | rfl
      · exact hxa.symm
      · exact hxb.symm
  have haf : a * (a * b) = a * b * a := (hfix a ha).2 (Or.inl rfl)
  have hbf : b * (a * b) = a * b * b := (hfix b hb).2 (Or.inr (Or.inl rfl))
  have himg : ∀ y ∈ ({a, b} : Set X), y * (a * b) = a * b * y → y ∈ E →
      g * y * g⁻¹ = a ∨ g * y * g⁻¹ = b := by
    intro y hy hyc hyE
    have hyE' : g * y * g⁻¹ ∈ E := Pair.conj_mem hE hyE g
    rcases (hfix _ hyE').1 (conj_commute_mul hg hyc) with h | h | hw
    · exact Or.inl h
    · exact Or.inr h
    · exfalso
      obtain ⟨w', hw', hne⟩ := hW _ hw
      apply hne
      have hw'c : w' * (a * b) = a * b * w' := (hfix _ hw'.1.1).2 (Or.inr (Or.inr hw'))
      have hgi : g⁻¹ * (a * b) = a * b * g⁻¹ := (Commute.inv_left (hg : Commute g (a * b))).eq
      have h1 := conj_commute_mul hgi hw'c
      rw [inv_inv] at h1
      have h2 := hcomm y hy _ (Pair.conj_mem hE hw'.1.1 g⁻¹) (by rwa [inv_inv])
      rw [inv_inv] at h2
      calc g * y * g⁻¹ * w' = g * (y * (g⁻¹ * w' * g)) * g⁻¹ := by group
        _ = g * ((g⁻¹ * w' * g) * y) * g⁻¹ := by rw [h2]
        _ = w' * (g * y * g⁻¹) := by group
  have hneq : g * a * g⁻¹ ≠ g * b * g⁻¹ := fun e => hab (by
    calc a = g⁻¹ * (g * a * g⁻¹) * g := by group
      _ = g⁻¹ * (g * b * g⁻¹) * g := by rw [e]
      _ = b := by group)
  rcases himg a (Or.inl rfl) haf ha with h1 | h1 <;>
    rcases himg b (Or.inr rfl) hbf hb with h2 | h2
  · exact absurd (h1.trans h2.symm) hneq
  · exact Or.inl ⟨h1, h2⟩
  · exact Or.inr ⟨h1, h2⟩
  · exact absurd (h1.trans h2.symm) hneq

omit hE ha hb hab in
theorem commute_mul_of_conj {g : X}
    (h : (g * a * g⁻¹ = a ∧ g * b * g⁻¹ = b) ∨ (g * a * g⁻¹ = b ∧ g * b * g⁻¹ = a)) :
    g * (a * b) = a * b * g := by
  have key : g * (a * b) * g⁻¹ = a * b := by
    rw [show g * (a * b) * g⁻¹ = (g * a * g⁻¹) * (g * b * g⁻¹) by group]
    rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · rw [h1, h2]
    · rw [h1, h2, hc]
  calc g * (a * b) = g * (a * b) * g⁻¹ * g := by group
    _ = a * b * g := by rw [key]

end CFSG.Fischer

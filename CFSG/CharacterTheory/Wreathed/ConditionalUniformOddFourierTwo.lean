module

public import CFSG.CharacterTheory.Wreathed.ConditionalUniformOddFourierCore

public section

open scoped BigOperators

namespace CFSG.Wreathed.ConditionalUniformOddFourier

open CFSG.Wreathed.ConditionalFourier CFSG.Wreathed.ConditionalOddFourier

variable {ι κ : Type*} [DecidableEq ι] [DecidableEq κ]
variable {B : Finset ι} {p : ι} {c : κ → ι → ℤ}

theorem sum_mul_four {y : ι → ℤ} {q₁ q₂ q₃ q₄ : ι} (h₁ : q₁ ∈ B) (h₂ : q₂ ∈ B) (h₃ : q₃ ∈ B)
    (h₄ : q₄ ∈ B) (h21 : q₂ ≠ q₁) (h23 : q₂ ≠ q₃) (h24 : q₂ ≠ q₄) (h31 : q₃ ≠ q₁)
    (h41 : q₄ ≠ q₁) (h34 : q₃ ≠ q₄)
    (hy : ∀ φ ∈ B, φ ≠ q₁ → φ ≠ q₂ → φ ≠ q₃ → φ ≠ q₄ → y φ = 0) (g : ι → ℤ) :
    ∑ φ ∈ B, y φ * g φ = y q₁ * g q₁ + y q₂ * g q₂ + y q₃ * g q₃ + y q₄ * g q₄ := by
  have hsub : ({q₁, q₂, q₃, q₄} : Finset ι) ⊆ B := by
    intro φ hφ
    simp only [Finset.mem_insert, Finset.mem_singleton] at hφ
    rcases hφ with h | h | h | h <;> rw [h]
    · exact h₁
    · exact h₂
    · exact h₃
    · exact h₄
  rw [← Finset.sum_subset hsub fun φ hφB hφ => by
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hφ
    rw [hy φ hφB hφ.1 hφ.2.1 hφ.2.2.1 hφ.2.2.2, zero_mul]]
  rw [Finset.sum_insert (by
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      exact ⟨Ne.symm h21, Ne.symm h31, Ne.symm h41⟩),
    Finset.sum_insert (by
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      exact ⟨h23, h24⟩), Finset.sum_pair h34]
  ring

theorem sum_mul_pair {w : ι → ℤ} {α ψ : ι} (hα : α ∈ B) (hψ : ψ ∈ B) (hαψ : α ≠ ψ)
    (hw : ∀ φ ∈ B, φ ≠ α → φ ≠ ψ → w φ = 0) (g : ι → ℤ) :
    ∑ φ ∈ B, g φ * w φ = g α * w α + g ψ * w ψ := by
  have hsub : ({α, ψ} : Finset ι) ⊆ B := by
    intro φ hφ
    simp only [Finset.mem_insert, Finset.mem_singleton] at hφ
    rcases hφ with h | h <;> rw [h]
    · exact hα
    · exact hψ
  rw [← Finset.sum_subset hsub fun φ hφB hφ => by
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hφ
    rw [hw φ hφB hφ.1 hφ.2, mul_zero], Finset.sum_pair hαψ]

omit [DecidableEq κ] in
theorem two_class_support {j₁ j₃ : κ} {σ : ℤ} {w y₀ : ι → ℤ} {α ψ χ₁ χ₃ : ι}
    (hσ : σ = 1 ∨ σ = -1) (hp : p ∈ B) (hαB : α ∈ B) (h1B : χ₁ ∈ B) (h3B : χ₃ ∈ B)
    (hαp : α ≠ p) (hα1 : α ≠ χ₁) (hα3 : α ≠ χ₃) (h1p : χ₁ ≠ p) (h3p : χ₃ ≠ p) (h13 : χ₁ ≠ χ₃)
    (hwα : w α = 1 ∨ w α = -1) (hwψ : w ψ = 2 ∨ w ψ = -2)
    (hw0 : ∀ φ ∈ B, φ ≠ α → φ ≠ ψ → w φ = 0) (hwp : w p = 0) (hw1 : w χ₁ = 0)
    (hw3 : w χ₃ = 0)
    (hc1 : ∀ φ ∈ B, c j₁ φ = -unitVector p φ + w φ + σ * unitVector χ₁ φ - σ * unitVector χ₃ φ)
    (hc3 : ∀ φ ∈ B, c j₃ φ = -unitVector p φ + w φ + σ * unitVector χ₃ φ - σ * unitVector χ₁ φ)
    (hy₀val : ∀ φ ∈ B, y₀ φ = 0 ∨ y₀ φ = 1 ∨ y₀ φ = -1) (hy₀p : y₀ p = 1)
    (ho01 : ∑ φ ∈ B, y₀ φ * c j₁ φ = 0) (ho03 : ∑ φ ∈ B, y₀ φ * c j₃ φ = 0)
    (hpar1 : ∀ φ ∈ B, c j₁ φ ≡ y₀ φ [ZMOD 2]) :
    (∀ φ ∈ B, φ ≠ p → φ ≠ α → φ ≠ χ₁ → φ ≠ χ₃ → y₀ φ = 0) ∧ (y₀ α = 1 ∨ y₀ α = -1) ∧
      (y₀ χ₃ = 1 ∨ y₀ χ₃ = -1) ∧ y₀ χ₁ = y₀ χ₃ := by
  have hoddiff : ∀ φ ∈ B, (Odd (c j₁ φ) ↔ y₀ φ ≠ 0) := by
    intro φ hφ
    have h := hpar1 φ hφ
    unfold Int.ModEq at h
    rw [Int.odd_iff]
    rcases hy₀val φ hφ with hy | hy | hy <;> rw [hy] at h ⊢ <;> omega
  have hc1off : ∀ φ ∈ B, φ ≠ p → φ ≠ χ₁ → φ ≠ χ₃ → c j₁ φ = w φ := by
    intro φ hφ h1 h2 h3
    rw [hc1 φ hφ, unitVector_of_ne h1, unitVector_of_ne h2, unitVector_of_ne h3]
    ring
  have hc1α : c j₁ α = w α := hc1off α hαB hαp hα1 hα3
  have hc13 : c j₁ χ₃ = -σ := by
    rw [hc1 χ₃ h3B, unitVector_of_ne h3p, hw3, unitVector_of_ne (Ne.symm h13), unitVector_self]
    ring
  have hy₀zero : ∀ φ ∈ B, φ ≠ p → φ ≠ α → φ ≠ χ₁ → φ ≠ χ₃ → y₀ φ = 0 := by
    intro φ hφ hφp hφα hφ1 hφ3
    by_contra hne
    have hodd := (hoddiff φ hφ).mpr hne
    rw [hc1off φ hφ hφp hφ1 hφ3] at hodd
    by_cases hφψ : φ = ψ
    · rw [hφψ] at hodd
      rcases hwψ with h | h <;> rw [h, Int.odd_iff] at hodd <;> norm_num at hodd
    · rw [hw0 φ hφ hφα hφψ, Int.odd_iff] at hodd
      norm_num at hodd
  have hunit : ∀ φ ∈ B, Odd (c j₁ φ) → y₀ φ = 1 ∨ y₀ φ = -1 := by
    intro φ hφ hodd
    have hne := (hoddiff φ hφ).mp hodd
    rcases hy₀val φ hφ with h | h | h
    · exact absurd h hne
    · exact Or.inl h
    · exact Or.inr h
  have hy₀α := hunit α hαB (by
    rw [hc1α, Int.odd_iff]
    rcases hwα with h | h <;> rw [h] <;> norm_num)
  have hy₀3 := hunit χ₃ h3B (by
    rw [hc13, Int.odd_iff]
    rcases hσ with h | h <;> rw [h] <;> norm_num)
  refine ⟨hy₀zero, hy₀α, hy₀3, ?_⟩
  have hS := sum_mul_four hp hαB h1B h3B hαp hα1 hα3 h1p h3p h13 hy₀zero
  have hE1 := ho01
  rw [hS, hy₀p, hc1 p hp, hc1 α hαB, hc1 χ₁ h1B, hc1 χ₃ h3B] at hE1
  have hE3 := ho03
  rw [hS, hy₀p, hc3 p hp, hc3 α hαB, hc3 χ₁ h1B, hc3 χ₃ h3B] at hE3
  simp only [unitVector_self, unitVector_of_ne hαp, unitVector_of_ne hα1, unitVector_of_ne hα3,
    unitVector_of_ne h1p, unitVector_of_ne h3p, unitVector_of_ne h13,
    unitVector_of_ne (Ne.symm h1p), unitVector_of_ne (Ne.symm h3p),
    unitVector_of_ne (Ne.symm h13), hwp, hw1, hw3] at hE1 hE3
  have h : σ * (y₀ χ₁ - y₀ χ₃) = 0 := by linarith only [hE1, hE3]
  rcases hσ with hs | hs <;> rw [hs] at h <;> linarith only [h]

omit [DecidableEq κ] in
theorem two_class_vanish {j₁ j₃ : κ} {σ : ℤ} {w y₀ y₁ : ι → ℤ} {α ψ χ₁ χ₃ : ι}
    (hσ : σ = 1 ∨ σ = -1) (hp : p ∈ B) (hαB : α ∈ B) (hψB : ψ ∈ B) (h1B : χ₁ ∈ B)
    (h3B : χ₃ ∈ B) (hαp : α ≠ p) (hα1 : α ≠ χ₁) (hα3 : α ≠ χ₃) (hαψ : α ≠ ψ) (h1p : χ₁ ≠ p)
    (h3p : χ₃ ≠ p) (h13 : χ₁ ≠ χ₃) (hwψ : w ψ = 2 ∨ w ψ = -2)
    (hw0 : ∀ φ ∈ B, φ ≠ α → φ ≠ ψ → w φ = 0)
    (hc1 : ∀ φ ∈ B, c j₁ φ = -unitVector p φ + w φ + σ * unitVector χ₁ φ - σ * unitVector χ₃ φ)
    (hc3 : ∀ φ ∈ B, c j₃ φ = -unitVector p φ + w φ + σ * unitVector χ₃ φ - σ * unitVector χ₁ φ)
    (hy₀zero : ∀ φ ∈ B, φ ≠ p → φ ≠ α → φ ≠ χ₁ → φ ≠ χ₃ → y₀ φ = 0)
    (hy₀α : y₀ α = 1 ∨ y₀ α = -1) (hy₀3 : y₀ χ₃ = 1 ∨ y₀ χ₃ = -1) (hcd : y₀ χ₁ = y₀ χ₃)
    (hy₀p : y₀ p = 1) (hy₁val : ∀ φ ∈ B, y₁ φ = 0 ∨ y₁ φ = 1 ∨ y₁ φ = -1) (hy₁p : y₁ p = 0)
    (hy01 : ∑ φ ∈ B, y₀ φ * y₁ φ = 0)
    (ho11 : ∑ φ ∈ B, y₁ φ * c j₁ φ = 0) (ho13 : ∑ φ ∈ B, y₁ φ * c j₃ φ = 0) :
    y₁ α = 0 ∧ y₁ χ₁ = 0 ∧ y₁ χ₃ = 0 ∧ y₁ ψ = 0 := by
  have hlin : ∀ (j : κ) (s : ℤ), (∀ φ ∈ B, c j φ =
      -unitVector p φ + w φ + s * unitVector χ₁ φ - s * unitVector χ₃ φ) →
      ∀ g : ι → ℤ, ∑ φ ∈ B, g φ * c j φ = -g p + ∑ φ ∈ B, g φ * w φ + s * g χ₁ - s * g χ₃ := by
    intro j s hcj g
    have h : ∑ φ ∈ B, g φ * c j φ = ∑ φ ∈ B, (-(g φ * unitVector p φ) + g φ * w φ +
        s * (g φ * unitVector χ₁ φ) - s * (g φ * unitVector χ₃ φ)) :=
      Finset.sum_congr rfl fun φ hφ => by rw [hcj φ hφ]; ring
    rw [h, Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.sum_add_distrib,
      Finset.sum_neg_distrib, ← Finset.mul_sum, ← Finset.mul_sum, sum_mul_unitVector hp,
      sum_mul_unitVector h1B, sum_mul_unitVector h3B]
  have hc3' : ∀ φ ∈ B, c j₃ φ =
      -unitVector p φ + w φ + (-σ) * unitVector χ₁ φ - (-σ) * unitVector χ₃ φ := by
    intro φ hφ
    rw [hc3 φ hφ]
    ring
  have hsumw := sum_mul_pair hαB hψB hαψ hw0
  have h11 := hlin j₁ σ hc1 y₁
  have h13' := hlin j₃ (-σ) hc3' y₁
  rw [ho11] at h11
  rw [ho13] at h13'
  have hu : y₁ χ₁ = y₁ χ₃ := by
    have h : σ * (y₁ χ₁ - y₁ χ₃) = 0 := by linarith only [h11, h13']
    rcases hσ with hs | hs <;> rw [hs] at h <;> linarith only [h]
  have huv : y₁ χ₁ = 0 ∧ y₁ α = 0 := by
    have h := hy01
    rw [sum_mul_four hp hαB h1B h3B hαp hα1 hα3 h1p h3p h13 hy₀zero, hy₀p, hy₁p, ← hu,
      hcd] at h
    have hv := hy₁val α hαB
    have hu' := hy₁val χ₁ h1B
    rcases hy₀α with ha | ha <;> rcases hy₀3 with hd | hd <;> rw [ha, hd] at h <;> omega
  have h3z : y₁ χ₃ = 0 := hu.symm.trans huv.1
  refine ⟨huv.2, huv.1, h3z, ?_⟩
  rw [hsumw, hy₁p, huv.2, huv.1, h3z] at h11
  rcases hwψ with h | h <;> rw [h] at h11 <;> linarith only [h11]

omit [DecidableEq κ] in
theorem two_class_exclusion_of_double {j₁ j₂ j₃ : κ} {σ : ℤ} {w y₀ y₁ : ι → ℤ}
    {α ψ χ₁ χ₃ : ι} (hσ : σ = 1 ∨ σ = -1) (hp : p ∈ B) (hαB : α ∈ B) (hψB : ψ ∈ B)
    (h1B : χ₁ ∈ B) (h3B : χ₃ ∈ B) (hαp : α ≠ p) (hα1 : α ≠ χ₁) (hα3 : α ≠ χ₃) (hψp : ψ ≠ p)
    (hψ1 : ψ ≠ χ₁) (hψ3 : ψ ≠ χ₃) (hαψ : α ≠ ψ) (h1p : χ₁ ≠ p) (h3p : χ₃ ≠ p) (h13 : χ₁ ≠ χ₃)
    (hwα : w α = 1 ∨ w α = -1) (hwψ : w ψ = 2 ∨ w ψ = -2)
    (hw0 : ∀ φ ∈ B, φ ≠ α → φ ≠ ψ → w φ = 0)
    (hc1 : ∀ φ ∈ B, c j₁ φ = -unitVector p φ + w φ + σ * unitVector χ₁ φ - σ * unitVector χ₃ φ)
    (hc3 : ∀ φ ∈ B, c j₃ φ = -unitVector p φ + w φ + σ * unitVector χ₃ φ - σ * unitVector χ₁ φ)
    (hsq2 : ∑ φ ∈ B, c j₂ φ * c j₂ φ = 8) (hg1 : ∑ φ ∈ B, c j₁ φ * c j₂ φ = 4)
    (hg3 : ∑ φ ∈ B, c j₃ φ * c j₂ φ = 4) (hp2 : c j₂ p = -1)
    (hy₀val : ∀ φ ∈ B, y₀ φ = 0 ∨ y₀ φ = 1 ∨ y₀ φ = -1)
    (hy₀4 : (B.filter fun φ => y₀ φ ≠ 0).card = 4) (hy₀p : y₀ p = 1)
    (hy₁val : ∀ φ ∈ B, y₁ φ = 0 ∨ y₁ φ = 1 ∨ y₁ φ = -1)
    (hy₁4 : (B.filter fun φ => y₁ φ ≠ 0).card = 4) (hy₁p : y₁ p = 0)
    (hy01 : ∑ φ ∈ B, y₀ φ * y₁ φ = 0)
    (ho01 : ∑ φ ∈ B, y₀ φ * c j₁ φ = 0) (ho03 : ∑ φ ∈ B, y₀ φ * c j₃ φ = 0)
    (ho11 : ∑ φ ∈ B, y₁ φ * c j₁ φ = 0) (ho13 : ∑ φ ∈ B, y₁ φ * c j₃ φ = 0)
    (hpar1 : ∀ φ ∈ B, c j₁ φ ≡ y₀ φ [ZMOD 2])
    (hpar2 : ∀ φ ∈ B, c j₂ φ ≡ y₀ φ + y₁ φ [ZMOD 2]) : False := by
  have hw1 : w χ₁ = 0 := hw0 χ₁ h1B (Ne.symm hα1) (Ne.symm hψ1)
  have hw3 : w χ₃ = 0 := hw0 χ₃ h3B (Ne.symm hα3) (Ne.symm hψ3)
  have hwp : w p = 0 := hw0 p hp (Ne.symm hαp) (Ne.symm hψp)
  obtain ⟨hy₀zero, hy₀α, hy₀3, hcd⟩ := two_class_support hσ hp hαB h1B h3B hαp hα1 hα3 h1p
    h3p h13 hwα hwψ hw0 hwp hw1 hw3 hc1 hc3 hy₀val hy₀p ho01 ho03 hpar1
  obtain ⟨hy₁α, hy₁1, hy₁3, hy₁ψ⟩ := two_class_vanish hσ hp hαB hψB h1B h3B hαp hα1 hα3 hαψ
    h1p h3p h13 hwψ hw0 hc1 hc3 hy₀zero hy₀α hy₀3 hcd hy₀p hy₁val hy₁p hy01 ho11 ho13
  have hy₁O₀ : ∀ φ ∈ B, y₀ φ ≠ 0 → y₁ φ = 0 := by
    intro φ hφ hne
    by_cases hφp : φ = p
    · rw [hφp, hy₁p]
    by_cases hφα : φ = α
    · rw [hφα, hy₁α]
    by_cases hφ1 : φ = χ₁
    · rw [hφ1, hy₁1]
    by_cases hφ3 : φ = χ₃
    · rw [hφ3, hy₁3]
    exact absurd (hy₀zero φ hφ hφp hφα hφ1 hφ3) hne
  have hdisj : Disjoint (B.filter fun φ => y₀ φ ≠ 0) (B.filter fun φ => y₁ φ ≠ 0) := by
    rw [Finset.disjoint_left]
    intro φ h0 h1
    rw [Finset.mem_filter] at h0 h1
    exact h1.2 (hy₁O₀ φ h0.1 h0.2)
  have hOcard : ((B.filter fun φ => y₀ φ ≠ 0) ∪ B.filter fun φ => y₁ φ ≠ 0).card = 8 := by
    rw [Finset.card_union_of_disjoint hdisj, hy₀4, hy₁4]
  have hodd2 : ∀ φ ∈ (B.filter fun φ => y₀ φ ≠ 0) ∪ B.filter fun φ => y₁ φ ≠ 0,
      Odd (c j₂ φ) := by
    intro φ hφ
    have hφB : φ ∈ B := by
      rcases Finset.mem_union.mp hφ with h | h <;> exact (Finset.mem_filter.mp h).1
    have h := hpar2 φ hφB
    unfold Int.ModEq at h
    rw [Int.odd_iff]
    rcases Finset.mem_union.mp hφ with h0 | h1
    · have hy1 := hy₁O₀ φ hφB (Finset.mem_filter.mp h0).2
      rcases hy₀val φ hφB with hv | hv | hv
      · exact absurd hv (Finset.mem_filter.mp h0).2
      · rw [hv, hy1] at h
        omega
      · rw [hv, hy1] at h
        omega
    · have hy0 : y₀ φ = 0 := by
        by_contra hne
        exact Finset.disjoint_left.mp hdisj (Finset.mem_filter.mpr ⟨hφB, hne⟩) h1
      rcases hy₁val φ hφB with hv | hv | hv
      · exact absurd hv (Finset.mem_filter.mp h1).2
      · rw [hv, hy0] at h
        omega
      · rw [hv, hy0] at h
        omega
  have hψO : ψ ∉ (B.filter fun φ => y₀ φ ≠ 0) ∪ B.filter fun φ => y₁ φ ≠ 0 := by
    rw [Finset.mem_union, Finset.mem_filter, Finset.mem_filter, not_or]
    exact ⟨fun h => h.2 (hy₀zero ψ hψB hψp (Ne.symm hαψ) hψ1 hψ3), fun h => h.2 hy₁ψ⟩
  have hc2ψ : c j₂ ψ = 0 :=
    eq_zero_of_sq_sum_le_card_odd
      (Finset.union_subset (Finset.filter_subset _ _) (Finset.filter_subset _ _)) hψB hψO hodd2
      (by rw [hsq2, hOcard]; norm_num)
  have h8 : ∑ φ ∈ B, c j₂ φ * (c j₁ φ + c j₃ φ) = 8 := by
    have h : ∑ φ ∈ B, c j₂ φ * (c j₁ φ + c j₃ φ) =
        ∑ φ ∈ B, c j₁ φ * c j₂ φ + ∑ φ ∈ B, c j₃ φ * c j₂ φ := by
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun φ _ => by ring
    rw [h, hg1, hg3]
    norm_num
  have hlin13 : ∑ φ ∈ B, c j₂ φ * (c j₁ φ + c j₃ φ) =
      -2 * c j₂ p + 2 * ∑ φ ∈ B, c j₂ φ * w φ := by
    have h : ∑ φ ∈ B, c j₂ φ * (c j₁ φ + c j₃ φ) =
        ∑ φ ∈ B, (-2 * (c j₂ φ * unitVector p φ) + 2 * (c j₂ φ * w φ)) :=
      Finset.sum_congr rfl fun φ hφ => by rw [hc1 φ hφ, hc3 φ hφ]; ring
    rw [h, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, sum_mul_unitVector hp]
  rw [hlin13, sum_mul_pair hαB hψB hαψ hw0, hp2, hc2ψ] at h8
  have hαsq : c j₂ α * c j₂ α ≤ 8 := by
    rw [← hsq2]
    exact Finset.single_le_sum (f := fun φ => c j₂ φ * c j₂ φ) (fun φ _ => mul_self_nonneg _)
      hαB
  have h3 : c j₂ α = 3 ∨ c j₂ α = -3 := by
    rcases hwα with h | h <;> rw [h] at h8
    · exact Or.inl (by linarith only [h8])
    · exact Or.inr (by linarith only [h8])
  rcases h3 with h | h <;> rw [h] at hαsq <;> norm_num at hαsq

theorem two_class_not_descII {d : ι → ℤ} {j₁ j₂ j₃ : κ} (h13 : j₁ ≠ j₃) {σ : ℤ} {χ : κ → ι}
    {V y₀ y₁ : ι → ℤ} (hc : ParityColumns B p d {j₁, j₃} c)
    (hf : ParityFamily B p d {j₁, j₃} c σ χ V) (h1 : ∀ j ∈ ({j₁, j₃} : Finset κ), V (χ j) = -σ)
    (hsq2 : ∑ φ ∈ B, c j₂ φ * c j₂ φ = 8) (hg1 : ∑ φ ∈ B, c j₁ φ * c j₂ φ = 4)
    (hg3 : ∑ φ ∈ B, c j₃ φ * c j₂ φ = 4) (hp2 : c j₂ p = -1)
    (hy₀val : ∀ φ ∈ B, y₀ φ = 0 ∨ y₀ φ = 1 ∨ y₀ φ = -1)
    (hy₀4 : (B.filter fun φ => y₀ φ ≠ 0).card = 4) (hy₀p : y₀ p = 1)
    (hy₁val : ∀ φ ∈ B, y₁ φ = 0 ∨ y₁ φ = 1 ∨ y₁ φ = -1)
    (hy₁4 : (B.filter fun φ => y₁ φ ≠ 0).card = 4) (hy₁p : y₁ p = 0)
    (hy01 : ∑ φ ∈ B, y₀ φ * y₁ φ = 0)
    (horth₀ : ∀ j ∈ ({j₁, j₃} : Finset κ), ∑ φ ∈ B, y₀ φ * c j φ = 0)
    (horth₁ : ∀ j ∈ ({j₁, j₃} : Finset κ), ∑ φ ∈ B, y₁ φ * c j φ = 0)
    (hpar₀ : ∀ j ∈ ({j₁, j₃} : Finset κ), ∀ φ ∈ B, c j φ ≡ y₀ φ [ZMOD 2])
    (hpar₂ : ∀ φ ∈ B, c j₂ φ ≡ y₀ φ + y₁ φ [ZMOD 2]) : False := by
  have hJ1 : j₁ ∈ ({j₁, j₃} : Finset κ) := Finset.mem_insert_self _ _
  have hJ3 : j₃ ∈ ({j₁, j₃} : Finset κ) :=
    Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
  have hcard : ({j₁, j₃} : Finset κ).card = 2 := Finset.card_pair h13
  obtain ⟨-, w, hwp, hwχ, hcw, -, -, hshape⟩ := hf.descII hc (by omega) h1
  rw [hcard] at hshape
  have herase1 : ({j₁, j₃} : Finset κ).erase j₁ = {j₃} :=
    Finset.erase_insert (by simpa using h13)
  have herase3 : ({j₁, j₃} : Finset κ).erase j₃ = {j₁} := by
    rw [Finset.pair_comm]
    exact Finset.erase_insert (by simpa using h13.symm)
  have hc1 : ∀ φ ∈ B, c j₁ φ = -unitVector p φ + w φ + σ * unitVector (χ j₁) φ -
      σ * unitVector (χ j₃) φ := by
    intro φ hφ
    rw [hcw j₁ hJ1 φ hφ, herase1, Finset.sum_singleton]
  have hc3 : ∀ φ ∈ B, c j₃ φ = -unitVector p φ + w φ + σ * unitVector (χ j₃) φ -
      σ * unitVector (χ j₁) φ := by
    intro φ hφ
    rw [hcw j₃ hJ3 φ hφ, herase3, Finset.sum_singleton]
  have hχ13 : χ j₁ ≠ χ j₃ := fun h => h13 (hf.injOn hJ1 hJ3 h)
  have hw1 := hwχ j₁ hJ1
  have hw3 := hwχ j₃ hJ3
  have hne : ∀ φ q, w q = 0 → w φ ≠ 0 → φ ≠ q := fun φ q hq hφ h => hφ (h ▸ hq)
  rcases hshape with ⟨-, hones, -⟩ | ⟨-, hval, hones, htwos⟩
  ·
    have hoddiff : ∀ φ ∈ B, (Odd (c j₁ φ) ↔ y₀ φ ≠ 0) := by
      intro φ hφ
      have h := hpar₀ j₁ hJ1 φ hφ
      unfold Int.ModEq at h
      rw [Int.odd_iff]
      rcases hy₀val φ hφ with hy | hy | hy <;> rw [hy] at h ⊢ <;> omega
    have hsub : (B.filter fun φ => |w φ| = 1) ⊆ B.filter fun φ => y₀ φ ≠ 0 := by
      intro φ hφ
      rw [Finset.mem_filter] at hφ ⊢
      have hφ0 : w φ ≠ 0 := fun h => by
        rw [h] at hφ
        norm_num at hφ
      refine ⟨hφ.1, (hoddiff φ hφ.1).mp ?_⟩
      rw [hc1 φ hφ.1, unitVector_of_ne (hne φ p hwp hφ0), unitVector_of_ne (hne φ _ hw1 hφ0),
        unitVector_of_ne (hne φ _ hw3 hφ0), Int.odd_iff]
      rcases (abs_eq (by norm_num : (0 : ℤ) ≤ 1)).mp hφ.2 with h | h <;> rw [h] <;> norm_num
    have hle := Finset.card_le_card hsub
    rw [hones, hy₀4] at hle
    norm_num at hle
  ·
    have hones' : (B.filter fun φ => |w φ| = 1).card = 1 := hones
    obtain ⟨α, hα⟩ := Finset.card_eq_one.mp hones'
    obtain ⟨ψ, hψ⟩ := Finset.card_eq_one.mp htwos
    have hαmem : α ∈ B ∧ |w α| = 1 := by
      have h : α ∈ B.filter fun φ => |w φ| = 1 := by
        rw [hα]
        exact Finset.mem_singleton_self α
      exact Finset.mem_filter.mp h
    have hψmem : ψ ∈ B ∧ |w ψ| = 2 := by
      have h : ψ ∈ B.filter fun φ => |w φ| = 2 := by
        rw [hψ]
        exact Finset.mem_singleton_self ψ
      exact Finset.mem_filter.mp h
    have hw0 : ∀ φ ∈ B, φ ≠ α → φ ≠ ψ → w φ = 0 := by
      intro φ hφ hφα hφψ
      rcases hval φ hφ with h | h | h
      · exact h
      · have hmem : φ ∈ B.filter fun φ => |w φ| = 1 := Finset.mem_filter.mpr ⟨hφ, h⟩
        rw [hα, Finset.mem_singleton] at hmem
        exact absurd hmem hφα
      · have hmem : φ ∈ B.filter fun φ => |w φ| = 2 := Finset.mem_filter.mpr ⟨hφ, h⟩
        rw [hψ, Finset.mem_singleton] at hmem
        exact absurd hmem hφψ
    have hwα0 : w α ≠ 0 := fun h => by
      have h' := hαmem.2
      rw [h] at h'
      norm_num at h'
    have hwψ0 : w ψ ≠ 0 := fun h => by
      have h' := hψmem.2
      rw [h] at h'
      norm_num at h'
    have hαψ : α ≠ ψ := by
      intro h
      have h' := hαmem.2
      rw [h, hψmem.2] at h'
      norm_num at h'
    exact two_class_exclusion_of_double (j₁ := j₁) (j₂ := j₂) (j₃ := j₃) hf.sign hc.mem
      hαmem.1 hψmem.1 (hf.mem j₁ hJ1) (hf.mem j₃ hJ3) (hne α p hwp hwα0) (hne α _ hw1 hwα0)
      (hne α _ hw3 hwα0) (hne ψ p hwp hwψ0) (hne ψ _ hw1 hwψ0) (hne ψ _ hw3 hwψ0) hαψ
      (hf.ne j₁ hJ1) (hf.ne j₃ hJ3) hχ13 ((abs_eq (by norm_num)).mp hαmem.2)
      ((abs_eq (by norm_num)).mp hψmem.2) hw0 hc1 hc3 hsq2 hg1 hg3 hp2 hy₀val hy₀4 hy₀p hy₁val
      hy₁4 hy₁p hy01 (horth₀ j₁ hJ1) (horth₀ j₃ hJ3) (horth₁ j₁ hJ1) (horth₁ j₃ hJ3)
      (hpar₀ j₁ hJ1) hpar₂

theorem two_class_constituents {d : ι → ℤ} {j₁ j₂ j₃ : κ} (h13 : j₁ ≠ j₃) {y₀ y₁ : ι → ℤ}
    (hc : ParityColumns B p d {j₁, j₃} c)
    (hsq2 : ∑ φ ∈ B, c j₂ φ * c j₂ φ = 8) (hg1 : ∑ φ ∈ B, c j₁ φ * c j₂ φ = 4)
    (hg3 : ∑ φ ∈ B, c j₃ φ * c j₂ φ = 4) (hp2 : c j₂ p = -1)
    (hy₀val : ∀ φ ∈ B, y₀ φ = 0 ∨ y₀ φ = 1 ∨ y₀ φ = -1)
    (hy₀4 : (B.filter fun φ => y₀ φ ≠ 0).card = 4) (hy₀p : y₀ p = 1)
    (hy₀deg : ∑ φ ∈ B, d φ * y₀ φ = 0)
    (hy₁val : ∀ φ ∈ B, y₁ φ = 0 ∨ y₁ φ = 1 ∨ y₁ φ = -1)
    (hy₁4 : (B.filter fun φ => y₁ φ ≠ 0).card = 4) (hy₁p : y₁ p = 0)
    (hy01 : ∑ φ ∈ B, y₀ φ * y₁ φ = 0)
    (horth₀ : ∀ j ∈ ({j₁, j₃} : Finset κ), ∑ φ ∈ B, y₀ φ * c j φ = 0)
    (horth₁ : ∀ j ∈ ({j₁, j₃} : Finset κ), ∑ φ ∈ B, y₁ φ * c j φ = 0)
    (hpar₀ : ∀ j ∈ ({j₁, j₃} : Finset κ), ∀ φ ∈ B, c j φ ≡ y₀ φ [ZMOD 2])
    (hpar₂ : ∀ φ ∈ B, c j₂ φ ≡ y₀ φ + y₁ φ [ZMOD 2]) (hdeg2 : ∀ φ ∈ B, φ ≠ p → 2 ≤ d φ) :
    ∃ (α : Fin 3 → ι) (β η : Fin 3 → ℤ) (σ : ℤ) (χ : κ → ι) (e : Fin 3),
      Function.Injective α ∧ (∀ i, α i ∈ B ∧ α i ≠ p) ∧ (∀ i, β i = 1 ∨ β i = -1) ∧
      (∀ i, η i = 1 ∨ η i = -1) ∧ (σ = 1 ∨ σ = -1) ∧ Set.InjOn χ ({j₁, j₃} : Finset κ) ∧
      (∀ j ∈ ({j₁, j₃} : Finset κ), χ j ∈ B ∧ χ j ≠ p ∧ ∀ i, χ j ≠ α i) ∧
      (∀ j ∈ ({j₁, j₃} : Finset κ), ∀ t ∈ ({j₁, j₃} : Finset κ), d (χ j) = d (χ t)) ∧
      (∀ φ ∈ B, y₀ φ = unitVector p φ + ∑ i, β i * unitVector (α i) φ) ∧
      (∀ j ∈ ({j₁, j₃} : Finset κ), ∀ φ ∈ B, c j φ =
        -unitVector p φ + ∑ i, η i * unitVector (α i) φ + 2 * σ * unitVector (χ j) φ) ∧
      η e = -β e ∧ (∀ i, i ≠ e → η i = β i) ∧ 1 + ∑ i, β i * d (α i) = 0 ∧
      (∀ j ∈ ({j₁, j₃} : Finset κ), σ * d (χ j) = 1 + β e * d (α e)) ∧ β e = σ ∧
      (∀ j ∈ ({j₁, j₃} : Finset κ), d (χ j) = d (α e) + σ) := by
  have h2 : 2 ≤ ({j₁, j₃} : Finset κ).card := by rw [Finset.card_pair h13]
  obtain ⟨σ₀, χ₀, V₀, hf₀⟩ := hc.exists_family h2
  obtain ⟨σ, χ, V, hf, hnorm⟩ := hf₀.normalize hc h2
  rcases hnorm with h0 | h1
  · obtain ⟨α, β, η, e, hinj, hα, hβ, hη, hχα, hy, hcj, hηe, hηi, hYdeg, hσδ, hβe, hδ⟩ :=
      family_constituents hc hf (Finset.mem_insert_self _ _) h0 hy₀val hy₀p hy₀deg horth₀ hpar₀
        hdeg2
    exact ⟨α, β, η, σ, χ, e, hinj, hα, hβ, hη, hf.sign, hf.injOn,
      fun j hj => ⟨hf.mem j hj, hf.ne j hj, hχα j hj⟩, hf.deg, hy, hcj, hηe, hηi, hYdeg, hσδ,
      hβe, hδ⟩
  · exact (two_class_not_descII h13 hc hf h1 hsq2 hg1 hg3 hp2 hy₀val hy₀4 hy₀p hy₁val hy₁4 hy₁p
      hy01 horth₀ horth₁ hpar₀ hpar₂).elim

end CFSG.Wreathed.ConditionalUniformOddFourier

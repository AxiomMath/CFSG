module

public import Mathlib.GroupTheory.PGroup

public section

namespace CFSG.HardMathSupport.Timmesfeld.ComponentBalance

open scoped commutatorElement

variable {X : Type*} [Group X]

@[expose, instance_reducible] def conjActionOn (B : Subgroup X) (T : Set X)
    (hT : ∀ b ∈ B, ∀ t ∈ T, b * t * b⁻¹ ∈ T) : MulAction ↥B ↥T where
  smul b t := ⟨b * t * b⁻¹, hT b b.2 t t.2⟩
  one_smul t := Subtype.ext (by
    change ((1 : ↥B) : X) * (t : X) * ((1 : ↥B) : X)⁻¹ = t
    simp)
  mul_smul a b t := Subtype.ext (by
    change ((a * b : ↥B) : X) * (t : X) * ((a * b : ↥B) : X)⁻¹ =
      (a : X) * ((b : X) * (t : X) * (b : X)⁻¹) * (a : X)⁻¹
    simp [mul_assoc])

theorem commutator_le_of_normalizer {Y B : Subgroup X}
    (hBY : B ≤ Subgroup.normalizer (Y : Set X)) : ⁅Y, B⁆ ≤ Y := by
  rw [Subgroup.commutator_le]
  intro y hy b hb
  have h1 : b * y⁻¹ * b⁻¹ ∈ Y := (Subgroup.mem_normalizer_iff.1 (hBY hb) y⁻¹).1 (Y.inv_mem hy)
  have e : ⁅y, b⁆ = y * (b * y⁻¹ * b⁻¹) := by simp only [commutatorElement_def]; group
  rw [e]
  exact Y.mul_mem hy h1

theorem conj_mem_commutator {Y B : Subgroup X}
    (hBY : B ≤ Subgroup.normalizer (Y : Set X)) {b : X} (hb : b ∈ B) {n : X}
    (hn : n ∈ ⁅Y, B⁆) : b * n * b⁻¹ ∈ ⁅Y, B⁆ := by
  rw [Subgroup.commutator_def] at hn ⊢
  refine Subgroup.closure_induction (p := fun n _ => b * n * b⁻¹ ∈
    Subgroup.closure {g | ∃ g₁ ∈ Y, ∃ g₂ ∈ B, ⁅g₁, g₂⁆ = g}) ?_ ?_ ?_ ?_ hn
  · rintro _ ⟨y, hy, c, hc, rfl⟩
    have h1 : b * y * b⁻¹ ∈ Y := (Subgroup.mem_normalizer_iff.1 (hBY hb) y).1 hy
    have h2 : b * c * b⁻¹ ∈ B := B.mul_mem (B.mul_mem hb hc) (B.inv_mem hb)
    have e : b * ⁅y, c⁆ * b⁻¹ = ⁅b * y * b⁻¹, b * c * b⁻¹⁆ := by
      simp only [commutatorElement_def]; group
    rw [e]
    exact Subgroup.subset_closure ⟨_, h1, _, h2, rfl⟩
  · simp
  · intro x y _ _ hx hy
    have : b * (x * y) * b⁻¹ = (b * x * b⁻¹) * (b * y * b⁻¹) := by group
    rw [this]
    exact Subgroup.mul_mem _ hx hy
  · intro x _ hx
    have : b * x⁻¹ * b⁻¹ = (b * x * b⁻¹)⁻¹ := by group
    rw [this]
    exact Subgroup.inv_mem _ hx

theorem le_sup_centralizer_commutator [Finite X] {p : ℕ} [Fact p.Prime] {Y B : Subgroup X}
    (hB : IsPGroup p B) (hBY : B ≤ Subgroup.normalizer (Y : Set X))
    (hY : Nat.Coprime p (Nat.card Y)) :
    Y ≤ (Y ⊓ Subgroup.centralizer (B : Set X)) ⊔ ⁅Y, B⁆ := by
  intro y hy
  set N : Subgroup X := ⁅Y, B⁆ with hN
  have hNY : N ≤ Y := commutator_le_of_normalizer hBY
  set T : Set X := {z | y⁻¹ * z ∈ N} with hT
  have hTinv : ∀ b ∈ B, ∀ t ∈ T, b * t * b⁻¹ ∈ T := by
    intro b hb t ht
    have h1 : ⁅y⁻¹, b⁆ ∈ N := Subgroup.commutator_mem_commutator (Y.inv_mem hy) hb
    have h2 : b * (y⁻¹ * t) * b⁻¹ ∈ N := conj_mem_commutator hBY hb ht
    have e : y⁻¹ * (b * t * b⁻¹) = ⁅y⁻¹, b⁆ * (b * (y⁻¹ * t) * b⁻¹) := by
      simp only [commutatorElement_def]; group
    show y⁻¹ * (b * t * b⁻¹) ∈ N
    rw [e]
    exact N.mul_mem h1 h2
  let _ : MulAction ↥B ↥T := conjActionOn B T hTinv
  have hcardT : Nat.card T = Nat.card N := by
    refine Nat.card_congr ⟨fun z => ⟨y⁻¹ * z.1, z.2⟩, fun n => ⟨y * n.1, by simp [hT]⟩, ?_, ?_⟩
    · intro z; ext; simp
    · intro n; ext; simp
  have hNcop : ¬ p ∣ Nat.card N := by
    intro hdvd
    have h1 : Nat.card N ∣ Nat.card Y := by
      have := Subgroup.card_dvd_of_le hNY
      exact this
    exact (Nat.Prime.coprime_iff_not_dvd (Fact.out : p.Prime)).1 hY (hdvd.trans h1)
  have hmod := IsPGroup.card_modEq_card_fixedPoints hB (α := ↥T)
  have hfix : (MulAction.fixedPoints ↥B ↥T).Nonempty := by
    by_contra hne
    rw [Set.not_nonempty_iff_eq_empty] at hne
    rw [hne] at hmod
    have h0 : Nat.card (↥(∅ : Set ↥T)) = 0 := by simp
    rw [h0, hcardT] at hmod
    exact hNcop ((Nat.modEq_zero_iff_dvd).1 hmod)
  obtain ⟨c, hc⟩ := hfix
  have hcB : ∀ b ∈ B, b * (c : X) * b⁻¹ = c := by
    intro b hb
    have := MulAction.mem_fixedPoints.1 hc ⟨b, hb⟩
    exact congrArg Subtype.val this
  have hcN : y⁻¹ * (c : X) ∈ N := c.2
  have hcY : (c : X) ∈ Y := by
    have : (c : X) = y * (y⁻¹ * c) := by group
    rw [this]; exact Y.mul_mem hy (hNY hcN)
  have hcC : (c : X) ∈ Subgroup.centralizer (B : Set X) := by
    rw [Subgroup.mem_centralizer_iff]
    intro b hb
    have := hcB b hb
    calc b * (c : X) = (b * c * b⁻¹) * b := by group
      _ = c * b := by rw [this]
  have : y = (c : X) * (y⁻¹ * c)⁻¹ := by group
  rw [this]
  exact Subgroup.mul_mem_sup ⟨hcY, hcC⟩ (N.inv_mem hcN)

end CFSG.HardMathSupport.Timmesfeld.ComponentBalance

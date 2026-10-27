module

public import CFSG.CharacterTheory.Wreathed.ConditionalCompleteBaseFixed
public import CFSG.CharacterTheory.Wreathed.ConditionalFiveFixedInteger

public section

open scoped BigOperators

namespace CFSG.Wreathed.ConditionalCompleteBase

open CFSG.Wreathed.ConditionalFourier CFSG.Wreathed.ConditionalFiveFixed

variable {ι : Type*} [DecidableEq ι] {B : Finset ι} {p : ι}

structure IsBaseColumn (B : Finset ι) (p : ι) (y₀ C : ι → ℤ) {κ' : Type*} (J : Finset κ')
    (xj : κ' → ι → ℤ) (b : ι → ℤ) : Prop where
  one : b p = 1
  orth_y₀ : ∑ φ ∈ B, b φ * y₀ φ = 0
  orth_x : ∀ j ∈ J, ∑ φ ∈ B, b φ * xj j φ = 0
  prod_C : ∑ φ ∈ B, b φ * C φ = 6

theorem IsBaseColumn.coords {κ' : Type*} {J : Finset κ'} {χ : κ' → ι} {M : ℕ} (hM : 2 ≤ M)
    (hJ : M ≤ J.card) {A Bq Dq ω : ι} {σ τ₀ κ : ℤ} (hσ : σ = 1 ∨ σ = -1)
    (hτ₀ : τ₀ = 1 ∨ τ₀ = -1) (hκ : κ = 1 ∨ κ = -1) (hp : p ∈ B) (hA : A ∈ B) (hBq : Bq ∈ B)
    (hDq : Dq ∈ B) (hω : ω ∈ B) (hχ : ∀ j ∈ J, χ j ∈ B) {y₀ C : ι → ℤ} {xj : κ' → ι → ℤ}
    (hy₀ : ∀ φ ∈ B, y₀ φ = unitVector p φ + σ * unitVector A φ - τ₀ * unitVector Bq φ +
      κ * unitVector Dq φ)
    (hxj : ∀ j ∈ J, ∀ φ ∈ B, xj j φ = fixedPart p A Bq Dq σ τ₀ κ φ +
      2 * σ * unitVector (χ j) φ)
    (hC : ∀ φ ∈ B, C φ = unitVector p φ - σ * unitVector A φ - τ₀ * unitVector Bq φ -
      κ * unitVector Dq φ + 2 * τ₀ * unitVector ω φ)
    {b : ι → ℤ} (hb : IsBaseColumn B p y₀ C J xj b)
    (hN : b p * b p + b A * b A + b Bq * b Bq + b Dq * b Dq + b ω * b ω +
      ∑ j ∈ J, b (χ j) * b (χ j) ≤ 7) :
    b A = -σ ∧ (∀ j ∈ J, b (χ j) = 0) ∧
      ((b Bq = -τ₀ ∧ b Dq = -κ ∧ b ω = τ₀) ∨ (b Bq = 0 ∧ b Dq = 0 ∧ b ω = 2 * τ₀)) := by
  have e1 := hb.orth_y₀
  rw [Finset.sum_congr rfl fun φ hφ => by rw [hy₀ φ hφ]] at e1
  have e1' : b p + σ * b A - τ₀ * b Bq + κ * b Dq = 0 := by
    have h := sum_mul_four_unitVector hp hA hBq hDq b 1 σ (-τ₀) κ
    have h' : ∑ φ ∈ B, b φ * (1 * unitVector p φ + σ * unitVector A φ +
        (-τ₀) * unitVector Bq φ + κ * unitVector Dq φ) = ∑ φ ∈ B, b φ * (unitVector p φ +
          σ * unitVector A φ - τ₀ * unitVector Bq φ + κ * unitVector Dq φ) :=
      Finset.sum_congr rfl fun φ _ => by ring
    linarith
  have e2 : ∀ j ∈ J, -b p - σ * b A - τ₀ * b Bq + κ * b Dq + 2 * σ * b (χ j) = 0 := by
    intro j hj
    have h := hb.orth_x j hj
    rw [Finset.sum_congr rfl fun φ hφ => by rw [hxj j hj φ hφ]] at h
    simp only [mul_add, Finset.sum_add_distrib] at h
    rw [sum_mul_fixedPart hp hA hBq hDq] at h
    have h2 : ∑ φ ∈ B, b φ * (2 * σ * unitVector (χ j) φ) = 2 * σ * b (χ j) := by
      have h3 : ∀ φ, b φ * (2 * σ * unitVector (χ j) φ) = 2 * σ * (b φ * unitVector (χ j) φ) :=
        fun φ => by ring
      rw [Finset.sum_congr rfl fun φ _ => h3 φ, ← Finset.mul_sum, sum_mul_unitVector (hχ j hj)]
    linarith
  have e3 : b p - σ * b A - τ₀ * b Bq - κ * b Dq + 2 * τ₀ * b ω = 6 := by
    have h := hb.prod_C
    rw [Finset.sum_congr rfl fun φ hφ => by rw [hC φ hφ]] at h
    have h' := sum_mul_five_unitVector hp hA hBq hDq hω b 1 (-σ) (-τ₀) (-κ) (2 * τ₀)
    have h'' : ∑ φ ∈ B, b φ * (1 * unitVector p φ + (-σ) * unitVector A φ +
        (-τ₀) * unitVector Bq φ + (-κ) * unitVector Dq φ + (2 * τ₀) * unitVector ω φ) =
        ∑ φ ∈ B, b φ * (unitVector p φ - σ * unitVector A φ - τ₀ * unitVector Bq φ -
          κ * unitVector Dq φ + 2 * τ₀ * unitVector ω φ) :=
      Finset.sum_congr rfl fun φ _ => by ring
    linarith
  exact base_fixed_coords hM hJ hσ hτ₀ hκ hb.one e1' e2 e3 hN

theorem base_column_pair_sums {A Bq Dq : ι} {σ τ₀ κ : ℤ} (hσ : σ = 1 ∨ σ = -1)
    (hτ₀ : τ₀ = 1 ∨ τ₀ = -1) (hκ : κ = 1 ∨ κ = -1) (hp : p ∈ B) (hA : A ∈ B) (hBq : Bq ∈ B)
    (hDq : Dq ∈ B) {γ : Fin 4 → ι} (hγ : ∀ l, γ l ∈ B) {ε : Fin 4 → ℤ} {xk yr b : ι → ℤ}
    (hxk : ∀ φ ∈ B, xk φ = fixedPart p A Bq Dq σ τ₀ κ φ + ∑ l, ε l * unitVector (γ l) φ)
    (hyr : ∀ φ ∈ B, yr φ = ∑ l, (quadSign l * ε l) * unitVector (γ l) φ)
    (hbp : b p = 1) (hbA : b A = -σ)
    (hfix : (b Bq = -τ₀ ∧ b Dq = -κ) ∨ (b Bq = 0 ∧ b Dq = 0))
    (hbx : ∑ φ ∈ B, b φ * xk φ = 0) (hby : ∑ φ ∈ B, b φ * yr φ = 0) :
    ε 0 * b (γ 0) + ε 1 * b (γ 1) = 0 ∧ ε 2 * b (γ 2) + ε 3 * b (γ 3) = 0 := by
  have hP : ∑ φ ∈ B, b φ * fixedPart p A Bq Dq σ τ₀ κ φ = 0 := by
    rw [sum_mul_fixedPart hp hA hBq hDq, hbp, hbA]
    rcases hfix with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rw [h1, h2] <;>
      rcases hσ with rfl | rfl <;> rcases hτ₀ with rfl | rfl <;> rcases hκ with rfl | rfl <;>
      norm_num
  have e1 := hbx
  rw [Finset.sum_congr rfl fun φ hφ => by rw [hxk φ hφ]] at e1
  simp only [mul_add, Finset.sum_add_distrib] at e1
  rw [hP, zero_add, sum_mul_lincomb hγ, Fin.sum_univ_four] at e1
  have e2 := hby
  rw [Finset.sum_congr rfl fun φ hφ => by rw [hyr φ hφ], sum_mul_lincomb hγ, Fin.sum_univ_four,
    quadSign_zero, quadSign_one, quadSign_two, quadSign_three] at e2
  constructor <;> linarith

theorem sum_ge_three_disjoint {S₁ S₂ S₃ : Finset ι} (h₁ : S₁ ⊆ B) (h₂ : S₂ ⊆ B) (h₃ : S₃ ⊆ B)
    (h12 : Disjoint S₁ S₂) (h13 : Disjoint S₁ S₃) (h23 : Disjoint S₂ S₃) {f : ι → ℤ}
    (hf : ∀ φ ∈ B, 0 ≤ f φ) :
    ∑ φ ∈ S₁, f φ + ∑ φ ∈ S₂, f φ + ∑ φ ∈ S₃, f φ ≤ ∑ φ ∈ B, f φ := by
  rw [← Finset.sum_union h12, ← Finset.sum_union (Finset.disjoint_union_left.mpr ⟨h13, h23⟩)]
  exact Finset.sum_le_sum_of_subset_of_nonneg
    (Finset.union_subset (Finset.union_subset h₁ h₂) h₃) fun φ hφ _ => hf φ hφ

end CFSG.Wreathed.ConditionalCompleteBase

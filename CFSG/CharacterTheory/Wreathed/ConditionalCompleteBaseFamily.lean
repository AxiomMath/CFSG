module

public import CFSG.CharacterTheory.Wreathed.ConditionalCompleteBaseColumns
public import CFSG.CharacterTheory.Wreathed.ConditionalCompleteBaseSetting

public section

open scoped BigOperators

namespace CFSG.Wreathed.ConditionalCompleteBase

open CFSG.Wreathed.ConditionalFourier CFSG.Wreathed.ConditionalFiveFixed

variable {ι : Type*} [DecidableEq ι]

theorem sum_supported_quad {R : Finset ι} {γ : Fin 4 → ι} (hγ : Function.Injective γ)
    (hγR : ∀ l, γ l ∈ R) {b g : ι → ℤ} (hb : ∀ φ ∈ R, (∀ l, φ ≠ γ l) → b φ = 0) :
    ∑ φ ∈ R, b φ * g φ = ∑ l, b (γ l) * g (γ l) := by
  have hsub : Finset.univ.image γ ⊆ R := fun φ hφ => by
    obtain ⟨l, -, rfl⟩ := Finset.mem_image.mp hφ
    exact hγR l
  rw [← Finset.sum_subset hsub fun φ hφR hφ => by
    rw [hb φ hφR fun l h => hφ (Finset.mem_image.mpr ⟨l, Finset.mem_univ _, h.symm⟩), zero_mul],
    Finset.sum_image fun i _ j _ h => hγ h]

theorem sum_supported_quad_add {R : Finset ι} {γ : Fin 4 → ι} (hγ : Function.Injective γ)
    (hγR : ∀ l, γ l ∈ R) {η : ι} (hηR : η ∈ R) (hηγ : ∀ l, η ≠ γ l) {b g : ι → ℤ}
    (hb : ∀ φ ∈ R, (∀ l, φ ≠ γ l) → φ ≠ η → b φ = 0) :
    ∑ φ ∈ R, b φ * g φ = ∑ l, b (γ l) * g (γ l) + b η * g η := by
  have hsub : insert η (Finset.univ.image γ) ⊆ R := by
    intro φ hφ
    rcases Finset.mem_insert.mp hφ with rfl | hφ
    · exact hηR
    · obtain ⟨l, -, rfl⟩ := Finset.mem_image.mp hφ
      exact hγR l
  have hηn : η ∉ Finset.univ.image γ := by
    rw [Finset.mem_image]
    rintro ⟨l, -, hl⟩
    exact hηγ l hl.symm
  rw [← Finset.sum_subset hsub fun φ hφR hφ => by
    rw [Finset.mem_insert, not_or] at hφ
    rw [hb φ hφR (fun l h => hφ.2 (Finset.mem_image.mpr ⟨l, Finset.mem_univ _, h.symm⟩)) hφ.1,
      zero_mul],
    Finset.sum_insert hηn, Finset.sum_image fun i _ j _ h => hγ h, add_comm]

variable {B : Finset ι} {p A Bq Dq ω : ι} {σ τ₀ κ : ℤ} {κ' : Type*} {J : Finset κ'}
  {χ : κ' → ι} {y₀ C : ι → ℤ} {xj : κ' → ι → ℤ}

structure BaseFamily (B : Finset ι) (p A Bq Dq ω : ι) (σ τ₀ κ : ℤ) {κ' : Type*}
    (J : Finset κ') (χ : κ' → ι) (y₀ C : ι → ℤ) (xj : κ' → ι → ℤ) (M : ℕ)
    (γ : ℕ → Fin 4 → ι) (ε : ℕ → Fin 4 → ℤ) (xk yr : ℕ → ι → ℤ) (cd cd' : ℕ → ι → ℤ)
    {β : Type*} (V : Finset β) (dg : β → ι → ℤ) : Prop where
  quad : ∀ r ∈ Finset.Ico 1 M,
    Quadruple B p A Bq Dq ω σ τ₀ κ J χ (γ r) (ε r) (xk r) (yr r)
  disj : ∀ r ∈ Finset.Ico 1 M, ∀ t ∈ Finset.Ico 1 M, r ≠ t → ∀ l l', γ r l ≠ γ t l'
  diag : ∀ r ∈ Finset.Ico 1 M,
    IsBaseColumn B p y₀ C J xj (cd r) ∧ IsBaseColumn B p y₀ C J xj (cd' r)
  gen : ∀ I ∈ V, IsBaseColumn B p y₀ C J xj (dg I)
  orth_diag : ∀ r ∈ Finset.Ico 1 M, ∀ t ∈ Finset.Ico 1 M,
    ∑ φ ∈ B, cd r φ * xk t φ = 0 ∧ ∑ φ ∈ B, cd r φ * yr t φ = 0 ∧
      ∑ φ ∈ B, cd' r φ * xk t φ = 0 ∧ ∑ φ ∈ B, cd' r φ * yr t φ = 0
  orth_gen : ∀ I ∈ V, ∀ t ∈ Finset.Ico 1 M,
    ∑ φ ∈ B, dg I φ * xk t φ = 0 ∧ ∑ φ ∈ B, dg I φ * yr t φ = 0
  norm_diag : ∀ r ∈ Finset.Ico 1 M,
    ∑ φ ∈ B, cd r φ * cd r φ = 8 ∧ ∑ φ ∈ B, cd' r φ * cd' r φ = 8
  norm_gen : ∀ I ∈ V, ∑ φ ∈ B, dg I φ * dg I φ = 7
  prod_pair : ∀ r ∈ Finset.Ico 1 M, ∑ φ ∈ B, cd r φ * cd' r φ = 6
  prod_diag : ∀ r ∈ Finset.Ico 1 M, ∀ t ∈ Finset.Ico 1 M, r ≠ t →
    ∑ φ ∈ B, cd r φ * cd t φ = 6 ∧ ∑ φ ∈ B, cd r φ * cd' t φ = 6 ∧
      ∑ φ ∈ B, cd' r φ * cd' t φ = 6
  prod_gen : ∀ I ∈ V, ∀ r ∈ Finset.Ico 1 M,
    ∑ φ ∈ B, dg I φ * cd r φ = 6 ∧ ∑ φ ∈ B, dg I φ * cd' r φ = 6
  prod_gen_gen : ∀ I ∈ V, ∀ I' ∈ V, I ≠ I' → ∑ φ ∈ B, dg I φ * dg I' φ = 6
  par : ∀ r ∈ Finset.Ico 1 M, ∀ φ ∈ B, cd r φ + cd' r φ ≡ xk r φ + C φ [ZMOD 2]

end CFSG.Wreathed.ConditionalCompleteBase

module

public import CFSG.CharacterTheory.Wreathed.ConditionalFiveFixedInteger

public section

open scoped BigOperators

namespace CFSG.Wreathed.ConditionalCompleteBase

open CFSG.Wreathed.ConditionalFourier CFSG.Wreathed.ConditionalFiveFixed

variable {ι : Type*} [DecidableEq ι]

structure CoreSetting (B : Finset ι) (p A Bq Dq ω : ι) (σ τ₀ κ : ℤ) {κ' : Type*}
    (J : Finset κ') (χ : κ' → ι) (y₀ C : ι → ℤ) (xj : κ' → ι → ℤ) : Prop where
  hp : p ∈ B
  hA : A ∈ B
  hBq : Bq ∈ B
  hDq : Dq ∈ B
  hω : ω ∈ B
  hAp : A ≠ p
  hBp : Bq ≠ p
  hDp : Dq ≠ p
  hωp : ω ≠ p
  hBA : Bq ≠ A
  hDA : Dq ≠ A
  hωA : ω ≠ A
  hDB : Dq ≠ Bq
  hωB : ω ≠ Bq
  hωD : ω ≠ Dq
  hσ : σ = 1 ∨ σ = -1
  hτ₀ : τ₀ = 1 ∨ τ₀ = -1
  hκ : κ = 1 ∨ κ = -1
  hχB : ∀ j ∈ J, χ j ∈ B
  hχinj : Set.InjOn χ J
  hχcore : ∀ j ∈ J, χ j ≠ p ∧ χ j ≠ A ∧ χ j ≠ Bq ∧ χ j ≠ Dq ∧ χ j ≠ ω
  hy₀ : ∀ φ ∈ B, y₀ φ = unitVector p φ + σ * unitVector A φ - τ₀ * unitVector Bq φ +
    κ * unitVector Dq φ
  hxj : ∀ j ∈ J, ∀ φ ∈ B, xj j φ = fixedPart p A Bq Dq σ τ₀ κ φ +
    2 * σ * unitVector (χ j) φ
  hC : ∀ φ ∈ B, C φ = unitVector p φ - σ * unitVector A φ - τ₀ * unitVector Bq φ -
    κ * unitVector Dq φ + 2 * τ₀ * unitVector ω φ

structure Quadruple (B : Finset ι) (p A Bq Dq ω : ι) (σ τ₀ κ : ℤ) {κ' : Type*}
    (J : Finset κ') (χ : κ' → ι) (γ : Fin 4 → ι) (ε : Fin 4 → ℤ) (xk yr : ι → ℤ) : Prop where
  inj : Function.Injective γ
  mem : ∀ l, γ l ∈ B
  sign : ∀ l, ε l = 1 ∨ ε l = -1
  core : ∀ l, γ l ≠ p ∧ γ l ≠ A ∧ γ l ≠ Bq ∧ γ l ≠ Dq ∧ γ l ≠ ω
  odd : ∀ l, ∀ j ∈ J, γ l ≠ χ j
  hxk : ∀ φ ∈ B, xk φ = fixedPart p A Bq Dq σ τ₀ κ φ + ∑ l, ε l * unitVector (γ l) φ
  hyr : ∀ φ ∈ B, yr φ = ∑ l, (quadSign l * ε l) * unitVector (γ l) φ

@[expose] def Outside (p A Bq Dq ω : ι) {κ' : Type*} (J : Finset κ') (χ : κ' → ι)
    (γ : Fin 4 → ι) (φ : ι) : Prop :=
  φ ≠ p ∧ φ ≠ A ∧ φ ≠ Bq ∧ φ ≠ Dq ∧ φ ≠ ω ∧ (∀ j ∈ J, φ ≠ χ j) ∧ ∀ l, φ ≠ γ l

instance (p A Bq Dq ω : ι) {κ' : Type*} (J : Finset κ') (χ : κ' → ι) (γ : Fin 4 → ι) :
    DecidablePred (Outside p A Bq Dq ω J χ γ) := fun φ => by
  unfold Outside
  infer_instance

variable {B : Finset ι} {p A Bq Dq ω : ι} {σ τ₀ κ : ℤ} {κ' : Type*} {J : Finset κ'}
  {χ : κ' → ι} {y₀ C : ι → ℤ} {xj : κ' → ι → ℤ}

theorem CoreSetting.sum_split (hS : CoreSetting B p A Bq Dq ω σ τ₀ κ J χ y₀ C xj)
    {γ : Fin 4 → ι} {ε : Fin 4 → ℤ} {xk yr : ι → ℤ}
    (hQ : Quadruple B p A Bq Dq ω σ τ₀ κ J χ γ ε xk yr) (f : ι → ℤ) :
    ∑ φ ∈ B, f φ = f p + f A + f Bq + f Dq + f ω + ∑ j ∈ J, f (χ j) + ∑ l, f (γ l) +
      ∑ φ ∈ B.filter (Outside p A Bq Dq ω J χ γ), f φ := by
  set T₁ : Finset ι := {p, A, Bq, Dq, ω} with hT₁
  set T₂ := J.image χ with hT₂
  set T₃ := Finset.univ.image γ with hT₃
  have hmem₁ : ∀ φ, φ ∈ T₁ ↔ φ = p ∨ φ = A ∨ φ = Bq ∨ φ = Dq ∨ φ = ω := fun φ => by simp [hT₁]
  have hsub : T₁ ∪ T₂ ∪ T₃ ⊆ B := by
    intro φ hφ
    rcases Finset.mem_union.mp hφ with hφ | hφ
    · rcases Finset.mem_union.mp hφ with hφ | hφ
      · rcases (hmem₁ φ).mp hφ with rfl | rfl | rfl | rfl | rfl
        exacts [hS.hp, hS.hA, hS.hBq, hS.hDq, hS.hω]
      · obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hφ
        exact hS.hχB j hj
    · obtain ⟨l, -, rfl⟩ := Finset.mem_image.mp hφ
      exact hQ.mem l
  have h12 : Disjoint T₁ T₂ := by
    rw [Finset.disjoint_left]
    intro φ h1 h2
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp h2
    obtain ⟨n1, n2, n3, n4, n5⟩ := hS.hχcore j hj
    rcases (hmem₁ _).mp h1 with h | h | h | h | h <;> contradiction
  have h123 : Disjoint (T₁ ∪ T₂) T₃ := by
    rw [Finset.disjoint_left]
    intro φ h1 h3
    obtain ⟨l, -, rfl⟩ := Finset.mem_image.mp h3
    rcases Finset.mem_union.mp h1 with h1 | h2
    · obtain ⟨n1, n2, n3, n4, n5⟩ := hQ.core l
      rcases (hmem₁ _).mp h1 with h | h | h | h | h <;> contradiction
    · obtain ⟨j, hj, h⟩ := Finset.mem_image.mp h2
      exact hQ.odd l j hj h.symm
  have hfilter : B.filter (Outside p A Bq Dq ω J χ γ) =
      B.filter fun φ => φ ∉ T₁ ∪ T₂ ∪ T₃ := by
    refine Finset.filter_congr fun φ _ => ?_
    simp only [Outside, Finset.mem_union, hmem₁, hT₂, hT₃, Finset.mem_image, Finset.mem_univ,
      true_and, not_or, not_exists, not_and]
    constructor
    · rintro ⟨h1, h2, h3, h4, h5, h6, h7⟩
      exact ⟨⟨⟨h1, h2, h3, h4, h5⟩, fun j hj h => h6 j hj h.symm⟩, fun l h => h7 l h.symm⟩
    · rintro ⟨⟨⟨h1, h2, h3, h4, h5⟩, h6⟩, h7⟩
      exact ⟨h1, h2, h3, h4, h5, fun j hj h => h6 j hj h.symm, fun l h => h7 l h.symm⟩
  rw [hfilter, ← Finset.sum_filter_add_sum_filter_not B (fun φ => φ ∈ T₁ ∪ T₂ ∪ T₃) f]
  congr 1
  rw [Finset.filter_mem_eq_inter, Finset.inter_eq_right.mpr hsub, Finset.sum_union h123,
    Finset.sum_union h12, hT₂, Finset.sum_image fun i hi j hj h => hS.hχinj hi hj h, hT₃,
    Finset.sum_image fun i _ j _ h => hQ.inj h, hT₁]
  rw [Finset.sum_insert (by simp [hS.hAp.symm, hS.hBp.symm, hS.hDp.symm, hS.hωp.symm]),
    Finset.sum_insert (by simp [hS.hBA.symm, hS.hDA.symm, hS.hωA.symm]),
    Finset.sum_insert (by simp [hS.hDB.symm, hS.hωB.symm]), Finset.sum_pair hS.hωD.symm]
  ring

end CFSG.Wreathed.ConditionalCompleteBase

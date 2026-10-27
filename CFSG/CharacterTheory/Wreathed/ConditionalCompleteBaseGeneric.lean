module

public import CFSG.CharacterTheory.Wreathed.ConditionalCompleteBaseColumns
public import CFSG.CharacterTheory.Wreathed.ConditionalCompleteBaseSetting

public section

open scoped BigOperators

namespace CFSG.Wreathed.ConditionalCompleteBase

open CFSG.Wreathed.ConditionalFourier CFSG.Wreathed.ConditionalFiveFixed

variable {ι : Type*} [DecidableEq ι]

@[expose] def Outside0 (p A Bq Dq ω : ι) {κ' : Type*} (J : Finset κ') (χ : κ' → ι) (φ : ι) :
    Prop :=
  φ ≠ p ∧ φ ≠ A ∧ φ ≠ Bq ∧ φ ≠ Dq ∧ φ ≠ ω ∧ ∀ j ∈ J, φ ≠ χ j

instance (p A Bq Dq ω : ι) {κ' : Type*} (J : Finset κ') (χ : κ' → ι) :
    DecidablePred (Outside0 p A Bq Dq ω J χ) := fun φ => by
  unfold Outside0
  infer_instance

variable {B : Finset ι} {p A Bq Dq ω : ι} {σ τ₀ κ : ℤ} {κ' : Type*} {J : Finset κ'}
  {χ : κ' → ι} {y₀ C : ι → ℤ} {xj : κ' → ι → ℤ}

theorem CoreSetting.sum_split0 (hS : CoreSetting B p A Bq Dq ω σ τ₀ κ J χ y₀ C xj)
    (f : ι → ℤ) :
    ∑ φ ∈ B, f φ = f p + f A + f Bq + f Dq + f ω + ∑ j ∈ J, f (χ j) +
      ∑ φ ∈ B.filter (Outside0 p A Bq Dq ω J χ), f φ := by
  set T₁ : Finset ι := {p, A, Bq, Dq, ω} with hT₁
  set T₂ := J.image χ with hT₂
  have hmem₁ : ∀ φ, φ ∈ T₁ ↔ φ = p ∨ φ = A ∨ φ = Bq ∨ φ = Dq ∨ φ = ω := fun φ => by simp [hT₁]
  have hsub : T₁ ∪ T₂ ⊆ B := by
    intro φ hφ
    rcases Finset.mem_union.mp hφ with hφ | hφ
    · rcases (hmem₁ φ).mp hφ with rfl | rfl | rfl | rfl | rfl
      exacts [hS.hp, hS.hA, hS.hBq, hS.hDq, hS.hω]
    · obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hφ
      exact hS.hχB j hj
  have h12 : Disjoint T₁ T₂ := by
    rw [Finset.disjoint_left]
    intro φ h1 h2
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp h2
    obtain ⟨n1, n2, n3, n4, n5⟩ := hS.hχcore j hj
    rcases (hmem₁ _).mp h1 with h | h | h | h | h <;> contradiction
  have hfilter : B.filter (Outside0 p A Bq Dq ω J χ) = B.filter fun φ => φ ∉ T₁ ∪ T₂ := by
    refine Finset.filter_congr fun φ _ => ?_
    simp only [Outside0, Finset.mem_union, hmem₁, hT₂, Finset.mem_image, not_or, not_exists,
      not_and]
    constructor
    · rintro ⟨h1, h2, h3, h4, h5, h6⟩
      exact ⟨⟨h1, h2, h3, h4, h5⟩, fun j hj h => h6 j hj h.symm⟩
    · rintro ⟨⟨h1, h2, h3, h4, h5⟩, h6⟩
      exact ⟨h1, h2, h3, h4, h5, fun j hj h => h6 j hj h.symm⟩
  rw [hfilter, ← Finset.sum_filter_add_sum_filter_not B (fun φ => φ ∈ T₁ ∪ T₂) f]
  congr 1
  rw [Finset.filter_mem_eq_inter, Finset.inter_eq_right.mpr hsub, Finset.sum_union h12, hT₂,
    Finset.sum_image fun i hi j hj h => hS.hχinj hi hj h, hT₁]
  rw [Finset.sum_insert (by simp [hS.hAp.symm, hS.hBp.symm, hS.hDp.symm, hS.hωp.symm]),
    Finset.sum_insert (by simp [hS.hBA.symm, hS.hDA.symm, hS.hωA.symm]),
    Finset.sum_insert (by simp [hS.hDB.symm, hS.hωB.symm]), Finset.sum_pair hS.hωD.symm]
  ring

theorem CoreSetting.inner_split0 (hS : CoreSetting B p A Bq Dq ω σ τ₀ κ J χ y₀ C xj)
    {b b' : ι → ℤ} (hb : ∀ j ∈ J, b (χ j) = 0) :
    ∑ φ ∈ B, b φ * b' φ = b p * b' p + b A * b' A + b Bq * b' Bq + b Dq * b' Dq + b ω * b' ω +
      ∑ φ ∈ B.filter (Outside0 p A Bq Dq ω J χ), b φ * b' φ := by
  rw [hS.sum_split0 fun φ => b φ * b' φ,
    Finset.sum_eq_zero fun j hj => by rw [hb j hj, zero_mul], add_zero]

theorem generic_column {M : ℕ} (hM : 2 ≤ M) (hJ : M ≤ J.card)
    (hS : CoreSetting B p A Bq Dq ω σ τ₀ κ J χ y₀ C xj) {d : ι → ℤ}
    (hd : IsBaseColumn B p y₀ C J xj d) (hdd : ∑ φ ∈ B, d φ * d φ = 7) :
    d A = -σ ∧ (∀ j ∈ J, d (χ j) = 0) ∧
      ((d Bq = -τ₀ ∧ d Dq = -κ ∧ d ω = τ₀ ∧
          ∑ φ ∈ B.filter (Outside0 p A Bq Dq ω J χ), d φ * d φ = 2) ∨
        (d Bq = 0 ∧ d Dq = 0 ∧ d ω = 2 * τ₀ ∧
          ∑ φ ∈ B.filter (Outside0 p A Bq Dq ω J χ), d φ * d φ = 1)) := by
  have hsplit := hS.sum_split0 fun φ => d φ * d φ
  rw [hdd] at hsplit
  have hRnn : 0 ≤ ∑ φ ∈ B.filter (Outside0 p A Bq Dq ω J χ), d φ * d φ :=
    Finset.sum_nonneg fun φ _ => mul_self_nonneg _
  obtain ⟨hdA, hdχ, hform⟩ := hd.coords hM hJ hS.hσ hS.hτ₀ hS.hκ hS.hp hS.hA hS.hBq hS.hDq hS.hω
    hS.hχB hS.hy₀ hS.hxj hS.hC (by linarith)
  have hJ0 : ∑ j ∈ J, d (χ j) * d (χ j) = 0 :=
    Finset.sum_eq_zero fun j hj => by rw [hdχ j hj, mul_zero]
  have hσ2 : σ * σ = 1 := by rcases hS.hσ with h | h <;> rw [h] <;> norm_num
  have hτ2 : τ₀ * τ₀ = 1 := by rcases hS.hτ₀ with h | h <;> rw [h] <;> norm_num
  have hκ2 : κ * κ = 1 := by rcases hS.hκ with h | h <;> rw [h] <;> norm_num
  rw [hJ0, hd.one, hdA] at hsplit
  refine ⟨hdA, hdχ, ?_⟩
  rcases hform with ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩
  · rw [h1, h2, h3] at hsplit
    exact Or.inl ⟨h1, h2, h3, by linear_combination -hsplit - hσ2 - 2 * hτ2 - hκ2⟩
  · rw [h1, h2, h3] at hsplit
    exact Or.inr ⟨h1, h2, h3, by linear_combination -hsplit - hσ2 - 4 * hτ2⟩

end CFSG.Wreathed.ConditionalCompleteBase

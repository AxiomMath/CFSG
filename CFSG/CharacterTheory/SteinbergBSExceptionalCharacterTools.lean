module

public import CFSG.CharacterTheory.SmallDefect.ClassMultiplication
public import CFSG.CharacterTheory.SmallDefect.Exceptional

public section

open scoped BigOperators Classical

namespace CFSG.CharacterTheory.SteinbergBS

open CFSG.TwoRankLowerBound.Helpers CFSG.BlockSectionOrthogonality.Helpers CFSG.SmallDefect

variable {G : Type} [Group G] [Fintype G]

theorem sum_filter_isConj_eq {f : G → ℂ} (hf : BlocksIsClassFunction f) (x : G) :
    ∑ g ∈ Finset.univ.filter (fun g : G => IsConj g x), f g =
      ((Finset.univ.filter fun g : G => IsConj g x).card : ℂ) * f x := by
  rw [← nsmul_eq_mul, ← Finset.sum_const]
  refine Finset.sum_congr rfl fun g hg => ?_
  obtain ⟨c, hc⟩ := isConj_iff.mp (Finset.mem_filter.mp hg).2.symm
  rw [← hc, hf]

theorem conj_mem_filter_isConj (x : G) :
    ∀ y ∈ Finset.univ.filter (fun g : G => IsConj g x), ∀ g : G,
      g * y * g⁻¹ ∈ Finset.univ.filter (fun g : G => IsConj g x) := by
  intro y hy g
  rw [Finset.mem_filter] at hy ⊢
  exact ⟨Finset.mem_univ _, (isConj_iff.mpr ⟨g, rfl⟩).symm.trans hy.2⟩

theorem class_multiplication_count (x₁ x₂ z : G) :
    ((((Finset.univ.filter fun g : G => IsConj g x₁) ×ˢ
        (Finset.univ.filter fun g : G => IsConj g x₂)).filter fun q => q.1 * q.2 = z).card : ℂ) =
      ((Finset.univ.filter fun g : G => IsConj g x₁).card : ℂ) *
          (Finset.univ.filter fun g : G => IsConj g x₂).card / Nat.card G *
        ∑ χ ∈ (irreducibles_finite G).toFinset, χ x₁ * χ x₂ * starRingEnd ℂ (χ z) / χ 1 ∧
    ((((Finset.univ.filter fun g : G => IsConj g x₁) ×ˢ
        (Finset.univ.filter fun g : G => IsConj g x₂)).filter fun q => q.1 * q.2 = z).card ≠ 0 →
      (Nat.card G : ℂ) =
        ((Finset.univ.filter fun g : G => IsConj g x₁).card : ℂ) *
            (Finset.univ.filter fun g : G => IsConj g x₂).card /
            ((((Finset.univ.filter fun g : G => IsConj g x₁) ×ˢ
              (Finset.univ.filter fun g : G => IsConj g x₂)).filter fun q => q.1 * q.2 = z).card :
              ℂ) *
          ∑ χ ∈ (irreducibles_finite G).toFinset, χ x₁ * χ x₂ * starRingEnd ℂ (χ z) / χ 1) := by
  set C₁ := Finset.univ.filter fun g : G => IsConj g x₁ with hC₁
  set C₂ := Finset.univ.filter fun g : G => IsConj g x₂ with hC₂
  set a := ((C₁ ×ˢ C₂).filter fun q => q.1 * q.2 = z).card with ha
  set S := ∑ χ ∈ (irreducibles_finite G).toFinset, χ x₁ * χ x₂ * starRingEnd ℂ (χ z) / χ 1
    with hS
  have hcount : (a : ℂ) = (C₁.card : ℂ) * C₂.card / Nat.card G * S := by
    rw [ha, card_mul_eq C₁ C₂ (conj_mem_filter_isConj x₁) (conj_mem_filter_isConj x₂) z, hS,
      Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun χ hχ => ?_
    have hclass := isClassFunction_of_mem ((irreducibles_finite G).mem_toFinset.mp hχ)
    rw [hC₁, hC₂, sum_filter_isConj_eq hclass, sum_filter_isConj_eq hclass]
    ring
  refine ⟨hcount, fun ha0 => ?_⟩
  have ha0' : (a : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr ha0
  have hG0 : (Nat.card G : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Nat.card_pos.ne'
  have hc1 : (C₁.card : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Finset.card_ne_zero.mpr
    ⟨x₁, by rw [hC₁]; exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, IsConj.refl _⟩⟩)
  have hc2 : (C₂.card : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Finset.card_ne_zero.mpr
    ⟨x₂, by rw [hC₂]; exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, IsConj.refl _⟩⟩)
  rw [hcount] at ha0' ⊢
  have hS0 : S ≠ 0 := by
    intro h
    rw [h, mul_zero] at ha0'
    exact ha0' rfl
  field_simp

section Suzuki

variable {H : Subgroup G} {A : Set G}

omit [Fintype G] in
theorem conj_mem_suzukiSet
    (hcent : ∀ a ∈ A, Subgroup.centralizer ({a} : Set G) ≤ H)
    (hfus : ∀ a ∈ A, ∀ b ∈ A, IsConj a b → ∃ h ∈ H, h * a * h⁻¹ = b)
    {a : G} (ha : a ∈ A) {c : G} (hca : c⁻¹ * a * c ∈ A) : c ∈ H := by
  have hconj : IsConj a (c⁻¹ * a * c) := isConj_iff.mpr ⟨c⁻¹, by group⟩
  obtain ⟨h, hh, hha⟩ := hfus a ha _ hca hconj
  have hch : c * h ∈ Subgroup.centralizer ({a} : Set G) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    calc c * h * a = c * (h * a * h⁻¹) * h := by group
      _ = c * (c⁻¹ * a * c) * h := by rw [hha]
      _ = a * (c * h) := by group
  have h1 := H.mul_mem (hcent a ha hch) (H.inv_mem hh)
  rwa [mul_inv_cancel_right] at h1

variable (hcent : ∀ a ∈ A, Subgroup.centralizer ({a} : Set G) ≤ H)
  (hfus : ∀ a ∈ A, ∀ b ∈ A, IsConj a b → ∃ h ∈ H, h * a * h⁻¹ = b)
include hcent hfus

theorem inducedFunction_suzuki_apply {α : H → ℂ} (hα : BlocksIsClassFunction α)
    (hsupp : ∀ h : H, (h : G) ∉ A → α h = 0) (a : H) (ha : (a : G) ∈ A) :
    inducedFunction H α a = α a :=
  inducedFunction_eq_on_trivial_intersection_support H A α (fun e c => hα e c) hsupp
    (fun _ hx _ hc hcx => hc (conj_mem_suzukiSet hcent hfus hx hcx)) a ha

omit hcent hfus in
theorem inducedFunction_suzuki_vanish {α : H → ℂ} (hsupp : ∀ h : H, (h : G) ∉ A → α h = 0)
    (x : G) (hx : ∀ a ∈ A, ¬ IsConj x a) : inducedFunction H α x = 0 :=
  inducedFunction_eq_zero_of_support_avoids_conjugates H A α hsupp x fun c hc =>
    hx _ hc (isConj_iff.mpr ⟨c⁻¹, by group⟩)

theorem inducedFunction_suzuki_inner {α β : H → ℂ} (hαsupp : ∀ h : H, (h : G) ∉ A → α h = 0)
    (hβ : BlocksIsClassFunction β) (hβsupp : ∀ h : H, (h : G) ∉ A → β h = 0) :
    BlocksInnerProduct (inducedFunction H α) (inducedFunction H β) = BlocksInnerProduct α β := by
  rw [blocksInnerProduct_inducedFunction_left H α _
    (fun e c => inducedFunction_conjugate H β e c)]
  unfold BlocksInnerProduct
  congr 1
  refine Finset.sum_congr rfl fun h _ => ?_
  dsimp only
  by_cases hh : (h : G) ∈ A
  · rw [inducedFunction_suzuki_apply hcent hfus hβ hβsupp h hh]
  · rw [hαsupp h hh, zero_mul, zero_mul]

theorem suzuki_induction_special_classes {α β : H → ℂ} (hα : BlocksIsClassFunction α)
    (hαsupp : ∀ h : H, (h : G) ∉ A → α h = 0) (hβ : BlocksIsClassFunction β)
    (hβsupp : ∀ h : H, (h : G) ∉ A → β h = 0) :
    BlocksInnerProduct (inducedFunction H α) (inducedFunction H β) = BlocksInnerProduct α β ∧
      (∀ a : H, (a : G) ∈ A → inducedFunction H α a = α a) ∧
      ∀ x : G, (∀ a ∈ A, ¬ IsConj x a) → inducedFunction H α x = 0 :=
  ⟨inducedFunction_suzuki_inner hcent hfus hαsupp hβ hβsupp,
    inducedFunction_suzuki_apply hcent hfus hα hαsupp,
    inducedFunction_suzuki_vanish hαsupp⟩

theorem suzuki_exceptional_characters (hA1 : (1 : G) ∉ A) {n : ℕ} (hn : 2 ≤ n)
    (θ : Fin n → H → ℂ) (hθ : ∀ i, θ i ∈ BlocksIrr H) (hθinj : Function.Injective θ)
    (hsupp : ∀ i j, ∀ h : H, (h : G) ∉ A → θ i h - θ j h = 0) :
    ∃ (ε : ℤ) (χ : Fin n → G → ℂ), (ε = 1 ∨ ε = -1) ∧ (∀ i, χ i ∈ BlocksIrr G) ∧
      Function.Injective χ ∧
      ∀ i j, inducedFunction H (θ i - θ j) = (ε : ℂ) • (χ i - χ j) := by
  let i₀ : Fin n := ⟨0, by omega⟩
  let i₁ : Fin n := ⟨1, by omega⟩
  have hi₁ : i₁ ≠ i₀ := fun h => by simp [i₀, i₁, Fin.ext_iff] at h
  have : Nonempty {i : Fin n // i ≠ i₀} := ⟨⟨i₁, hi₁⟩⟩
  have hdiffsupp : ∀ i j, ∀ h : H, (h : G) ∉ A → (θ i - θ j) h = 0 := fun i j h hh => by
    rw [Pi.sub_apply, hsupp i j h hh]
  have hdiffclass : ∀ i j, BlocksIsClassFunction (θ i - θ j) := by
    intro i j g c
    simp only [Pi.sub_apply]
    rw [isClassFunction_of_mem (hθ i), isClassFunction_of_mem (hθ j)]
  let f : {i : Fin n // i ≠ i₀} → G → ℂ := fun i => inducedFunction H (θ i.1 - θ i₀)
  have hfv : ∀ i, f i ∈ BlocksVChar G := fun i =>
    inducedFunction_mem_blocksVChar H ((BlocksVChar H).sub_mem
      (AddSubgroup.subset_closure (hθ i.1)) (AddSubgroup.subset_closure (hθ i₀)))
  have hf1 : ∀ i, f i 1 = 0 := fun i =>
    inducedFunction_suzuki_vanish (hdiffsupp i.1 i₀) 1 fun a ha hconj => by
      rw [isConj_one_right] at hconj
      exact hA1 (hconj ▸ ha)
  have hgram : ∀ i j, BlocksInnerProduct (f i) (f j) = 1 + if i = j then 1 else 0 := by
    intro i j
    change BlocksInnerProduct (inducedFunction H (θ i.1 - θ i₀))
      (inducedFunction H (θ j.1 - θ i₀)) = _
    rw [inducedFunction_suzuki_inner hcent hfus (hdiffsupp i.1 i₀) (hdiffclass j.1 i₀)
      (hdiffsupp j.1 i₀), blocksInnerProduct_sub_sub (hθ i.1) (hθ i₀) (hθ j.1) (hθ i₀)]
    have hij : θ i.1 = θ j.1 ↔ i = j := ⟨fun h => Subtype.ext (hθinj h), fun h => h ▸ rfl⟩
    have hi0 : θ i.1 ≠ θ i₀ := fun h => i.2 (hθinj h)
    have hj0 : θ i₀ ≠ θ j.1 := fun h => j.2 (hθinj h).symm
    simp only [hij, hi0, hj0, ↓reduceIte]
    split_ifs <;> ring
  obtain ⟨common, χ', ε, hχ'inj, hχ'ne, hε, -, hχ'⟩ :=
    blocksVChar_norm_two_gram_common_sign f hfv hf1 (by intro i j; rw [hgram i j]; congr)
  let χ : Fin n → G → ℂ := fun i =>
    if hi : i = i₀ then (common : G → ℂ) else (χ' ⟨i, hi⟩ : G → ℂ)
  have hχ0 : χ i₀ = common := by simp [χ]
  have hχi : ∀ i (hi : i ≠ i₀), χ i = χ' ⟨i, hi⟩ := fun i hi => by simp [χ, hi]
  have hind0 : ∀ i, inducedFunction H (θ i - θ i₀) = (ε : ℂ) • (χ i - χ i₀) := by
    intro i
    by_cases hi : i = i₀
    · subst hi
      rw [sub_self, sub_self, smul_zero]
      funext x
      simp [inducedFunction]
    · rw [hχi i hi, hχ0]
      exact hχ' ⟨i, hi⟩
  refine ⟨ε, χ, hε, fun i => ?_, fun i j hij => ?_, fun i j => ?_⟩
  · by_cases hi : i = i₀
    · rw [hi, hχ0]
      exact common.2
    · rw [hχi i hi]
      exact (χ' ⟨i, hi⟩).2
  · by_cases hi : i = i₀ <;> by_cases hj : j = i₀
    · rw [hi, hj]
    · rw [hi, hχ0, hχi j hj] at hij
      exact absurd (Subtype.ext hij.symm) (hχ'ne _)
    · rw [hj, hχ0, hχi i hi] at hij
      exact absurd (Subtype.ext hij) (hχ'ne _)
    · rw [hχi i hi, hχi j hj] at hij
      exact congrArg Subtype.val (hχ'inj (Subtype.ext hij))
  · have h := congrArg₂ (· - ·) (hind0 i) (hind0 j)
    rw [← inducedFunction_sub', sub_sub_sub_cancel_right, ← smul_sub,
      sub_sub_sub_cancel_right] at h
    exact h

end Suzuki

end CFSG.CharacterTheory.SteinbergBS

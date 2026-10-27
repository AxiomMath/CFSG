module

public import Mathlib.Data.Set.Card
public import Mathlib.Algebra.Group.Subgroup.Defs

public section

namespace CFSG.LocalAnalysis.RankThreeUC

variable {G : Type} [Group G] [Finite G]

theorem comb_one {A H : Subgroup G} (good bad : G → Prop)
    (_hAc : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a) (hA2 : ∀ a ∈ A, a ^ 2 = 1)
    (hgb : ∀ a, good a → ¬ bad a) (hHA : H ≤ A)
    (hH2 : ∀ a ∈ A, a ∉ H → ∀ b ∈ A, b ∉ H → a * b ∈ H)
    (hbad : ∀ a ∈ A, bad a → a ∉ H) (hHgood : ∀ a ∈ H, a ≠ 1 → good a)
    {e : G} (heA : e ∈ A) (heH : e ∉ H) (hge : good e) :
    ({a | a ∈ A ∧ a ≠ 1 ∧ bad a} : Set G).ncard < ({a | a ∈ A ∧ a ≠ 1 ∧ good a} : Set G).ncard := by
  have he1 : e ≠ 1 := fun h => heH (h ▸ H.one_mem)
  have heinv : e⁻¹ = e := inv_eq_of_mul_eq_one_right (by rw [← pow_two]; exact hA2 e heA)
  have h1 : ({a | a ∈ A ∧ a ≠ 1 ∧ bad a} : Set G).ncard ≤ ({a | a ∈ H ∧ a ≠ 1} : Set G).ncard := by
    refine Set.ncard_le_ncard_of_injOn (fun b => b * e) ?_ (mul_left_injective e).injOn
    rintro b ⟨hbA, -, hbb⟩
    refine ⟨hH2 b hbA (hbad b hbA hbb) e heA heH, fun hbe => ?_⟩
    have hbe' : b = e := by rw [← heinv]; exact eq_inv_of_mul_eq_one_left hbe
    exact hgb e hge (hbe' ▸ hbb)
  have h2 : (insert e {a | a ∈ H ∧ a ≠ 1} : Set G).ncard ≤
      ({a | a ∈ A ∧ a ≠ 1 ∧ good a} : Set G).ncard := by
    refine Set.ncard_le_ncard ?_
    rintro x (hx | ⟨hxH, hx1⟩)
    · rw [hx]; exact ⟨heA, he1, hge⟩
    · exact ⟨hHA hxH, hx1, hHgood x hxH hx1⟩
  have h3 : (insert e {a | a ∈ H ∧ a ≠ 1} : Set G).ncard =
      ({a | a ∈ H ∧ a ≠ 1} : Set G).ncard + 1 :=
    Set.ncard_insert_of_notMem (fun h => heH h.1)
  omega

theorem comb_two {A H₁ H₂ : Subgroup G} (good bad : G → Prop)
    (_hAc : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a) (_hA2 : ∀ a ∈ A, a ^ 2 = 1)
    (_hgb : ∀ a, good a → ¬ bad a) (hH₁A : H₁ ≤ A) (_hH₂A : H₂ ≤ A)
    (hH₁2 : ∀ a ∈ A, a ∉ H₁ → ∀ b ∈ A, b ∉ H₁ → a * b ∈ H₁)
    (hH₂2 : ∀ a ∈ A, a ∉ H₂ → ∀ b ∈ A, b ∉ H₂ → a * b ∈ H₂)
    (hbad₁ : ∀ a ∈ A, bad a → a ∉ H₁) (hbad₂ : ∀ a ∈ A, bad a → a ∉ H₂)
    (hgood : ∀ a ∈ H₁, a ∈ H₂ → a ≠ 1 → good a)
    {e₁ e₂ : G} (he₁ : e₁ ∈ A) (he₁₁ : e₁ ∉ H₁) (he₁₂ : e₁ ∈ H₂)
    (he₂ : e₂ ∈ A) (he₂₂ : e₂ ∉ H₂) (he₂₁ : e₂ ∈ H₁) (hg₁ : good e₁) (hg₂ : good e₂) :
    ({a | a ∈ A ∧ a ≠ 1 ∧ bad a} : Set G).ncard < ({a | a ∈ A ∧ a ≠ 1 ∧ good a} : Set G).ncard := by
  have hee : e₁ * e₂ ∈ A := A.mul_mem he₁ he₂
  have h₁ : e₁ * e₂ ∉ H₁ := fun h =>
    he₁₁ (by simpa using H₁.mul_mem h (H₁.inv_mem he₂₁))
  have h₂ : e₁ * e₂ ∉ H₂ := fun h =>
    he₂₂ (by simpa using H₂.mul_mem (H₂.inv_mem he₁₂) h)
  have hB : ({a | a ∈ A ∧ a ≠ 1 ∧ bad a} : Set G).ncard ≤
      (insert 1 {a | a ∈ H₁ ∧ a ∈ H₂ ∧ a ≠ 1} : Set G).ncard := by
    refine Set.ncard_le_ncard_of_injOn (fun b => b * (e₁ * e₂)) ?_ (mul_left_injective _).injOn
    rintro b ⟨hbA, -, hbb⟩
    have a₁ := hH₁2 b hbA (hbad₁ b hbA hbb) _ hee h₁
    have a₂ := hH₂2 b hbA (hbad₂ b hbA hbb) _ hee h₂
    by_cases hb1 : b * (e₁ * e₂) = 1
    · exact Or.inl hb1
    · exact Or.inr ⟨a₁, a₂, hb1⟩
  have hS : (insert e₁ (insert e₂ {a | a ∈ H₁ ∧ a ∈ H₂ ∧ a ≠ 1}) : Set G).ncard ≤
      ({a | a ∈ A ∧ a ≠ 1 ∧ good a} : Set G).ncard := by
    refine Set.ncard_le_ncard ?_
    rintro x (hx | hx | ⟨hx₁, hx₂, hx₃⟩)
    · rw [hx]; exact ⟨he₁, fun h => he₁₁ (h ▸ H₁.one_mem), hg₁⟩
    · rw [hx]; exact ⟨he₂, fun h => he₂₂ (h ▸ H₂.one_mem), hg₂⟩
    · exact ⟨hH₁A hx₁, hx₃, hgood x hx₁ hx₂ hx₃⟩
  have n₁ : (1 : G) ∉ ({a | a ∈ H₁ ∧ a ∈ H₂ ∧ a ≠ 1} : Set G) := fun h => h.2.2 rfl
  have n₂ : e₂ ∉ ({a | a ∈ H₁ ∧ a ∈ H₂ ∧ a ≠ 1} : Set G) := fun h => he₂₂ h.2.1
  have n₃ : e₁ ∉ (insert e₂ {a | a ∈ H₁ ∧ a ∈ H₂ ∧ a ≠ 1} : Set G) := by
    rintro (h | h)
    · exact he₂₂ (h ▸ he₁₂)
    · exact he₁₁ h.1
  have c₁ := Set.ncard_insert_of_notMem n₁
  have c₂ := Set.ncard_insert_of_notMem n₂
  have c₃ := Set.ncard_insert_of_notMem n₃
  omega

theorem comb_three {A H₁ H₂ H₃ : Subgroup G} (good bad : G → Prop)
    (_hAc : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a) (_hA2 : ∀ a ∈ A, a ^ 2 = 1)
    (_hgb : ∀ a, good a → ¬ bad a) (hH₁A : H₁ ≤ A) (_hH₂A : H₂ ≤ A) (_hH₃A : H₃ ≤ A)
    (hH₁2 : ∀ a ∈ A, a ∉ H₁ → ∀ b ∈ A, b ∉ H₁ → a * b ∈ H₁)
    (hH₂2 : ∀ a ∈ A, a ∉ H₂ → ∀ b ∈ A, b ∉ H₂ → a * b ∈ H₂)
    (hH₃2 : ∀ a ∈ A, a ∉ H₃ → ∀ b ∈ A, b ∉ H₃ → a * b ∈ H₃)
    (hbad₁ : ∀ a ∈ A, bad a → a ∉ H₁) (hbad₂ : ∀ a ∈ A, bad a → a ∉ H₂)
    (hbad₃ : ∀ a ∈ A, bad a → a ∉ H₃)
    (hgood₂₃ : ∀ a ∈ H₂, a ∈ H₃ → a ≠ 1 → good a)
    (hgood₁₃ : ∀ a ∈ H₁, a ∈ H₃ → a ≠ 1 → good a)
    {e₁ e₂ : G} (he₁ : e₁ ∈ A) (he₁₁ : e₁ ∉ H₁) (he₁₂ : e₁ ∈ H₂) (he₁₃ : e₁ ∈ H₃)
    (he₂ : e₂ ∈ A) (he₂₂ : e₂ ∉ H₂) (he₂₁ : e₂ ∈ H₁) (he₂₃ : e₂ ∈ H₃) :
    ({a | a ∈ A ∧ a ≠ 1 ∧ bad a} : Set G).ncard < ({a | a ∈ A ∧ a ≠ 1 ∧ good a} : Set G).ncard := by
  have hDpos : 0 < ({a | a ∈ H₁ ∧ a ∈ H₂ ∧ a ∈ H₃} : Set G).ncard :=
    (Set.ncard_pos (Set.toFinite _)).2 ⟨1, H₁.one_mem, H₂.one_mem, H₃.one_mem⟩
  have hBD : ({a | a ∈ A ∧ a ≠ 1 ∧ bad a} : Set G).ncard ≤
      ({a | a ∈ H₁ ∧ a ∈ H₂ ∧ a ∈ H₃} : Set G).ncard := by
    rcases ({a | a ∈ A ∧ a ≠ 1 ∧ bad a} : Set G).eq_empty_or_nonempty with h | ⟨b₀, hb₀A, -, hb₀⟩
    · rw [h]; simp
    · refine Set.ncard_le_ncard_of_injOn (fun b => b * b₀) ?_ (mul_left_injective b₀).injOn
      rintro b ⟨hbA, -, hbb⟩
      exact ⟨hH₁2 b hbA (hbad₁ b hbA hbb) b₀ hb₀A (hbad₁ b₀ hb₀A hb₀),
        hH₂2 b hbA (hbad₂ b hbA hbb) b₀ hb₀A (hbad₂ b₀ hb₀A hb₀),
        hH₃2 b hbA (hbad₃ b hbA hbb) b₀ hb₀A (hbad₃ b₀ hb₀A hb₀)⟩
  have hE₁ : ((fun d => e₁ * d) '' {a | a ∈ H₁ ∧ a ∈ H₂ ∧ a ∈ H₃} : Set G) ⊆
      {a | a ∈ A ∧ a ≠ 1 ∧ good a} := by
    rintro _ ⟨d, ⟨hd₁, hd₂, hd₃⟩, rfl⟩
    have hne : e₁ * d ≠ 1 := fun h =>
      he₁₁ (by rw [eq_inv_of_mul_eq_one_left h]; exact H₁.inv_mem hd₁)
    exact ⟨A.mul_mem he₁ (hH₁A hd₁), hne, hgood₂₃ _ (H₂.mul_mem he₁₂ hd₂)
      (H₃.mul_mem he₁₃ hd₃) hne⟩
  have hE₂ : ((fun d => e₂ * d) '' {a | a ∈ H₁ ∧ a ∈ H₂ ∧ a ∈ H₃} : Set G) ⊆
      {a | a ∈ A ∧ a ≠ 1 ∧ good a} := by
    rintro _ ⟨d, ⟨hd₁, hd₂, hd₃⟩, rfl⟩
    have hne : e₂ * d ≠ 1 := fun h =>
      he₂₂ (by rw [eq_inv_of_mul_eq_one_left h]; exact H₂.inv_mem hd₂)
    exact ⟨A.mul_mem he₂ (hH₁A hd₁), hne, hgood₁₃ _ (H₁.mul_mem he₂₁ hd₁)
      (H₃.mul_mem he₂₃ hd₃) hne⟩
  have hdisj : Disjoint ((fun d => e₁ * d) '' {a | a ∈ H₁ ∧ a ∈ H₂ ∧ a ∈ H₃} : Set G)
      ((fun d => e₂ * d) '' {a | a ∈ H₁ ∧ a ∈ H₂ ∧ a ∈ H₃}) := by
    rw [Set.disjoint_left]
    rintro _ ⟨d, ⟨hd₁, -, -⟩, rfl⟩ ⟨d', ⟨hd'₁, -, -⟩, hdd⟩
    refine he₁₁ ?_
    have : e₁ = e₂ * d' * d⁻¹ := by
      rw [eq_mul_inv_iff_mul_eq]; exact hdd.symm
    rw [this]
    exact H₁.mul_mem (H₁.mul_mem he₂₁ hd'₁) (H₁.inv_mem hd₁)
  have hU := Set.ncard_union_eq hdisj
  have hi₁ := Set.ncard_image_of_injective ({a | a ∈ H₁ ∧ a ∈ H₂ ∧ a ∈ H₃} : Set G)
    (mul_right_injective e₁)
  have hi₂ := Set.ncard_image_of_injective ({a | a ∈ H₁ ∧ a ∈ H₂ ∧ a ∈ H₃} : Set G)
    (mul_right_injective e₂)
  have hsub := Set.ncard_le_ncard (Set.union_subset hE₁ hE₂)
    (Set.toFinite ({a | a ∈ A ∧ a ≠ 1 ∧ good a} : Set G))
  omega

end CFSG.LocalAnalysis.RankThreeUC

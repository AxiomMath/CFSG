module

public import CFSG.LargeExtraspecial.DW2ModBasic

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.DW

open Module Submodule

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]

variable (Y : Subgroup (V ≃ₗ[ZMod 2] V))

@[expose] def IsNontrivFactor (A B : Submodule (ZMod 2) V) : Prop :=
  IsInv Y A ∧ IsInv Y B ∧ A ≤ B ∧ ¬ commSub Y B ≤ A ∧
    ∀ W, IsInv Y W → A ≤ W → W ≤ B → W = A ∨ W = B

@[expose] def OneFactorOn (A B : Submodule (ZMod 2) V) : Prop :=
  IsInv Y A ∧ IsInv Y B ∧ ∃ W₁ W₂ : Submodule (ZMod 2) V, A ≤ W₁ ∧ IsUnip Y A W₁ ∧
    IsNontrivFactor Y W₁ W₂ ∧ W₂ ≤ B ∧ IsUnip Y W₂ B

@[expose] def OneFactor : Prop :=
  OneFactorOn Y ⊥ ⊤

variable {Y}

theorem IsNontrivFactor.ne {A B : Submodule (ZMod 2) V} (h : IsNontrivFactor Y A B) : A ≠ B := by
  rintro rfl
  exact h.2.2.2.1 (commSub_le_of_isInv h.1)

theorem IsNontrivFactor.commSub_sup {A B : Submodule (ZMod 2) V} (h : IsNontrivFactor Y A B) :
    commSub Y B ⊔ A = B := by
  obtain ⟨hA, hB, hAB, hne, hirr⟩ := h
  rcases hirr _ ((isInv_commSub hB).sup hA) le_sup_right
      (sup_le (commSub_le_of_isInv hB) hAB) with h | h
  · exact absurd (h ▸ le_sup_left) hne
  · exact h

theorem IsNontrivFactor.not_isUnip {A B : Submodule (ZMod 2) V} (h : IsNontrivFactor Y A B) :
    ¬ IsUnip Y A B := by
  rintro ⟨k, hk⟩
  have hA := h.1
  have hB := h.2.1
  have key : ∀ j, iterComm Y B j ⊔ A = B := by
    intro j
    induction j with
    | zero => exact sup_eq_left.mpr h.2.2.1
    | succ j ih =>
      refine le_antisymm (sup_le (iterComm_le_of_isInv hB _) h.2.2.1) ?_
      calc B = commSub Y B ⊔ A := h.commSub_sup.symm
        _ ≤ commSub Y (iterComm Y B j ⊔ A) ⊔ A := by rw [ih]
        _ ≤ (commSub Y (iterComm Y B j) ⊔ commSub Y A) ⊔ A :=
          sup_le_sup_right (commSub_sup_le _ _) _
        _ ≤ iterComm Y B (j + 1) ⊔ A := by
          rw [iterComm_succ']
          exact sup_le (sup_le le_sup_left (le_sup_of_le_right (commSub_le_of_isInv hA)))
            le_sup_right
  have hBA : B ≤ A := by
    rw [← key k]
    exact sup_le hk le_rfl
  exact h.ne (le_antisymm h.2.2.1 hBA)

theorem OneFactorOn.not_isUnip {A B : Submodule (ZMod 2) V} (h : OneFactorOn Y A B) :
    ¬ IsUnip Y A B := by
  obtain ⟨-, -, W₁, W₂, hAW₁, -, hF, hW₂B, -⟩ := h
  exact fun hu => hF.not_isUnip (hu.mono hAW₁ hW₂B)

theorem OneFactorOn.dichotomy {A B : Submodule (ZMod 2) V} (h : OneFactorOn Y A B)
    {W : Submodule (ZMod 2) V} (hW : IsInv Y W) (hAW : A ≤ W) (hWB : W ≤ B) :
    IsUnip Y A W ∨ IsUnip Y W B := by
  obtain ⟨hA, -, W₁, W₂, hAW₁, ⟨k₀, hk₀⟩, hF, hW₂B, ⟨k₁, hk₁⟩⟩ := h
  obtain ⟨hW₁, hW₂, hW₁₂, -, hirr⟩ := hF
  rcases hirr ((W ⊓ W₂) ⊔ W₁) ((hW.inf hW₂).sup hW₁) le_sup_right
      (sup_le inf_le_right hW₁₂) with h1 | h1
  · left
    have hle : iterComm Y W k₁ ≤ W₁ := by
      have h2 : iterComm Y W k₁ ≤ W ⊓ W₂ :=
        le_inf (iterComm_le_of_isInv hW _) ((iterComm_mono hWB _).trans hk₁)
      exact h2.trans (h1 ▸ le_sup_left)
    exact ⟨k₁ + k₀, by rw [iterComm_add]; exact (iterComm_mono hle _).trans hk₀⟩
  · right
    have hle : iterComm Y B k₁ ≤ W ⊔ W₁ :=
      hk₁.trans (h1 ▸ sup_le_sup_right inf_le_left _)
    refine ⟨k₁ + k₀, ?_⟩
    rw [iterComm_add]
    refine (iterComm_mono hle _).trans ((iterComm_sup_le _ _ _).trans
      (sup_le (iterComm_le_of_isInv hW _) ?_))
    exact hk₀.trans hAW

variable [FiniteDimensional (ZMod 2) V]

end CFSG.LargeExtraspecial.DW

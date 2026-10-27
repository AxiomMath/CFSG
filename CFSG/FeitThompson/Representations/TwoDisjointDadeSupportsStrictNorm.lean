module

public import CFSG.FeitThompson.Representations.DadeAveragingSupportBound

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

namespace CFSG.FeitThompson

open ComplexOrder

variable {G : Type*} [Group G] [Fintype G]

theorem sum_norm_sq_of_cfInner_self_eq_one {χ : G → ℂ} (hχ : cfInner χ χ = 1) :
    ∑ g : G, ‖χ g‖ ^ 2 = (Nat.card G : ℝ) := by
  have hcard : (Nat.card G : ℂ) ≠ 0 := by simp
  rw [cfInner_self_eq_sum_norm_sq, inv_mul_eq_one₀ hcard] at hχ
  have h : ((∑ g : G, ‖χ g‖ ^ 2 : ℝ) : ℂ) = ((Nat.card G : ℝ) : ℂ) := by push_cast; exact hχ.symm
  exact_mod_cast h

variable {L₁ L₂ : Subgroup G} {A₁ A₂ : Set G} {H₁ H₂ : G → Subgroup G}

theorem sum_add_sum_totalDadeSupport_le (hD₁ : IsDadeData L₁ A₁ H₁) (hD₂ : IsDadeData L₂ A₂ H₂)
    (hdisj : Disjoint (totalDadeSupport A₁ H₁) (totalDadeSupport A₂ H₂))
    {χ : G → ℂ} (hχ : cfInner χ χ = 1) :
    ∑ g ∈ (totalDadeSupport_finite A₁ H₁).toFinset, ‖χ g‖ ^ 2
      + ∑ g ∈ (totalDadeSupport_finite A₂ H₂).toFinset, ‖χ g‖ ^ 2
      ≤ (Nat.card G : ℝ) - ‖χ 1‖ ^ 2 := by
  classical
  rw [← Finset.sum_union (Set.Finite.disjoint_toFinset.2 hdisj)]
  have hsub : (totalDadeSupport_finite A₁ H₁).toFinset ∪ (totalDadeSupport_finite A₂ H₂).toFinset
      ⊆ Finset.univ.erase 1 := by
    intro g hg
    simp only [Finset.mem_union, Set.Finite.mem_toFinset] at hg
    refine Finset.mem_erase.2 ⟨?_, Finset.mem_univ _⟩
    rintro rfl
    rcases hg with h | h
    · exact hD₁.one_notMem_totalDadeSupport h
    · exact hD₂.one_notMem_totalDadeSupport h
  calc ∑ g ∈ _ ∪ _, ‖χ g‖ ^ 2 ≤ ∑ g ∈ Finset.univ.erase (1 : G), ‖χ g‖ ^ 2 :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub fun _ _ _ => by positivity
    _ = (Nat.card G : ℝ) - ‖χ 1‖ ^ 2 := by
        rw [Finset.sum_erase_eq_sub (Finset.mem_univ _), sum_norm_sq_of_cfInner_self_eq_one hχ]

variable [Fintype ↥L₁] [Fintype ↥L₂]

theorem cfInner_self_dadeAverage_add_le_of_disjoint
    (hD₁ : IsDadeData L₁ A₁ H₁) (hD₂ : IsDadeData L₂ A₂ H₂)
    (hdisj : Disjoint (totalDadeSupport A₁ H₁) (totalDadeSupport A₂ H₂))
    {χ : classFun G} (hχ : cfInner (χ : G → ℂ) (χ : G → ℂ) = 1) :
    cfInner (fun y : ↥L₁ => dadeAverage A₁ H₁ (χ : G → ℂ) (y : G))
          (fun y : ↥L₁ => dadeAverage A₁ H₁ (χ : G → ℂ) (y : G))
        + cfInner (fun y : ↥L₂ => dadeAverage A₂ H₂ (χ : G → ℂ) (y : G))
          (fun y : ↥L₂ => dadeAverage A₂ H₂ (χ : G → ℂ) (y : G))
      ≤ 1 - (‖(χ : G → ℂ) 1‖ : ℂ) ^ 2 / (Nat.card G : ℂ) := by
  refine (add_le_add (cfInner_self_dadeAverage_le_sum_totalDadeSupport hD₁ χ)
    (cfInner_self_dadeAverage_le_sum_totalDadeSupport hD₂ χ)).trans ?_
  have hcardpos : (0 : ℝ) < (Nat.card G : ℝ) := by exact_mod_cast Nat.card_pos (α := G)
  have hreal : (Nat.card G : ℝ)⁻¹ *
      (∑ g ∈ (totalDadeSupport_finite A₁ H₁).toFinset, ‖(χ : G → ℂ) g‖ ^ 2
        + ∑ g ∈ (totalDadeSupport_finite A₂ H₂).toFinset, ‖(χ : G → ℂ) g‖ ^ 2)
      ≤ 1 - ‖(χ : G → ℂ) 1‖ ^ 2 / (Nat.card G : ℝ) := by
    rw [inv_mul_le_iff₀ hcardpos, show (Nat.card G : ℝ) *
        (1 - ‖(χ : G → ℂ) 1‖ ^ 2 / (Nat.card G : ℝ))
        = (Nat.card G : ℝ) - ‖(χ : G → ℂ) 1‖ ^ 2 by field_simp]
    exact sum_add_sum_totalDadeSupport_le hD₁ hD₂ hdisj hχ
  have hc := Complex.real_le_real.2 hreal
  push_cast at hc
  convert hc using 2
  ring

theorem cfInner_self_dadeAverage_add_lt_one_of_disjoint
    (hD₁ : IsDadeData L₁ A₁ H₁) (hD₂ : IsDadeData L₂ A₂ H₂)
    (hdisj : Disjoint (totalDadeSupport A₁ H₁) (totalDadeSupport A₂ H₂))
    {χ : classFun G} (hχ : cfInner (χ : G → ℂ) (χ : G → ℂ) = 1)
    (hχ1 : (χ : G → ℂ) 1 ≠ 0) :
    cfInner (fun y : ↥L₁ => dadeAverage A₁ H₁ (χ : G → ℂ) (y : G))
          (fun y : ↥L₁ => dadeAverage A₁ H₁ (χ : G → ℂ) (y : G))
        + cfInner (fun y : ↥L₂ => dadeAverage A₂ H₂ (χ : G → ℂ) (y : G))
          (fun y : ↥L₂ => dadeAverage A₂ H₂ (χ : G → ℂ) (y : G))
      < 1 := by
  refine (cfInner_self_dadeAverage_add_le_of_disjoint hD₁ hD₂ hdisj hχ).trans_lt ?_
  have hcardpos : (0 : ℝ) < (Nat.card G : ℝ) := by exact_mod_cast Nat.card_pos (α := G)
  have hpos : (0 : ℝ) < ‖(χ : G → ℂ) 1‖ ^ 2 / (Nat.card G : ℝ) := by
    have : (0 : ℝ) < ‖(χ : G → ℂ) 1‖ := norm_pos_iff.2 hχ1
    positivity
  have h := Complex.real_lt_real.2 (sub_lt_self (1 : ℝ) hpos)
  push_cast at h
  exact h

end CFSG.FeitThompson

end

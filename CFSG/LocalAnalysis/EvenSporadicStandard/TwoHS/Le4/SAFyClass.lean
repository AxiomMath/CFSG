module

public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoHS.Le4.SAFyDef

public section

namespace CFSG.EvenSporadicStandard.TwoHS

set_option maxRecDepth 100000 in
theorem perm5_transp : ∀ σ : Equiv.Perm (Fin 5), σ * σ = 1 → Equiv.Perm.sign σ = -1 →
    ∃ π : Equiv.Perm (Fin 5), π * Equiv.swap 0 1 * π⁻¹ = σ := by decide

theorem dihChar_sr_eq_one : ∀ k : ZMod 4, dihChar 1 (DihedralGroup.sr k) = 1 → k = 0 ∨ k = 2 := by
  decide

theorem dihChar_sr_eq_neg_one :
    ∀ k : ZMod 4, dihChar 1 (DihedralGroup.sr k) = -1 → k = 1 ∨ k = 3 := by decide

theorem z3_sq_eq_one : ∀ c : Z3, c * c = 1 → c = 1 := by decide

theorem hmodel_conj_sr2 : ((DihedralGroup.sr 2 : DihedralGroup 4), (1 : Z3),
    (1 : Equiv.Perm (Fin 5))) = (DihedralGroup.r 1, 1, 1) * (DihedralGroup.sr 0, 1, 1) *
      (DihedralGroup.r 1, 1, 1)⁻¹ := by decide

theorem hmodel_class (k : ZMod 4) (σ : Equiv.Perm (Fin 5)) (hσ2 : σ * σ = 1)
    (hpar : dihChar 1 (DihedralGroup.sr k) * Equiv.Perm.sign σ = 1)
    (hno : ¬ (σ ≠ 1 ∧ Equiv.Perm.sign σ = 1 ∧ dihChar 1 (DihedralGroup.sr k) = 1)) :
    ∃ g : HModel, ((DihedralGroup.sr k, 1, σ) : HModel) = g * (DihedralGroup.sr 0, 1, 1) * g⁻¹ ∨
      ((DihedralGroup.sr k, 1, σ) : HModel) =
        g * (DihedralGroup.sr 1, 1, Equiv.swap 0 1) * g⁻¹ := by
  rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with hs | hs
  · have hd : dihChar 1 (DihedralGroup.sr k) = 1 := by
      rw [hs, mul_one] at hpar; exact hpar
    have hσ : σ = 1 := by
      by_contra hne
      exact hno ⟨hne, hs, hd⟩
    subst hσ
    rcases dihChar_sr_eq_one k hd with rfl | rfl
    · exact ⟨1, Or.inl (by simp)⟩
    · exact ⟨(DihedralGroup.r 1, 1, 1), Or.inl hmodel_conj_sr2⟩
  · have hd : dihChar 1 (DihedralGroup.sr k) = -1 := by
      rw [hs] at hpar
      have : dihChar 1 (DihedralGroup.sr k) * -1 = 1 := hpar
      calc dihChar 1 (DihedralGroup.sr k) = dihChar 1 (DihedralGroup.sr k) * (-1) * (-1) := by
            simp
        _ = -1 := by rw [this]; simp
    obtain ⟨π, hπ⟩ := perm5_transp σ hσ2 hs
    rcases dihChar_sr_eq_neg_one k hd with rfl | rfl
    · refine ⟨(1, 1, π), Or.inr ?_⟩
      ext <;> simp [hπ]
    · refine ⟨(DihedralGroup.r 1, 1, π), Or.inr ?_⟩
      have h3 : ((DihedralGroup.sr 3 : DihedralGroup 4)) =
          DihedralGroup.r 1 * DihedralGroup.sr 1 * (DihedralGroup.r 1)⁻¹ := by decide
      refine Prod.ext ?_ (Prod.ext (by simp) ?_)
      · simpa using h3
      · simp [hπ]

end CFSG.EvenSporadicStandard.TwoHS

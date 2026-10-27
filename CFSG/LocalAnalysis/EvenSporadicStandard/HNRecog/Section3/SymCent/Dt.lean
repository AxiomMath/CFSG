module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.SymCent.Base4

public section

namespace CFSG.EvenSporadicStandard.HNRecog.Section3

open CFSG.EvenSporadicStandard.HNRecog

theorem symCent_dt (n : ℕ) {σ : Sym (n + 4)} (hσ : σ.cycleType = {2, 2}) :
    Nonempty (↥(Subgroup.centralizer ({σ} : Set (Sym (n + 4)))) ≃* DihedralGroup 4 × Sym n) := by
  let τ₀ : Sym 4 := Equiv.swap 0 1 * Equiv.swap 2 3
  have hτ₀ : τ₀.cycleType = {2, 2} :=
    Equiv.Perm.cycleType_swap_mul_swap_of_nodup (by decide)
  have hsum : τ₀.cycleType.sum = 4 := by rw [hτ₀]; decide
  obtain ⟨e₁⟩ := symCent_extend n 4 hsum (hσ.trans hτ₀.symm)
  obtain ⟨e₂⟩ := symCent_base_four hτ₀
  exact ⟨e₁.trans (e₂.prodCongr (MulEquiv.refl (Sym n)))⟩

end CFSG.EvenSporadicStandard.HNRecog.Section3

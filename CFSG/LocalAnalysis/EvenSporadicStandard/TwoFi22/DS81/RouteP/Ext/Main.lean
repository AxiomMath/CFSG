module

public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoFi22.DS81.RouteP.Ext.Defs

public section

namespace CFSG.EvenSporadicStandard.TwoFi22.DS81.RouteP

open CFSG.Monster.Code CFSG.Quasithin.H.Mathieu

universe u v

namespace CocodeExtension

variable {N : Type u} {N₀ : Type v} [Group N] [Group N₀] {E : Subgroup N} {E₀ : Subgroup N₀}
  {e : ↥E ≃* W11} {e₀ : ↥E₀ ≃* W11} (h : CocodeExtension N E e) (h₀ : CocodeExtension N₀ E₀ e₀)

theorem apply_eq_of_eT (Ψ : N ≃* N₀)
    (hΨe : ∀ x, h.toExtData.π x = 1 → h₀.toExtData.eT (Ψ x) = h.toExtData.eT x)
    (hΨπ : ∀ n, h₀.toExtData.π (Ψ n) = h.toExtData.π n) :
    ∀ x : ↥E, (Ψ x : N₀) = ((e₀.symm (e x) : ↥E₀) : N₀) := by
  intro x
  have hx : h.toExtData.π (x : N) = 1 := h.π_eq_one_iff.2 x.2
  have hΨx : (Ψ (x : N)) ∈ E₀ := h₀.π_eq_one_iff.1 ((hΨπ x).trans hx)
  have h1 := hΨe x hx
  rw [h₀.toExtData_eT hΨx, h.toExtData_eT x.2] at h1
  have h2 : (⟨Ψ (x : N), hΨx⟩ : ↥E₀) = e₀.symm (e x) := by
    rw [← h1]
    simp
  exact congrArg Subtype.val h2

end CocodeExtension

end CFSG.EvenSporadicStandard.TwoFi22.DS81.RouteP

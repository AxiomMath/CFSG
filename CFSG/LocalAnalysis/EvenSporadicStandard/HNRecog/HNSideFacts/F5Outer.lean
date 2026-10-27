module

public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoHS.Le4.S9Hmod
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoHS.Le4.S9Iso

public section

namespace CFSG.EvenSporadicStandard.TwoHS

open Subgroup CFSG.Blueprint CFSG.Blueprint.NativeSporadic CFSG.Sporadic.Recognition.HSMultiplier

section Outer


theorem IsHSCover.hsCtx {H : Type} [Group H] {E : Subgroup H} (h : IsHSCover H E) : HSCtx := by
  have hfin : Finite E := have := h.finite; inferInstance
  have := h.perfect
  obtain ⟨e⟩ := nonempty_mulEquiv_cover_of_doubleCover_hs h.perfect h.card_center h.quotient
  obtain ⟨e₀⟩ := h.quotient
  refine ⟨?_, ?_, ?_⟩
  · exact Group.IsPerfect.ofSurjective (f := e.symm.toMonoidHom) e.symm.surjective
  · rw [Nat.card_congr (centerCongr e).toEquiv]
    exact h.card_center
  · exact ⟨(QuotientGroup.congr (center HSCover) (center E) e
      (map_center_eq_of_mulEquiv e)).trans e₀⟩

theorem IsHSCover.isF5Centralizer_of_sign {H : Type} [Group H] {E : Subgroup H}
    (h : IsHSCover H E) (hi : E.index = 2)
    (hs : ∀ g : H, g ∉ E → g ^ 2 ∈ centralizer (E : Set H) → g ^ 2 = 1) :
    IsF5Centralizer H E := by
  have hnE : E.Normal := h.normal
  have hfin : Finite H := h.finite
  have hΛ : HSCtx := h.hsCtx
  have hΛfin : Finite HSCover := hΛ.finite
  have hEfin : Finite E := inferInstance
  have hEm : hΛ.Emod.Normal := hΛ.Emod_normal
  obtain ⟨φ⟩ := nonempty_mulEquiv_of_doubleCover_hs hΛ.perfect h.perfect hΛ.card_center
    h.card_center hΛ.quotient h.quotient
  have hsurj : Function.Surjective (MulAut.conjNormal : H →* MulAut E) :=
    conjNormal_surjective_of_card_le (h.card_mulAut_mul_card_centralizer_le hi)
  obtain ⟨Ψ, hΨ⟩ := exists_mulEquiv_extending_of_outer_involution (E₁ := hΛ.Emod) (E₂ := E)
    hΛ.Emod_index hi hΛ.centralizer_Emod_le (hΛ.eEmod.symm.trans φ) hsurj hΛ.yMod_not_mem
    (by rw [sq]; exact hΛ.yMod_mul_self) hs
  refine ⟨h, hi, Ψ hΛ.yMod, fun hy => hΛ.yMod_not_mem
    ((mem_iff_of_extending Ψ (hΛ.eEmod.symm.trans φ) hΨ _).2 hy), ?_⟩
  rw [← map_pow, sq, hΛ.yMod_mul_self, map_one]

end Outer

end CFSG.EvenSporadicStandard.TwoHS

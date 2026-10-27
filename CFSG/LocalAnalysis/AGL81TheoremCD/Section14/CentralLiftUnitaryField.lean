module

public import CFSG.LocalAnalysis.AGL81TheoremCD.Section14.CentralLiftKlein
import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanSL3LiftUFieldAut

public section

namespace CFSG.LocalAnalysis.AGL81TheoremCD.Section14.CentralLift

open CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
  CFSG.RankThree.PartTwo.KFacts in
theorem fixesKleinFour_of_not_mem_range {p f : ℕ} {F : Type} [Field F]
    (h : UnitaryFieldData p f F) (hp2 : p ≠ 2) (hq : 2 < p ^ f)
    {θ : MulAut (unitarySU p f F 3)} (hθ : θ ^ 3 = 1)
    (hD : MulAut.congr (suCenterEquiv h hq) (centerDescend _ θ) ∉ (psuConj h).range) :
    FixesKleinFour θ := by
  set α : MulAut (unitaryPSU h 3) :=
    MulAut.congr (suCenterEquiv h hq) (centerDescend _ θ) with hα
  have hα3 : α ^ 3 = 1 := by rw [hα, ← map_pow, ← map_pow, hθ, map_one, map_one]
  obtain ⟨σ, -, H, hαH⟩ := unitary_order_three_field_descent hq α hα3 hD
  have hθeq : θ = suConj h H * suField h σ * (suConj h H)⁻¹ := by
    apply CFSG.LocalAnalysis.RankThreeTheoremC.SL3LiftUnitaryField.eq_of_descend_eq h hq
    rw [map_mul, map_mul, map_inv, map_inv, map_mul, map_mul,
      CFSG.LocalAnalysis.RankThreeTheoremC.SL3LiftUnitaryField.descend_suConj,
      CFSG.LocalAnalysis.RankThreeTheoremC.SL3LiftUnitaryField.descend_suField]
    exact hαH
  haveI : CharP F p := h.charP
  have h2 : (2 : F) ≠ 0 := Ring.two_ne_zero (by rw [ringChar.eq F p]; exact hp2)
  rw [hθeq]
  exact FixesKleinFour.conj (fixesKleinFour_suField h h2 σ) (suConj h H)

end CFSG.LocalAnalysis.AGL81TheoremCD.Section14.CentralLift

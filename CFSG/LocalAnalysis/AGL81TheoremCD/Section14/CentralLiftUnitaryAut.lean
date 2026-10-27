module

public import CFSG.LocalAnalysis.AGL81TheoremCD.Section14.CentralLiftDefs
public import CFSG.RankThree.PartTwo.KFacts.AutPSU
import CFSG.LocalAnalysis.AGL81TheoremCD.Section14.CentralLiftUnitaryField
import CFSG.LocalAnalysis.AGL81TheoremCD.Section14.CentralLiftUnitaryCube
import CFSG.LocalAnalysis.AGL81TheoremCD.Section14.CentralLiftUnitaryTorus
import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanSL3LiftUFieldAut

public section

namespace CFSG.LocalAnalysis.AGL81TheoremCD.Section14.CentralLift

open CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
  CFSG.RankThree.PartTwo.KFacts

variable {p f : ℕ} {F : Type} [Field F]

theorem fixesKleinFour_or_fixesTorusPrime (h : UnitaryFieldData p f F) (hp2 : p ≠ 2)
    (hq : 2 < p ^ f) (h3 : 3 ∣ p ^ f + 1) {θ : MulAut (unitarySU p f F 3)} (hθ : θ ^ 3 = 1) :
    FixesKleinFour θ ∨ FixesTorusPrime (p ^ f) θ := by
  by_cases hD : MulAut.congr (suCenterEquiv h hq) (centerDescend _ θ) ∈ (psuConj h).range
  · obtain ⟨B, hB⟩ := hD
    have hθB : θ = suConj h B :=
      CFSG.LocalAnalysis.RankThreeTheoremC.SL3LiftUnitaryField.eq_of_descend_eq h hq
        (by rw [CFSG.LocalAnalysis.RankThreeTheoremC.SL3LiftUnitaryField.descend_suConj, hB])
    subst hθB
    obtain ⟨c, hc, hBc⟩ :=
      CFSG.LocalAnalysis.RankThreeTheoremC.SL3LiftUnitary.exists_scalar_pow_three h hθ
    by_cases hcube : ∃ μ : Fˣ, μ ^ 3 = c
    · obtain ⟨μ, rfl⟩ := hcube
      exact Or.inl (fixesKleinFour_of_pow_three_eq_cube h hp2 h3 B hBc)
    · refine Or.inr (fixesTorusPrime_of_not_cube h hq h3 B hc hBc fun b hb => hcube ?_)
      have hb0 : b ≠ 0 := by
        rintro rfl
        exact c.ne_zero (by rw [← hb]; ring)
      exact ⟨Units.mk0 b hb0, Units.ext (by simpa using hb)⟩
  · exact Or.inl (fixesKleinFour_of_not_mem_range h hp2 hq hθ hD)

end CFSG.LocalAnalysis.AGL81TheoremCD.Section14.CentralLift

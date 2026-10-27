module

import CFSG.LocalAnalysis.GLTheoremA.CatA.T171SmallTypeAlpha
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.GLTheoremA.S10.Defs

public section

namespace CFSG.LocalAnalysis.GLTheoremA.I167

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.LocalAnalysis.GLTheoremA CFSG.LocalAnalysis.GLTheoremA.S10

variable {Ω : Type} [Group Ω] [Finite Ω]

theorem exc_not_centMod {p : ℕ} {X : Subgroup Ω} {x : Ω} (hX : CFSG.Open.IsQuasisimple ↥X)
    (hnt : Nontrivial (PSimple p X)) (hxX : x ∉ cs X) : ¬ CentMod p X x := by
  intro hc
  have hne : GLAPPrimeCore p ↥X ≠ ⊤ := by
    intro htop
    have hsub : Subsingleton (PQuot p X) := by
      show Subsingleton (↥X ⧸ GLAPPrimeCore p ↥X)
      rw [htop]
      exact QuotientGroup.subsingleton_quotient_top
    have hsub2 : Subsingleton (PSimple p X) :=
      (QuotientGroup.mk'_surjective (Subgroup.center (PQuot p X))).subsingleton
    exact (not_subsingleton_iff_nontrivial.2 hnt) hsub2
  exact hxX (CFSG.LocalAnalysis.GLTheoremA.T171S.centralizes_of_centMod_of_isQuasisimple
    hX hne hc.1 hc)

end CFSG.LocalAnalysis.GLTheoremA.I167

end


module

public import CFSG.LocalAnalysis.OddStandard.Solomon75OddCoreCert
public import CFSG.GH74.Uniqueness.SU.SU13Final
public import CFSG.LocalAnalysis.OddStandard.Solomon75Sec3Equiv

public section

namespace CFSG.OddStandard.Solomon75

open Subgroup CFSG CFSG.GH74.GLS

section Aschbacher


theorem solomon44NineTen_of_certificate :
    Solomon44NineTen := by
  intro G _ _ hs hnonab t ht n hn hcov
  have hO : pPrimeCore 2 ↥(centralizer ({t} : Set G)) = ⊥ := by
    rcases hn with rfl | rfl
    · exact solomon44OddCore_nine_of_certificate G hnonab t ht hcov
    · exact solomon44OddCore_ten_of_certificate G hnonab t ht hcov
  let e : ↥(centralizer ({t} : Set G)) ⧸ pPrimeCore 2 ↥(centralizer ({t} : Set G)) ≃*
      ↥(centralizer ({t} : Set G)) :=
    (QuotientGroup.quotientMulEquivOfEq hO).trans QuotientGroup.quotientBot
  exact GH74.Uniqueness.SU.SU13.thm231 G hs hnonab t ht n hn
    (GH74.Uniqueness.SU.SU13.isTwoAlt_of_isDoubleCoverOfAlt
      (isDoubleCoverOfAlt_congr' e hcov))

end Aschbacher

end CFSG.OddStandard.Solomon75

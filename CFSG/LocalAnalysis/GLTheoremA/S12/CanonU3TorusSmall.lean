module

public import CFSG.LocalAnalysis.GLTheoremA.S12.CanonU3TorusCore
public import CFSG.LocalAnalysis.GLTheoremA.S12.CanonU3Small
public import CFSG.LocalAnalysis.GLTheoremA.S12.CanonU3Exc

public section

namespace CFSG.LocalAnalysis.GLTheoremA.CanonU3

open CFSG.Open CFSG.LocalAnalysis.GLTheoremA.Y10GField

section Certs


theorem u3TorusCoreOn_lin : U3TorusCoreOn FamLin := by
  refine u3TorusCoreOn_of_false fun S _ _ labL β n J hF h => ?_
  rcases hF with hA | ⟨hD, h3⟩ | ⟨hD, h2⟩
  · exact false_of_A h hA
  · exact false_of_D3 h hD h3
  · exact false_of_twD2 h hD h2

theorem u3TorusCoreOn_symp : U3TorusCoreOn FamSymp := by
  refine u3TorusCoreOn_of_false fun S _ _ labL β n J hF h => ?_
  rcases hF with hB | hC | hB2
  · exact false_of_B_or_C h (Or.inl hB)
  · exact false_of_B_or_C h (Or.inr hC)
  · exact false_of_B2der h hB2

theorem u3TorusCoreOn_orthPlus : U3TorusCoreOn fun lab => lab.tag = .D ∧ lab.rank ≠ 3 := by
  refine u3TorusCoreOn_of_false fun S _ _ labL β n J hF h => ?_
  exact false_of_D_of_rank_ne_three h hF.1 hF.2

end Certs

section ExcCerts


theorem u3TorusCoreOn_exc_of_ne : U3TorusCoreOn fun lab => FamExc lab ∧ lab.tag ≠ .twF4 := by
  refine u3TorusCoreOn_of_false fun S _ _ labL β n J hF h => ?_
  obtain ⟨hE, hne⟩ := hF
  rcases hE with hE6 | hE7 | hE8 | hF4 | hTwE6 | hTriD4 | hG2 | hG2der | hTwB2 | hTwF4 |
    hTwF4der
  · exact false_of_E6 h hE6
  · exact false_of_E7_or_E8 h (Or.inl hE7)
  · exact false_of_E7_or_E8 h (Or.inr hE8)
  · exact false_of_F4 h hF4
  · exact false_of_twE6 h hTwE6
  · exact false_of_triD4 h hTriD4
  · exact false_of_G2 h hG2
  · exact false_of_G2der h hG2der
  · exact false_of_twB2 h hTwB2
  · exact (hne hTwF4).elim
  · exact false_of_twF4der h hTwF4der

end ExcCerts

end CFSG.LocalAnalysis.GLTheoremA.CanonU3

module

public import CFSG.LocalAnalysis.GLTheoremA.S12.CanonU3TorusSmall
public import CFSG.LocalAnalysis.GLTheoremA.S12.CanonU3TorusTwF4
public import CFSG.LocalAnalysis.GLTheoremA.S12.CanonU3TorusUni
public import CFSG.LocalAnalysis.GLTheoremA.S12.CanonU3TorusOrthMinus
public import CFSG.LocalAnalysis.GLTheoremA.S12.CanonU3TorusBridge

public section

namespace CFSG.LocalAnalysis.GLTheoremA.CanonU3

open CFSG.Open
open CFSG.LocalAnalysis.GLTheoremA.Y10GField
open CFSG.LocalAnalysis.GLTheoremA.CanonU3.OrthMinus

section TwF4Certs


theorem u3TorusCoreOn_twF4 : U3TorusCoreOn fun lab => lab.tag = .twF4 := by
  intro S _ _ labL β β₁ β₂ n J hF hT
  exact (false_of_twF4_torus hT.core hF hT.innDiagKind₁ hT.innDiagKind₂ hT.pow_three₁
    hT.pow_three₂ hT.commute₁ hT.commute₂ hT.commute₁₂ hT.moves₁ hT.moves₂).elim

end TwF4Certs

section ExcCerts


theorem u3TorusCoreOn_exc : U3TorusCoreOn FamExc := by
  intro S _ _ labL β β₁ β₂ n J hF hT
  by_cases h : labL.tag = .twF4
  · exact u3TorusCoreOn_twF4 S labL β β₁ β₂ n J h hT
  · exact u3TorusCoreOn_exc_of_ne S labL β β₁ β₂ n J ⟨hF, h⟩ hT

end ExcCerts

section OrthCerts


theorem u3TorusCoreOn_orth : U3TorusCoreOn FamOrth := by
  intro S _ _ labL β β₁ β₂ n J hF hT
  unfold FamOrth at hF
  rcases hF with hD | hD
  · exact u3TorusCoreOn_orthPlus S labL β β₁ β₂ n J hD hT
  · exact u3TorusCoreOn_orthMinus S labL β β₁ β₂ n J hD hT

end OrthCerts

section CoreCerts


theorem u3TorusCoreS_holds : U3TorusCoreS :=
  u3TorusCoreS_of_families u3TorusCoreOn_lin u3TorusCoreOn_uni u3TorusCoreOn_symp
    u3TorusCoreOn_orth u3TorusCoreOn_exc

end CoreCerts

section SubcompCerts


theorem u3SubcompTorus_holds : U3SubcompTorus :=
  u3SubcompTorus_of_core CFSG.LocalAnalysis.GLTheoremA.CanonSubcomp.subcompField_holds
    u3TorusCoreS_holds

end SubcompCerts

end CFSG.LocalAnalysis.GLTheoremA.CanonU3

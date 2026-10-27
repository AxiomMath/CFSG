module

public import CFSG.LocalAnalysis.GLTheoremA.S12.CanonU3Bridge
public import CFSG.LocalAnalysis.GLTheoremA.S12.CanonU3Small
public import CFSG.LocalAnalysis.GLTheoremA.S12.CanonU3OrthMinus
public import CFSG.LocalAnalysis.GLTheoremA.S12.CanonU3Uni
public import CFSG.LocalAnalysis.GLTheoremA.S12.CanonU3Exc

public section

namespace CFSG.LocalAnalysis.GLTheoremA.CanonU3

open CFSG.LocalAnalysis.GLTheoremA.Y10GField

section OrthCerts


theorem u3CoreOn_orth : U3CoreOn FamOrth := by
  intro S _ _ labL β n J hF h
  unfold FamOrth at hF
  rcases hF with hD | hD
  · exact u3CoreOn_orthPlus S labL β n J hD h
  · exact u3CoreOn_orthMinus S labL β n J hD h

end OrthCerts

section CoreCerts


theorem u3CoreS_holds : U3CoreS :=
  u3CoreS_of_families u3CoreOn_lin u3CoreOn_uni u3CoreOn_symp u3CoreOn_orth u3CoreOn_exc

end CoreCerts

section SubcompCerts


theorem u3SubcompL_holds : U3SubcompL :=
  u3SubcompL_of_core CFSG.LocalAnalysis.GLTheoremA.CanonSubcomp.subcompField_holds u3CoreS_holds

end SubcompCerts

end CFSG.LocalAnalysis.GLTheoremA.CanonU3

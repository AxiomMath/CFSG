module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.H248FactsM
public import CFSG.LocalAnalysis.GLTheoremB.Lemma911Certified
import CFSG.LocalAnalysis.GLTheoremA.CatA.H248L227Res

public section

namespace CFSG.LocalAnalysis.GLTheoremA.H248

open CFSG.LocalAnalysis.GLTheoremB


theorem l227FactM_holds : L227FactM :=
  H248L227.l227FactM_of_outer fun _ _ _ hQ _ hJ => outer_solvable_of_component_certified hQ hJ

end CFSG.LocalAnalysis.GLTheoremA.H248

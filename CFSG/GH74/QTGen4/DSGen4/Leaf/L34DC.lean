module

public import CFSG.GH74.QTGen4.DSGen4.Leaf.L34DCStd
public import CFSG.GH74.QTGen4.DSGen4.Leaf.L34DCSwap
public import CFSG.GH74.QTGen4.DSGen4.Leaf.L34DCWitnessB
public import CFSG.GH74.QTGen4.DSGen4.Leaf.L34DCWitnessC

public section

namespace CFSG.GH74.QTGen4.DSGen4

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.H13
  CFSG.Quasithin.Background.Harris.F112S3Big
open scoped commutatorElement

theorem leafL34DC : LeafL34DC :=
  L34.leafL34DC_of_std fun F _ _ _ hq =>
    have h : L34.DCStd F := L34.dcStd_of_witnesses hq (L34.witnessLn hq)
      (fun κ => L34.witnessPt_of_witnessLn κ (L34.witnessLn hq κ))
    ⟨h, L34.dcStdSwap_of_dcStd h⟩

end CFSG.GH74.QTGen4.DSGen4

module

public import CFSG.Certificates.Kernel.Spor.HBfsKeys
public import CFSG.LocalAnalysis.EvenSporadicStandard.HypOne.SylowFour

public section

namespace CFSG.KS.MulH

open CFSG.Sporadic.Th.Native CFSG.Sporadic.Schreier.Native CFSG.Sporadic.SmallOddCore.Native

theorem fiveConjOK_of_tree {n cap f : Nat} {cg cgInv : Array Table} {x : Table} (hcap : 5 ≤ cap)
    (h : CFSG.KS.HBfs.FiveTree (hkey n) (fun l y => conjT n cg[l]! cgInv[l]! y) cg.size f [x]) :
    CFSG.EvenSporadicStandard.HypOne.fiveConjOK n cap cg cgInv x = true := by
  unfold CFSG.EvenSporadicStandard.HypOne.fiveConjOK
  obtain ⟨h1, h2⟩ := conjTree_keys n cg cgInv x cap
  simp only [h1, h2, Bool.and_true, decide_eq_true_eq]
  rw [conjClosureH_eq]
  exact CFSG.KS.HBfs.five_of_tree hcap h

end CFSG.KS.MulH

end

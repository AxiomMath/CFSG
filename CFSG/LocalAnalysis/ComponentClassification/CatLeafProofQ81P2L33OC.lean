module

public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofQ81P2L33OCLin
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofQ81P2L33OCUni
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofQ81P2L33OCSpInv

public section

namespace CFSG.ComponentClassification.HarrisLit.L33.OC

open CFSG Subgroup CFSG.Assembly.LowTwoRank

theorem oddClsRow_psp :
    OddClsRow .PSp :=
  oddClsRow_psp_of oddSpHigherRow

theorem twoNilpFor_odd_of_orth
    (hO : OddClsRow .POmegaOdd) (hP : OddClsRow .POmegaPlus) (hM : OddClsRow .POmegaMinus) :
    TwoNilpFor fun Y _ => ∃ t n p f, p ≠ 2 ∧ StatedClassicalModel Y t n p f :=
  twoNilpFor_odd_of_rows oddClsRow_psl oddClsRow_psu oddClsRow_psp hO hP hM

end CFSG.ComponentClassification.HarrisLit.L33.OC

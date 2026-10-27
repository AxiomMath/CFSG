module

import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7.SEFive.AltTenGood
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7.SEFive.AltTenPermThree
public import CFSG.RankThree.PartOne.S12.InputsSec15

public section

open CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7.SEFive
open CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7.SEFive.AltTen

namespace CFSG.LocalAnalysis.AGL81TheoremCD.Section14.KFTwo

theorem pPrimeCore_three_eq_bot_of_altTen {X : Type} [Group X] [Finite X]
    (hO : CFSG.pPrimeCore 5 X = ⊥) {N : Subgroup X}
    (hN : CFSG.RankThree.PartOne.IsStronglyPEmbedded 5 N)
    (e : ↥(CFSG.generalizedFitting X) ≃* alternatingGroup (Fin 10)) :
    CFSG.pPrimeCore 3 ↥N = ⊥ := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  refine pPrimeCore_eq_bot_of_altTen (q := 3) hO hN e
    (fun B hB Q hQ hQB hnorm => eq_bot_of_normalized_by_alt_prod_three hB hQ hQB hnorm)

end CFSG.LocalAnalysis.AGL81TheoremCD.Section14.KFTwo

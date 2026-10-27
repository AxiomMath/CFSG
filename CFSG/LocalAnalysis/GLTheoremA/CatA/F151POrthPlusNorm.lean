module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.F151Defs
import CFSG.LocalAnalysis.GLTheoremA.CatA.F151POrthNormCore
import CFSG.LocalAnalysis.GLTheoremA.CatA.F151PIso
import CFSG.LocalAnalysis.GLTheoremA.CatA.T171ShapeFamInOrthTransModel
import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.LayerNonsolv3

public section

namespace CFSG.LocalAnalysis.GLTheoremA.F151

theorem orthPlusNorm_holds : OrthPlusNorm := by
  intro n m K _ _ hn hcard p hp hp2
  haveI : CharP K 2 := by
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    haveI : Fintype K := Fintype.ofFinite K
    exact charP_of_card_eq_prime_pow (R := K) (p := 2) (f := m)
      (by simpa only [Nat.card_eq_fintype_card] using hcard)
  obtain ⟨hQ, hT⟩ :=
    CFSG.ClassicalGroups.Orthogonal.regular_quadPlus (K := K) (n := n) (by omega)
  refine shapeModelNormIso_holds
    (CFSG.RankThree.Classical2.ProjOrthDerived (CFSG.LieType.Universal.Spin.quadPlus n K))
    (CFSG.Assembly.LargeEvenProj (CFSG.Assembly.LargeEvenOmega
      (CFSG.Assembly.LargeEvenQPlus K n)))
    (CFSG.LocalAnalysis.GLTheoremA.T171Sh.orthModelEquivPlus n K).symm p ?_
  exact shapeModelNormAt_projOrth_two (K := K) (V := Fin n ⊕ Fin n → K)
    (Q := CFSG.LieType.Universal.Spin.quadPlus n K) hp hp2 hQ hT

end CFSG.LocalAnalysis.GLTheoremA.F151

end

module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.F151Defs
import CFSG.LocalAnalysis.GLTheoremA.CatA.F151POrthNormCore
import CFSG.LocalAnalysis.GLTheoremA.CatA.F151PIso
import CFSG.LocalAnalysis.GLTheoremA.CatA.T171ShapeFamInOrthTransModel
import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.LayerNonsolv3

public section

namespace CFSG.LocalAnalysis.GLTheoremA.F151

open CFSG.RankThree.Classical2 (ProjOrthDerived)
open CFSG.LieType.Universal.Spin (quadMinus)

theorem orthMinusNorm_holds : OrthMinusNorm := by
  intro n m K _ _ hn hK b c hirr p hp hp2
  letI : Fintype K := Fintype.ofFinite K
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : CharP K 2 :=
    charP_of_card_eq_prime_pow (p := 2) (f := m)
      (by rw [← Nat.card_eq_fintype_card]; exact hK)
  obtain ⟨hQ, hT⟩ :=
    CFSG.ClassicalGroups.Orthogonal.regular_quadMinus (n := n) (K := K) (b := b) (c := c)
      hn hirr
  have hcore : ShapeModelNormAt (ProjOrthDerived (quadMinus n K b c)) p :=
    shapeModelNormAt_projOrth_two (K := K)
      (V := Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2 → K) (Q := quadMinus n K b c) hp hp2 hQ hT
  exact shapeModelNormIso_holds (ProjOrthDerived (quadMinus n K b c))
    (CFSG.Assembly.LargeEvenProj (CFSG.Assembly.LargeEvenOmega
      (CFSG.Assembly.LargeEvenQMinus (n - 1) b c)))
    (T171Sh.orthModelEquivMinus n K b c).symm p hcore

end CFSG.LocalAnalysis.GLTheoremA.F151

end

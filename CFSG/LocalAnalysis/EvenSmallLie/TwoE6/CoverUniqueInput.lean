module

public import CFSG.LocalAnalysis.EvenSmallLie.TwoE6.CoverLevi

public section

namespace CFSG.EvenSmallLie.TwoE6

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Chevalley.C2E6Overlap
  CFSG.LieType.Steinberg.Exceptional
open scoped MatrixGroups

@[expose] def LeviA2DiagInput
    : Prop :=
  ∃ (e : SL(3, GaloisField 2 (2 * 1)) →* twistedE6Group 2 1)
    (g : GL (Fin 3) (GaloisField 2 (2 * 1)))
    (u : (a : Fin TwistTag.E6.foldedTag.rank) → (orbitField TwistTag.E6 K barHom a)ˣ),
    Function.Injective e ∧ e.range = (twistedE6Datum 2 1).levi levi34 ∧
    (g : Matrix (Fin 3) (Fin 3) (GaloisField 2 (2 * 1))).det ≠ 1 ∧
    ∀ A B : SL(3, GaloisField 2 (2 * 1)),
      (B : Matrix (Fin 3) (Fin 3) (GaloisField 2 (2 * 1))) =
        (g : Matrix (Fin 3) (Fin 3) (GaloisField 2 (2 * 1))) *
          (A : Matrix (Fin 3) (Fin 3) (GaloisField 2 (2 * 1))) *
          ((g⁻¹ : GL (Fin 3) (GaloisField 2 (2 * 1))) : Matrix (Fin 3) (Fin 3) _) →
      compatDiagAutHom TwistTag.E6 K barHom u (isogenyStd (e A)) = isogenyStd (e B)

end CFSG.EvenSmallLie.TwoE6

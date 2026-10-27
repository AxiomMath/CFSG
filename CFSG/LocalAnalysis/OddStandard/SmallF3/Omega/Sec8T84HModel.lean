module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec6Defs
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec4Basic

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

@[expose] def Sec8T84ModelSylow : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module (ZMod 3) V] [FiniteDimensional (ZMod 3) V]
    (Q : QuadraticForm (ZMod 3) V) (hQ : Q.Nondegenerate),
    Module.finrank (ZMod 3) V = 6 → quadSign Q = -1 →
      ∀ P : Subgroup (ProjOrth Q), IsSylow2Of P (omegaProj hQ) →
        omega1 P = P ∧
          ∀ B : Subgroup (ProjOrth Q), IsNormalE16In P B →
            ∃ D : Subgroup (ProjOrth Q), D ≤ P ∧ B ⊓ D = ⊥ ∧ B ⊔ D = P

end CFSG.OddStandard.SmallF3.Omega

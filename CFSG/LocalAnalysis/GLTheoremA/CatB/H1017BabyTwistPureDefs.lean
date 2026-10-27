module

public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.BThreeFi23Reps
public import CFSG.Monster.GMS.Facts.BabyTables
public import CFSG.Monster.GMS.Defs

public section

namespace CFSG.LocalAnalysis.GLTheoremA.H1017

open CFSG.Open CFSG.Blueprint CFSG.Monster.GMS CFSG.HardMathSupport.Timmesfeld.SporadicBalance


@[expose] def BabyNoPureFourAt (k : Fin 4) : Prop :=
  ∀ t : NativeSporadic.B, BabyInv k t → ∀ D : Subgroup NativeSporadic.B,
    D ≤ Subgroup.centralizer ({t} : Set NativeSporadic.B) → IsElemAbelian 3 D →
      Nat.card D = 3 ^ 4 → ∃ x ∈ D, x ≠ 1 ∧ ¬ IsConj x (BThreeFi23.phiB (BThreeFi23.t3 1))

end CFSG.LocalAnalysis.GLTheoremA.H1017

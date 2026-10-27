module

public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.BSevenLocalCore
public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.BThreeFi23Census
public import CFSG.HardMathSupport.Solomon.Coordinator.YS08.Spor.FixCount
public import CFSG.Monster.B.Pinned.GeneratorDeterminants
public import CFSG.Monster.B.Dyadic.BinElim
public import Certificates.Data.CFSGNative.MonsterB.BinaryRank
public import Certificates.Data.CFSGNative.SectionRank.B
public import Mathlib.Data.Nat.Notation
public import CFSG.Blueprint.NativeSporadic
public import Mathlib.LinearAlgebra.Matrix.Rank
import Certificates.Kernel.BabyMonster.SeedRanks
public import Mathlib.RingTheory.AdjoinRoot
public import Mathlib.RingTheory.AlgebraTower
public import Mathlib.LinearAlgebra.Projection
public import Certificates.Certificate3109
public import Certificates.Certificate17451
public import Certificates.Certificate214034
public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Fi23Sylow
public import Certificates.Certificate13622Base

public section

namespace CFSG.HardMathSupport.Timmesfeld.SporadicBalance.BSevenLocal

open CFSG.HardMathSupport.Timmesfeld.SporadicBalance.BThreeFi23

theorem rk_phiB_t3_one : rk (phiB (t3 1)) = 2916 ∧ orderOf (phiB (t3 1)) = 3 :=
  Certificates.certificate17451

end CFSG.HardMathSupport.Timmesfeld.SporadicBalance.BSevenLocal

module

public import CFSG.HardMathSupport.Solomon.Coordinator.B3B.BNFCheck
public import CFSG.HardMathSupport.Solomon.Coordinator.B3B.BNFProd
public import CFSG.HardMathSupport.Cooperstein.Coordinator.FFSporadic.BHeis
public import Certificates.Certificate36920
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
public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.BSevenLocalCore

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.B3B

open CFSG.SectionRank CFSG.SectionRank.Native CFSG.Blueprint
open CFSG.HardMathSupport.Cooperstein.Coordinator.FFSporadic
open CFSG.HardMathSupport.Meierfrankenfeld.FFToolkit

theorem bNF_holds :
    ∃ (x y : Fin 4 → NativeSporadic.B) (z : NativeSporadic.B) (g : Fin 2 → NativeSporadic.B),
      HeisCfg 3 4 x y z ∧ (∀ i, y i ^ 3 = 1) ∧
      (∀ (k : Fin 2) (j : Fin 4),
        g k * x j * (g k)⁻¹ = nfProd x y z (nfXData.getD (4 * k.val + j.val) [])) ∧
      (∀ (k : Fin 2) (j : Fin 4),
        g k * y j * (g k)⁻¹ = nfProd x y z (nfYData.getD (4 * k.val + j.val) [])) ∧
      (∀ k : Fin 2, g k * z * (g k)⁻¹ = z ^ 2) ∧
      CFSG.HardMathSupport.Timmesfeld.SporadicBalance.BSevenLocal.rk z = 2916 :=
  Certificates.certificate36920

end CFSG.HardMathSupport.Solomon.Coordinator.B3B

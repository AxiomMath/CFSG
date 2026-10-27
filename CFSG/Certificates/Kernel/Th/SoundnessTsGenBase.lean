
module

public import CFSG.Certificates.Kernel.Th.Gen.Ts
public import CFSG.Sporadic.ThSchreier.LocalOrbitInputs
public meta import CFSG.Sporadic.ThSchreier.WordsBase
public meta import CFSG.Sporadic.ThSchreier.LocalDataBase
public import CFSG.Sporadic.ThSchreier.TwoCentralizerInputs
public meta import CFSG.Sporadic.ThSchreier.OrbitCheck819Base
public meta import CFSG.Sporadic.Th.Max3.PacketBase
import CFSG.Certificates.Kernel.Common.Generalize
import CFSG.Certificates.Kernel.Th.Spec.Big
import CFSG.Certificates.Kernel.Th.Spec.Loops
import CFSG.Certificates.Kernel.Th.Spec.Parse
import CFSG.Certificates.Kernel.Th.Spec.Seed
import CFSG.Certificates.Kernel.Th.Spec.Ts2313Base
import CFSG.Certificates.Kernel.Th.Spec.Ts2324Base
import CFSG.Certificates.Kernel.Th.Spec.TsLeaves
public import CFSG.Certificates.Kernel.Common.LceS
public import CFSG.Certificates.Kernel.Common.RelNorm
public import CFSG.Certificates.Kernel.Th.S.HswTC
public import CFSG.Certificates.Kernel.Th.S.OutS
public import CFSG.Certificates.Kernel.Th.S.TcS
import CFSG.Certificates.Kernel.Th.Spec.GjBase
import CFSG.Sporadic.ThSchreier.UASpaceInputs

@[expose] public section

namespace CFSG.KC.Th.Soundness

open CFSG CFSG.Sporadic CFSG.Sporadic.ThSchreier CFSG.Sporadic.Th CFSG.Sporadic.Th.Native
open CFSG.Sporadic.Th.Max3 Pointwise
open CFSG.Sporadic.Th.Max3
open CFSG.KC.Th.Gen CFSG.Sporadic.Th CFSG.Sporadic.ThSchreier

#kc_generalize TsGen2313 (sA sB rows : String) (px py tp tpa tla : Array ℕ)
    using [CFSG.Sporadic.Th.Native.seedA ↦ sA, CFSG.Sporadic.Th.Native.seedB ↦ sB,
      CFSG.Sporadic.ThSchreier.localRowsTxt ↦ rows, CFSG.Sporadic.ThSchreier.localPermX ↦ px,
      CFSG.Sporadic.ThSchreier.localPermY ↦ py, CFSG.Sporadic.ThSchreier.localTreePts ↦ tp,
      CFSG.Sporadic.ThSchreier.localTreePar ↦ tpa, CFSG.Sporadic.ThSchreier.localTreeLab ↦ tla]
    from [CFSG.Blueprint.NativeSporadic.ThSeed1, CFSG.Blueprint.NativeSporadic.ThSeed2] :
  (((∀ i < 2457, ∀ j < 2457, i < j → localRowNats.getD i 0 ≠ localRowNats.getD j 0) ∧
      localRowNats.getD 0 0 = 0x6accc40834b0cc5bb7315609695cfa8d6f195e2ac39c3b4260e97d31187fa2 ∧
      (∀ i < 2457, localPermX[i]! < 2457 ∧ localPermY[i]! < 2457 ∧
        (frApply (frTable rowsLX) (localRowV4 i)).beq (localRowV4 localPermX[i]!) = true ∧
        (frApply (frTable (CFSG.Sporadic.Th.Native.mulRows rowsLY rowsLY)) (localRowV4 i)).beq
          (localRowV4 localPermY[i]!) = true)
    )
    ∧ (localTreePts[0]! = 0 ∧ (∀ k < 2457, localTreePts[k]! < 2457) ∧
      (∀ i < 2457, ∃ k < 2457, localTreePts[k]! = i) ∧
      (∀ k < 2457, 1 ≤ k → localTreePar[k]! < k ∧
        ((localTreeLab[k]! = 1 ∧ localPermX[localTreePts[localTreePar[k]!]!]! = localTreePts[k]!) ∨
         (localTreeLab[k]! = 2 ∧ localPermY[localTreePts[localTreePar[k]!]!]! = localTreePts[k]!)))
    )
    ∧ (eqRows (CFSG.Sporadic.Th.Native.mulRows rowsLX rowsLX) idRows = true ∧ eqRows rowsLX idRows = false ∧
      eqRows (CFSG.Sporadic.Th.Native.mulRows (CFSG.Sporadic.Th.Native.mulRows rowsLY rowsLY) rowsLY) idRows = true ∧
      eqRows rowsLY idRows = false ∧
      eqRows (powRows (CFSG.Sporadic.Th.Native.mulRows rowsLX rowsLY) 21) idRows = true ∧
      eqRows (powRows (CFSG.Sporadic.Th.Native.mulRows rowsLX rowsLY) 3) idRows = false ∧
      eqRows (powRows (CFSG.Sporadic.Th.Native.mulRows rowsLX rowsLY) 7) idRows = false ∧
      imageKey (frTable rowsLX) wKeyRow = wKeyRow ∧
      imageKey (frTable (CFSG.Sporadic.Th.Native.mulRows rowsLY rowsLY)) wKeyRow = wKeyRow
    ))

end CFSG.KC.Th.Soundness

end

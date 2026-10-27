
module

public import CFSG.Certificates.Kernel.Th.SoundnessTsBase

public import CFSG.Certificates.Kernel.Th.Gen.Ts
public import CFSG.Sporadic.ThSchreier.LocalOrbitInputs
public meta import CFSG.Sporadic.ThSchreier.WordsBase1
public meta import CFSG.Sporadic.ThSchreier.LocalData
public import CFSG.Sporadic.ThSchreier.TwoCentralizerInputs
public meta import CFSG.Sporadic.ThSchreier.OrbitCheck819Base
public meta import CFSG.Sporadic.Th.Max3.PacketBase1
import CFSG.Certificates.Kernel.Th.SoundnessTsGen
public import CFSG.Sporadic.Th.Max3.Data

public section

namespace CFSG.KC.Th.Soundness

open CFSG.KC.Th.Gen CFSG.Sporadic.Th CFSG.Sporadic.ThSchreier

open CFSG CFSG.Sporadic CFSG.Sporadic.ThSchreier CFSG.Sporadic.Th CFSG.Sporadic.Th.Native in
open CFSG.Sporadic.Th.Max3 Pointwise in
theorem ts_sound2313 (D : TsData) (_hA : Native.seedA = String.ofList D.ThSeed_LA)
    (_hB : Native.seedB = String.ofList D.ThSeed_LB)
    (_hR : localRowsTxt = String.ofList D.ThTs_Lrows)
    (_hX : localPermX = (natsOf (String.ofList D.ThTs_Lpx)).toArray)
    (_hY : localPermY = (natsOf (String.ofList D.ThTs_Lpy)).toArray)
    (_hP : localTreePts = (natsOf (String.ofList D.ThTs_Ltp)).toArray)
    (_hQ : localTreePar = (natsOf (String.ofList D.ThTs_Ltpa)).toArray)
    (_hL : localTreeLab = (natsOf (String.ofList D.ThTs_Ltla)).toArray)
    (_h : tsChk D = true) : ((∀ i < 2457, ∀ j < 2457, i < j → localRowNats.getD i 0 ≠ localRowNats.getD j 0) ∧
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
    ) :=
  TsGen2313.inst (ts_sound2313_gen _ _ _ _ _ _ _ _ D _hA _hB _hR _hX _hY _hP _hQ _hL _h)

open CFSG CFSG.Sporadic CFSG.Sporadic.ThSchreier CFSG.Sporadic.Th CFSG.Sporadic.Th.Native in
open CFSG.Sporadic.Th.Max3 in
theorem ts_sound2324 (D : TsData) (_hA : Native.seedA = String.ofList D.ThSeed_LA)
    (_hB : Native.seedB = String.ofList D.ThSeed_LB) (_h : tsChk D = true) :
 eqRows (CFSG.Sporadic.Th.Native.mulRows (hRows centWord0) rowsT) (CFSG.Sporadic.Th.Native.mulRows rowsT (hRows centWord0)) = true ∧
    eqRows (CFSG.Sporadic.Th.Native.mulRows (hRows centWord1) rowsT) (CFSG.Sporadic.Th.Native.mulRows rowsT (hRows centWord1)) = true ∧
    (∀ R ∈ twoRowsList, eqRows (CFSG.Sporadic.Th.Native.mulRows R (invRows R)) idRows = true ∧
      (invRows R).size = 248 ∧ ∀ r ∈ invRows R, r.wf = true) ∧
    twoRowsList.length = 10 ∧
    eqRows (signedRows (tupleRows twoRowsList) origWord0) rowsLX = true ∧
    eqRows (signedRows (tupleRows twoRowsList) origWord1) rowsLY = true ∧
    eqRows rowsTwoR rowsE217 = true ∧ eqRows rowsTwoR idRows = false ∧
    eqRows rowsTwoR rowsZ = false :=
  TsGen2324.inst (ts_sound2324_gen _ _ D _hA _hB _h)

end CFSG.KC.Th.Soundness


module

public import CFSG.Certificates.Kernel.Th.SoundnessMax3GenBase

public import CFSG.Certificates.Kernel.Th.Gen.Max3
public import CFSG.Sporadic.Th.Max3.OddCaseInputs
public import Mathlib
public import CFSG.Blueprint.NativeSporadic
public import CFSG.Blueprint.MatrixSeedIdentification
public import CFSG.Sporadic.Th.F2Spec
public import CFSG.Certificates.SchreierStabilizerGenerators
public import Certificates.Data.CFSGNative.Th.Certificate
public import CFSG.Sporadic.Th.Max3.InvolutionsBase1
public import CFSG.Sporadic.Th.Max3.AllConjInputs
public import CFSG.Sporadic.Th.Max3.QuotientBase1
public import CFSG.Sporadic.Th.Max3.InvolutionsInputs
public import CFSG.Sporadic.Th.Max3.CoreBase1
public import CFSG.Sporadic.Th.Max3.PacketInputs
public import CFSG.Sporadic.Th.Max3.AltNine
public import CFSG.LocalAnalysis.ComponentClassification.PresentationLocalCarmichael
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PCore.PCore
public import CFSG.Sporadic.Th.Max3.QuotientInputs
public import CFSG.Sporadic.Th.Max3.Data
import CFSG.Certificates.Kernel.Common.Generalize
import CFSG.Certificates.Kernel.Th.Max3S.R9014
import CFSG.Certificates.Kernel.Th.Max3S.R10088
import CFSG.Certificates.Kernel.Th.Max3S.R10089
import CFSG.Certificates.Kernel.Th.Max3S.R10090
import CFSG.Certificates.Kernel.Th.Max3S.R10091
import CFSG.Certificates.Kernel.Th.Max3S.R10092
import CFSG.Certificates.Kernel.Th.Max3S.Regs
import CFSG.Certificates.Kernel.Th.Max3S.RegsExtra
import CFSG.Certificates.Kernel.Th.Max3S.DefsExtraBase
import CFSG.Certificates.Kernel.Th.Max3S.R10088Base
import CFSG.Certificates.Kernel.Th.Max3S.R10089Base
import CFSG.Certificates.Kernel.Th.Max3S.R10090Base
import CFSG.Certificates.Kernel.Th.Max3S.R10091Base
import CFSG.Certificates.Kernel.Th.Max3S.R9014Base
import CFSG.Certificates.Kernel.Th.Spec.Mirror

public section

namespace CFSG.KC.Th.Soundness

open CFSG CFSG.Sporadic CFSG.Sporadic.Th
open Native Max3
open CFSG.Sporadic.Th.Native CFSG.Sporadic.Th.Max3.AllConj CFSG.Sporadic.Th.Max3
open CFSG.Sporadic.Th.Native CFSG.Sporadic.Th.Max3 CFSG.Sporadic.Th.Max3.InvRep
open CFSG.Sporadic.Th.Native CFSG.Sporadic.Th.Max3.Packet CFSG.Sporadic.Th.Max3
open CFSG.ComponentClassification.PresentationLocal CFSG.Sporadic.Th.Native CFSG.Sporadic.Th.Max3
  CFSG.Sporadic.Th.Max3.AltQuot
open CFSG.Sporadic.Th.Native CFSG.Sporadic.Th.Max3
open CFSG.KC.Th.Gen CFSG.Sporadic.Th

#kc_generalize Max3Gen10092 (sA sB : String)
    using [CFSG.Sporadic.Th.Native.seedA ↦ sA, CFSG.Sporadic.Th.Native.seedB ↦ sB]
    from [CFSG.Blueprint.NativeSporadic.ThSeed1, CFSG.Blueprint.NativeSporadic.ThSeed2] :
  ((eqRows (powRows Slp.rowsT8 3) idRows = true ∧
      eqRows (powRows Slp.rowsS8' 19) idRows = true ∧
      eqRows (CFSG.Sporadic.Th.Native.mulRows rowsX rowsX) idRows = true ∧
      eqRows (powRows rowsY 6) idRows = true ∧
      eqRows rowsZ rowsA = true ∧
      eqRows rowsZ idRows = false ∧
      eqRows (CFSG.Sporadic.Th.Native.mulRows rowsZ rowsZ) idRows = true ∧
      eqRows (CFSG.Sporadic.Th.Native.mulRows rowsZ rowsX) (CFSG.Sporadic.Th.Native.mulRows rowsX rowsZ) = true ∧
      eqRows (CFSG.Sporadic.Th.Native.mulRows rowsZ rowsY) (CFSG.Sporadic.Th.Native.mulRows rowsY rowsZ) = true ∧
      (∀ i : Fin 8, eqRows (CFSG.Sporadic.Th.Native.mulRows (rowsQ i) (rowsQ i)) idRows = true) ∧
      (∀ i : Fin 8, eqRows (CFSG.Sporadic.Th.Native.mulRows rowsZ (rowsQ i)) (CFSG.Sporadic.Th.Native.mulRows (rowsQ i) rowsZ) = true) ∧
      (∀ i j : Fin 8, eqRows (CFSG.Sporadic.Th.Native.mulRows (rowsQ i) (rowsQ j))
        (CFSG.Sporadic.Th.Native.mulRows (CFSG.Sporadic.Th.Native.mulRows (rowsQ j) (rowsQ i)) (powRows rowsZ (c i j).val)) = true) ∧
      (∀ i : Fin 8, eqRows (CFSG.Sporadic.Th.Native.mulRows (CFSG.Sporadic.Th.Native.mulRows rowsX (rowsQ i)) rowsX)
        (rowsNf (xz i).val fun j => (xv i j).val) = true) ∧
      (∀ i : Fin 8, eqRows (CFSG.Sporadic.Th.Native.mulRows (CFSG.Sporadic.Th.Native.mulRows rowsY (rowsQ i)) (powRows rowsY 5))
        (rowsNf (yz i).val fun j => (yv i j).val) = true))
    ∧ (∀ k l : Fin 512, l < k → eqRows (rowsNfAt k) (rowsNfAt l) = false))

#kc_generalize Max3Gen10091 (sA sB : String)
    using [CFSG.Sporadic.Th.Native.seedA ↦ sA, CFSG.Sporadic.Th.Native.seedB ↦ sB]
    from [CFSG.Blueprint.NativeSporadic.ThSeed1, CFSG.Blueprint.NativeSporadic.ThSeed2] :
  ((∀ k : CarmichaelIndex 9,
        eqRows (powRows (carmRows k) 3) (rowsNfIdx (carmCubeIdx k)) = true) ∧
      (∀ j k : CarmichaelIndex 9, j.1 < k.1 →
        eqRows (powRows (CFSG.Sporadic.Th.Native.mulRows (carmRows j) (carmRows k)) 2) (rowsNfIdx (carmPairIdx j k)) =
          true) ∧
      eqRows (CFSG.Sporadic.Th.Native.mulRows rowsX waRows) (rowsNfIdx 299) = true ∧
      eqRows (CFSG.Sporadic.Th.Native.mulRows (powRows rowsY 5) wbRows) (rowsNfIdx 201) = true ∧
      eqRows rowsCommXQ idRows = false ∧ eqRows rowsCommXQ rowsZ = false)

#kc_generalize Max3Gen10090 (sA sB : String)
    using [CFSG.Sporadic.Th.Native.seedA ↦ sA, CFSG.Sporadic.Th.Native.seedB ↦ sB]
    from [CFSG.Blueprint.NativeSporadic.ThSeed1, CFSG.Blueprint.NativeSporadic.ThSeed2] :
  (eqRows (signedWordRows coreZWord) rowsZ = true ∧
      ∀ i : Fin 8, eqRows (signedWordRows (coreGeneratorWords i))
        (CFSG.Sporadic.Th.Native.mulRows (rowsQ i) (powRows rowsZ (qPShift i).val)) = true)

#kc_generalize Max3Gen10089 (sA sB : String)
    using [CFSG.Sporadic.Th.Native.seedA ↦ sA, CFSG.Sporadic.Th.Native.seedB ↦ sB]
    from [CFSG.Blueprint.NativeSporadic.ThSeed1, CFSG.Blueprint.NativeSporadic.ThSeed2] :
  ((∀ k : Fin 512, eqRows (CFSG.Sporadic.Th.Native.mulRows (rowsNfAt k) (rowsNfAt k)) idRows = false ∨
        eqRows (rowsNfAt k) idRows = true ∨ eqRows (rowsNfAt k) rowsZ = true ∨
        eqRows (CFSG.Sporadic.Th.Native.mulRows (rowsConj k) (rowsQ 0)) (CFSG.Sporadic.Th.Native.mulRows (rowsNfAt k) (rowsConj k)) = true) ∧
      (∀ k : Fin 512, eqRows (CFSG.Sporadic.Th.Native.mulRows (rowsXNf k) (rowsXNf k)) idRows = false ∨
        eqRows (CFSG.Sporadic.Th.Native.mulRows (rowsNfAt (uIdx k)) rowsX) (CFSG.Sporadic.Th.Native.mulRows (rowsXNf k) (rowsNfAt (uIdx k))) =
          true) ∧
      (∀ k : Fin 512, eqRows (CFSG.Sporadic.Th.Native.mulRows (rowsDNf k) (rowsDNf k)) idRows = false))

#kc_generalize Max3Gen10088 (sA sB : String)
    using [CFSG.Sporadic.Th.Native.seedA ↦ sA, CFSG.Sporadic.Th.Native.seedB ↦ sB]
    from [CFSG.Blueprint.NativeSporadic.ThSeed1, CFSG.Blueprint.NativeSporadic.ThSeed2] :
  (eqRows (CFSG.Sporadic.Th.Native.mulRows rowsFusionQ0 (rowsQ 0)) (CFSG.Sporadic.Th.Native.mulRows rowsA rowsFusionQ0) = true ∧
      eqRows (CFSG.Sporadic.Th.Native.mulRows rowsFusionX rowsX) (CFSG.Sporadic.Th.Native.mulRows rowsA rowsFusionX) = true)

#kc_generalize Max3Gen9014 (sA sB : String)
    using [CFSG.Sporadic.Th.Native.seedA ↦ sA, CFSG.Sporadic.Th.Native.seedB ↦ sB]
    from [CFSG.Blueprint.NativeSporadic.ThSeed1, CFSG.Blueprint.NativeSporadic.ThSeed2] :
  ((∀ i : Fin 4, eqRows (CFSG.Sporadic.Th.Native.mulRows (rowsEQ i) (rowsEQ i)) idRows = true) ∧
      (∀ i j : Fin 4, eqRows (CFSG.Sporadic.Th.Native.mulRows (rowsEQ i) (rowsEQ j)) (CFSG.Sporadic.Th.Native.mulRows (rowsEQ j) (rowsEQ i)) = true) ∧
      (∀ i : Fin 4, eqRows (CFSG.Sporadic.Th.Native.mulRows (rowsFQ i) (rowsEQ i))
        (CFSG.Sporadic.Th.Native.mulRows (CFSG.Sporadic.Th.Native.mulRows (rowsEQ i) rowsZ) (rowsFQ i)) = true) ∧
      (∀ i j : Fin 4, i ≠ j →
        eqRows (CFSG.Sporadic.Th.Native.mulRows (rowsFQ j) (rowsEQ i)) (CFSG.Sporadic.Th.Native.mulRows (rowsEQ i) (rowsFQ j)) = true))

theorem max3_sound10092_gen (sA sB : String) (D : Max3Data) (_hA : sA = String.ofList D.ThSeed_LA)
    (_hB : sB = String.ofList D.ThSeed_LB) (_h : max3Chk D = true) : Max3Gen10092 sA sB := by
  subst _hA _hB
  exact fun _ _ => CFSG.KC.Th.Max3S.c10092_of D _h (CFSG.KC.Th.Max3S.regOK_of D _h)

theorem max3_sound10091_gen (sA sB : String) (D : Max3Data) (_hA : sA = String.ofList D.ThSeed_LA)
    (_hB : sB = String.ofList D.ThSeed_LB) (_h : max3Chk D = true) : Max3Gen10091 sA sB := by
  subst _hA _hB
  exact fun _ => CFSG.KC.Th.Max3S.c10091_of D _h (CFSG.KC.Th.Max3S.regOK_of D _h)
    (CFSG.KC.Th.Max3S.regExtra_of D _h)

theorem max3_sound10090_gen (sA sB : String) (D : Max3Data) (_hA : sA = String.ofList D.ThSeed_LA)
    (_hB : sB = String.ofList D.ThSeed_LB) (_h : max3Chk D = true) : Max3Gen10090 sA sB := by
  subst _hA _hB
  exact fun _ => CFSG.KC.Th.Max3S.c10090_of D _h (CFSG.KC.Th.Max3S.regOK_of D _h)

theorem max3_sound10089_gen (sA sB : String) (D : Max3Data) (_hA : sA = String.ofList D.ThSeed_LA)
    (_hB : sB = String.ofList D.ThSeed_LB) (_h : max3Chk D = true) : Max3Gen10089 sA sB := by
  subst _hA _hB
  exact fun _ _ => CFSG.KC.Th.Max3S.c10089_of D _h (CFSG.KC.Th.Max3S.regOK_of D _h)

theorem max3_sound10088_gen (sA sB : String) (D : Max3Data) (_hA : sA = String.ofList D.ThSeed_LA)
    (_hB : sB = String.ofList D.ThSeed_LB) (_h : max3Chk D = true) : Max3Gen10088 sA sB := by
  subst _hA _hB
  exact fun _ => CFSG.KC.Th.Max3S.c10088_of D _h (CFSG.KC.Th.Max3S.regOK_of D _h)
    (CFSG.KC.Th.Max3S.regExtra_of D _h)

theorem max3_sound9014_gen (sA sB : String) (D : Max3Data) (_hA : sA = String.ofList D.ThSeed_LA)
    (_hB : sB = String.ofList D.ThSeed_LB) (_h : max3Chk D = true) : Max3Gen9014 sA sB := by
  subst _hA _hB
  exact fun _ => CFSG.KC.Th.Max3S.c9014_of D _h (CFSG.KC.Th.Max3S.regOK_of D _h)
    (CFSG.KC.Th.Max3S.regExtra_of D _h)

end CFSG.KC.Th.Soundness

end

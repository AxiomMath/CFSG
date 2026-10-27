
module


public import CFSG.Certificates.Kernel.Th.Gen.Max3
public import CFSG.Sporadic.Th.Max3.OddCaseInputs
public import CFSG.Sporadic.Th.Max3.AllConjInputs
public import CFSG.Sporadic.Th.Max3.InvolutionsInputs
public import CFSG.Sporadic.Th.Max3.QuotientInputs
import CFSG.Certificates.Kernel.Th.SoundnessMax3Gen

public section

namespace CFSG.KC.Th.Soundness

open CFSG.KC.Th.Gen CFSG.Sporadic.Th

open CFSG.Sporadic.Th.Native CFSG.Sporadic.Th.Max3 in
theorem max3_sound10092 (D : Max3Data) (_hA : Native.seedA = String.ofList D.ThSeed_LA)
    (_hB : Native.seedB = String.ofList D.ThSeed_LB) (_h : max3Chk D = true) :

    (eqRows (powRows Slp.rowsT8 3) idRows = true ∧
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
    ∧ (∀ k l : Fin 512, l < k → eqRows (rowsNfAt k) (rowsNfAt l) = false) :=
  Max3Gen10092.inst (max3_sound10092_gen _ _ D _hA _hB _h)

open CFSG.ComponentClassification.PresentationLocal CFSG.Sporadic.Th.Native CFSG.Sporadic.Th.Max3
  CFSG.Sporadic.Th.Max3.AltQuot in
theorem max3_sound10091 (D : Max3Data) (_hA : Native.seedA = String.ofList D.ThSeed_LA)
    (_hB : Native.seedB = String.ofList D.ThSeed_LB) (_h : max3Chk D = true) :

    (∀ k : CarmichaelIndex 9,
        eqRows (powRows (carmRows k) 3) (rowsNfIdx (carmCubeIdx k)) = true) ∧
      (∀ j k : CarmichaelIndex 9, j.1 < k.1 →
        eqRows (powRows (CFSG.Sporadic.Th.Native.mulRows (carmRows j) (carmRows k)) 2) (rowsNfIdx (carmPairIdx j k)) =
          true) ∧
      eqRows (CFSG.Sporadic.Th.Native.mulRows rowsX waRows) (rowsNfIdx 299) = true ∧
      eqRows (CFSG.Sporadic.Th.Native.mulRows (powRows rowsY 5) wbRows) (rowsNfIdx 201) = true ∧
      eqRows rowsCommXQ idRows = false ∧ eqRows rowsCommXQ rowsZ = false :=
  Max3Gen10091.inst (max3_sound10091_gen _ _ D _hA _hB _h)

open CFSG.Sporadic.Th.Native CFSG.Sporadic.Th.Max3.Packet CFSG.Sporadic.Th.Max3 in
theorem max3_sound10090 (D : Max3Data) (_hA : Native.seedA = String.ofList D.ThSeed_LA)
    (_hB : Native.seedB = String.ofList D.ThSeed_LB) (_h : max3Chk D = true) :

    eqRows (signedWordRows coreZWord) rowsZ = true ∧
      ∀ i : Fin 8, eqRows (signedWordRows (coreGeneratorWords i))
        (CFSG.Sporadic.Th.Native.mulRows (rowsQ i) (powRows rowsZ (qPShift i).val)) = true :=
  Max3Gen10090.inst (max3_sound10090_gen _ _ D _hA _hB _h)

open CFSG.Sporadic.Th.Native CFSG.Sporadic.Th.Max3 CFSG.Sporadic.Th.Max3.InvRep in
theorem max3_sound10089 (D : Max3Data) (_hA : Native.seedA = String.ofList D.ThSeed_LA)
    (_hB : Native.seedB = String.ofList D.ThSeed_LB) (_h : max3Chk D = true) :

    (∀ k : Fin 512, eqRows (CFSG.Sporadic.Th.Native.mulRows (rowsNfAt k) (rowsNfAt k)) idRows = false ∨
        eqRows (rowsNfAt k) idRows = true ∨ eqRows (rowsNfAt k) rowsZ = true ∨
        eqRows (CFSG.Sporadic.Th.Native.mulRows (rowsConj k) (rowsQ 0)) (CFSG.Sporadic.Th.Native.mulRows (rowsNfAt k) (rowsConj k)) = true) ∧
      (∀ k : Fin 512, eqRows (CFSG.Sporadic.Th.Native.mulRows (rowsXNf k) (rowsXNf k)) idRows = false ∨
        eqRows (CFSG.Sporadic.Th.Native.mulRows (rowsNfAt (uIdx k)) rowsX) (CFSG.Sporadic.Th.Native.mulRows (rowsXNf k) (rowsNfAt (uIdx k))) =
          true) ∧
      (∀ k : Fin 512, eqRows (CFSG.Sporadic.Th.Native.mulRows (rowsDNf k) (rowsDNf k)) idRows = false) :=
  Max3Gen10089.inst (max3_sound10089_gen _ _ D _hA _hB _h)

open CFSG.Sporadic.Th.Native CFSG.Sporadic.Th.Max3.AllConj CFSG.Sporadic.Th.Max3 in
theorem max3_sound10088 (D : Max3Data) (_hA : Native.seedA = String.ofList D.ThSeed_LA)
    (_hB : Native.seedB = String.ofList D.ThSeed_LB) (_h : max3Chk D = true) :

    eqRows (CFSG.Sporadic.Th.Native.mulRows rowsFusionQ0 (rowsQ 0)) (CFSG.Sporadic.Th.Native.mulRows rowsA rowsFusionQ0) = true ∧
      eqRows (CFSG.Sporadic.Th.Native.mulRows rowsFusionX rowsX) (CFSG.Sporadic.Th.Native.mulRows rowsA rowsFusionX) = true :=
  Max3Gen10088.inst (max3_sound10088_gen _ _ D _hA _hB _h)

open CFSG CFSG.Sporadic CFSG.Sporadic.Th in
open Native Max3 in
theorem max3_sound9014 (D : Max3Data) (_hA : Native.seedA = String.ofList D.ThSeed_LA)
    (_hB : Native.seedB = String.ofList D.ThSeed_LB) (_h : max3Chk D = true) :
 (∀ i : Fin 4, eqRows (CFSG.Sporadic.Th.Native.mulRows (rowsEQ i) (rowsEQ i)) idRows = true) ∧
      (∀ i j : Fin 4, eqRows (CFSG.Sporadic.Th.Native.mulRows (rowsEQ i) (rowsEQ j)) (CFSG.Sporadic.Th.Native.mulRows (rowsEQ j) (rowsEQ i)) = true) ∧
      (∀ i : Fin 4, eqRows (CFSG.Sporadic.Th.Native.mulRows (rowsFQ i) (rowsEQ i))
        (CFSG.Sporadic.Th.Native.mulRows (CFSG.Sporadic.Th.Native.mulRows (rowsEQ i) rowsZ) (rowsFQ i)) = true) ∧
      (∀ i j : Fin 4, i ≠ j →
        eqRows (CFSG.Sporadic.Th.Native.mulRows (rowsFQ j) (rowsEQ i)) (CFSG.Sporadic.Th.Native.mulRows (rowsEQ i) (rowsFQ j)) = true) :=
  Max3Gen9014.inst (max3_sound9014_gen _ _ D _hA _hB _h)

end CFSG.KC.Th.Soundness

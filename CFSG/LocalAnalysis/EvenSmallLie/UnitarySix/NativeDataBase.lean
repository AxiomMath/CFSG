
module

public import CFSG.Fischer.T46Simple
public import CFSG.Sporadic.Schreier.MathieuOddCoreClasses
public import CFSG.Sporadic.Schreier.MathieuOddCoreOuter
public import CFSG.LocalAnalysis.ComponentClassification.M12CoverAutCentralizerData
public import CFSG.ClassicalInvolution.SmallCases.Sporadic.SetOrbitTools
public import CFSG.LocalAnalysis.ComponentClassification.PSL3FourCertificate
public meta import Certificates.Data.CFSGNative.F4.T46Simple
public meta import Certificates.Data.CFSGNative.Fi22.Local
public meta import Certificates.Data.CFSGNative.Th.Tables
public meta import Certificates.Data.CFSGNative.Th.Orbit
public import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.NativeDataInputs

@[expose] public section

namespace CFSG.EvenSmallLie.UnitarySix

open CFSG.Certificates CFSG.Certificates.Native CFSG.Sporadic.Th CFSG.Sporadic.Th.Native
open CFSG.Sporadic.Schreier CFSG.Sporadic.Schreier.Native CFSG.Sporadic.Fi22.Native
open CFSG.ComponentClassification.M12Cover CFSG.Sporadic.Schreier.Co3.Native
open CFSG.Monster.B.Co2.Native CFSG.PSL3Four.Native

@[expose] def tableFun (T : Table) (i : Fin 693) : Fin 693 :=
  ⟨ap T i % 693, Nat.mod_lt _ (by norm_num)⟩

theorem involOK_spec {T : Table} (h : involOK T = true) {i : ℕ} (hi : i < 693) :
    ap T i < 693 ∧ ap T (ap T i) = i := by
  simp only [involOK, Bool.and_eq_true, invoOK, allIn_eq_true, decide_eq_true_eq,
    beq_iff_eq] at h
  exact ⟨h.1 i (Nat.zero_le _) hi, h.2 i (Nat.zero_le _) hi⟩

theorem tableFun_tableFun {T : Table} (h : involOK T = true) (i : Fin 693) :
    tableFun T (tableFun T i) = i := by
  obtain ⟨h1, h2⟩ := involOK_spec h i.2
  apply Fin.ext
  simp only [tableFun]
  rw [Nat.mod_eq_of_lt h1, h2, Nat.mod_eq_of_lt i.2]

@[expose] def involPerm (T : Table) (h : involOK T = true) : Equiv.Perm (Fin 693) :=
  ⟨tableFun T, tableFun T, tableFun_tableFun h, tableFun_tableFun h⟩

@[expose] def letterArrs : Array (Array ℕ) :=
  (Array.range 46).map fun k => (letterT k).map UInt32.toNat

@[expose] def arrOf (g : Equiv.Perm (Fin 693)) : Array ℕ := Array.ofFn fun i => (g i : ℕ)

@[expose] def aWords : List (List ℤ) :=
  [[1], [12], [46], [17, 46, 8, -46, -17], [35], [34, 46, 21, -46, -34], [32, 46, 19, -46, -32],
    [8, 46, 36, 21, 46, 2, -46, -21, -36, -46, -8], [39, 46, 25, -46, -39]]

@[expose] def kWords : List (List ℤ) :=
  [[4, 11, 21, 34], [16, 46, 2, -46, -16, 7, 46, 2, -46, -7], [16, 46, 2, -46, -16, 46, 18, -46]]

@[expose] def tWords : List (List ℤ) :=
  [[16, 46, 2, -46, -16, 7, 46, 2, -46, -7], [16, 46, 2, -46, -16, 46, 18, -46],
    [32, 46, 27, -46, -32, 37, 46, 19, -46, -37], [32, 46, 27, -46, -32, 42, 46, 23, -46, -42]]

@[expose] def fixA : List ℕ :=
  [0, 11, 12, 27, 42, 205, 206, 217, 218, 233, 248, 427, 438, 439, 454, 469, 648, 659, 660, 675,
    690]

@[expose] def sRepWords : List (List ℤ) :=
  [[4], [5], [1], [3, 7], [8, 9], [5, 7], [2, 3], [1, 9], [5, 6], [2, 4], [1, 4], [5, 9], [3, 4],
    [6, 9], [7, 8], [3, 4, 8], [3, 6, 9], [2, 7, 8], [1, 3, 6], [1, 5, 8], [2, 5, 9], [1, 5, 7],
    [2, 5, 6], [2, 4, 5], [2, 3, 9], [11], [12], [13], [10], [4, 12], [1, 13], [9, 11], [12, 13],
    [10, 11], [9, 10], [5, 10, 11], [3, 12, 13], [10, 13, 10, 13], [11, 13, 11, 13],
    [10, 12, 10, 12], [10, 4, 12, 10, 12], [3, 11, 13, 11, 13], [3, 10, 13, 10, 13]]

@[expose] def sConjWords : List (List ℤ) :=
  [[], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [],
    [], [18], [45], [45], [18], [45], [45], [18], [45], [18], [18], [18], [45], [45], [45], [45],
    [45], [45], [45]]

@[expose] def beta : Array ℕ :=
  #[205, 11, 217, 438, 659, 0, 206, 427, 648, 12, 218, 439, 660, 27, 233, 454, 675, 42, 248, 469,
    690, 381, 23, 405, 319, 626, 1, 383, 297, 604, 25, 407, 321, 628, 19, 401, 315, 622, 40, 422,
    336, 643]

@[expose] def orbitRecord : Array (List ℕ) × Array ℕ × Array ℕ := hashSearch letterArrs fixA 900

end CFSG.EvenSmallLie.UnitarySix

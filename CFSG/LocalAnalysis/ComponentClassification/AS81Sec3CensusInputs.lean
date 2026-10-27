module

public import CFSG.Fischer.F4
public import Certificates.Data.CFSGNative.PSL3Four.Basic
public meta import CFSG.Fischer.F4
public meta import Certificates.Data.CFSGNative.PSL3Four.Basic
public meta import Mathlib
public import Mathlib

public section

namespace CFSG.ComponentClassification.AS81.Census

open CFSG.PSL3Four.Native CFSG.Fischer

@[expose] def decodeV (n : Nat) : Fin 6 → F4 := fun i =>
  ⟨⟨n / 4 ^ i.val % 4, Nat.mod_lt _ (by decide)⟩⟩

@[expose] def encodeV (v : Fin 6 → F4) : Nat :=
  (v 0).code.val + 4 * ((v 1).code.val + 4 * ((v 2).code.val + 4 * ((v 3).code.val +
    4 * ((v 4).code.val + 4 * (v 5).code.val))))

@[expose] def applyF (M : Array Nat) (v : Fin 6 → F4) : Fin 6 → F4 := fun i =>
  v 0 * decodeV M[0]! i + v 1 * decodeV M[1]! i + v 2 * decodeV M[2]! i +
    v 3 * decodeV M[3]! i + v 4 * decodeV M[4]! i + v 5 * decodeV M[5]! i

@[expose] def applyC (M : Array Nat) (n : Nat) : Nat := encodeV (applyF M (decodeV n))

@[expose] def qF (v : Fin 6 → F4) : F4 :=
  v 0 * v 0 + v 0 * v 1 + v 1 * v 1 + v 2 * v 3 + v 4 * v 4 + v 4 * v 5 + v 5 * v 5

@[expose] def matMul (A B : Array Nat) : Array Nat := Array.ofFn (n := 6) fun i => applyC A B[i]!

@[expose] def idMat : Array Nat := #[1, 4, 16, 64, 256, 1024]

@[expose] def wordMat (M : Array (Array Nat)) (w : List Nat) : Array Nat :=
  w.foldl (fun r a => matMul r M[a]!) idMat

@[expose] def isomOK (M : Array Nat) : Bool :=
  M.size == 6 && allBelow 6 (fun i => decide (M[i]! < 4096)) &&
    allBelow 4096 fun n => decide (qF (applyF M (decodeV n)) = qF (decodeV n)) &&
      (n == 0 || applyC M n != 0)

@[expose] def isF2 (v : Nat) : Bool := allBelow 6 fun i => decide (v / 4 ^ i % 4 < 2)

@[expose] def f2Mat (M : Array Nat) : Bool := allBelow 6 fun i => isF2 M[i]!

@[expose] def f2code (b : Nat) : Nat :=
  b % 2 + 4 * (b / 2 % 2 + 4 * (b / 4 % 2 + 4 * (b / 8 % 2 + 4 * (b / 16 % 2 + 4 * (b / 32 % 2)))))

@[expose] def f2point (v : Nat) : Nat :=
  v % 4 + 2 * (v / 4 % 4 + 2 * (v / 16 % 4 + 2 * (v / 64 % 4 + 2 * (v / 256 % 4 +
    2 * (v / 1024 % 4)))))

@[expose] def f2perm (M : Array Nat) : Tab :=
  Array.ofFn (n := 64) fun b => f2point (applyC M (f2code b.val))

@[expose] def formStep (M : Array Nat) (t : Tab) : Tab :=
  ((t.toList.map (applyC M)).mergeSort (· ≤ ·)).toArray

@[expose] def actTab (M : Array Nat) : Array Nat := Array.ofFn (n := 4096) fun n => applyC M n.val

@[expose] def formStepT (T : Array Nat) (t : Tab) : Tab :=
  ((t.toList.map fun n => T[n]!).mergeSort (· ≤ ·)).toArray

@[expose] def n0Tab : Tab := (((List.range 64).map f2code).mergeSort (· ≤ ·)).toArray

@[expose] def x0M : Array Nat := #[4, 5, 16, 64, 256, 1024]

@[expose] def tauM : Array Nat := #[1, 5, 16, 64, 256, 1024]

@[expose] def cM : Array Nat := #[1, 4, 16, 64, 256, 1280]

@[expose] def b3M : Array Nat := #[1, 4, 64, 1104, 1344, 1024]

@[expose] def b5M : Array Nat := #[1, 4, 336, 16, 1040, 256]

@[expose] def g1M : Array Nat := #[1364, 5, 1301, 1360, 320, 1280]

@[expose] def g2M : Array Nat := #[1296, 1364, 1297, 1301, 1280, 1088]

@[expose] def g1iM : Array Nat := #[69, 65, 1044, 84, 340, 1364]

@[expose] def g2iM : Array Nat := #[17, 80, 257, 85, 1365, 1109]

@[expose] def rootsM : Array (Array Nat × Array Nat) := #[
  (#[1, 4, 16, 64, 256, 1024], #[1, 4, 16, 64, 256, 1024]),
  (#[224, 288, 780, 522, 256, 1249], #[224, 288, 780, 522, 256, 1249]),
  (#[643, 1532, 1579, 899, 65, 185], #[643, 1532, 1579, 899, 65, 185]),
  (#[3457, 865, 3812, 1073, 1072, 3380], #[320, 21, 201, 4018, 2012, 391]),
  (#[2431, 2940, 3947, 2327, 65, 2885], #[415, 1532, 1349, 159, 746, 983]),
  (#[1038, 2391, 2514, 3731, 87, 1009], #[1037, 3515, 2017, 1873, 182, 865]),
  (#[1553, 1651, 3399, 1371, 2792, 2138], #[2656, 759, 3409, 2327, 2773, 2138]),
  (#[2656, 759, 3409, 2327, 2773, 2138], #[1553, 1651, 3399, 1371, 2792, 2138]),
  (#[2299, 2572, 1452, 156, 842, 3848], #[2811, 2060, 1196, 156, 842, 3906]),
  (#[2811, 2060, 1196, 156, 842, 3906], #[2299, 2572, 1452, 156, 842, 3848]),
  (#[1229, 2949, 3598, 3505, 87, 2528], #[1229, 3221, 1838, 1584, 758, 403]),
  (#[1037, 3515, 2017, 1873, 182, 865], #[1038, 2391, 2514, 3731, 87, 1009]),
  (#[412, 3191, 1041, 899, 2773, 934], #[1293, 1651, 3625, 1607, 2115, 2868]),
  (#[3652, 4085, 255, 1543, 2243, 2491], #[725, 4081, 3783, 963, 2591, 299]),
  (#[3172, 1872, 1713, 1317, 87, 329], #[1556, 3408, 1413, 1257, 93, 403]),
  (#[1, 4, 128, 48, 256, 1024], #[1, 4, 128, 48, 256, 1024]),
  (#[2431, 2940, 3625, 2774, 65, 2885], #[415, 1388, 1333, 159, 746, 935]),
  (#[4048, 65, 1281, 1217, 1, 3605], #[256, 1361, 61, 260, 860, 588]),
  (#[725, 4081, 3783, 963, 2591, 299], #[3652, 4085, 255, 1543, 2243, 2491]),
  (#[1556, 3408, 1413, 1257, 93, 403], #[3172, 1872, 1713, 1317, 87, 329])]

@[expose] def goodData : List (Nat × Array Nat × Array Nat) := [
  (3, #[340, 337, 336, 277, 256, 1344], #[1361, 337, 1028, 1089, 1088, 1108]),
  (15, #[4, 5, 16, 64, 256, 1024], #[4, 5, 1104, 1360, 272, 320]),
  (17, #[1, 1109, 1089, 1041, 1361, 337], #[1024, 341, 1045, 1093, 5, 1108])]

@[expose] def badData : List (Nat × Nat × List Nat) := [
  (1, 0, [3, 1, 1, 1, 3]), (1, 1, [2, 2]), (2, 0, [2, 1, 0, 3]), (2, 1, [2, 2]),
  (4, 0, [2, 0, 3, 3]), (4, 1, [3, 3, 1, 3, 3]), (5, 0, [3, 0, 0, 3]), (5, 1, [2, 0, 3]),
  (6, 0, [3, 0, 1, 0, 3]), (6, 1, [3, 3, 3, 3]), (7, 0, [2, 0, 1, 0, 2]), (7, 1, [3, 3, 3, 3]),
  (8, 0, [2, 2]), (8, 1, [3, 1, 1, 2]), (9, 0, [2, 2]), (9, 1, [3, 3, 0, 2]),
  (10, 0, [3, 0, 1, 2]), (10, 1, [2, 2, 2, 2]), (11, 0, [3, 3, 1, 2]), (11, 1, [2, 1, 3, 3]),
  (12, 0, [3, 0, 0, 2]), (12, 1, [3, 3]), (13, 0, [3, 1, 0, 3]), (13, 1, [2, 2, 0, 3]),
  (14, 0, [2, 1, 2]), (14, 1, [2, 2, 1, 2]), (16, 0, [2, 1, 2]), (16, 1, [3, 1, 1, 1, 2]),
  (18, 0, [2, 1, 0, 2]), (18, 1, [3, 0, 1, 2]), (19, 0, [3, 0, 3]), (19, 1, [2, 2, 2, 2, 2])]

@[expose] def goodOrbits : List Nat := [3, 15, 17]

@[expose] def lEnum : Enum := enumBFS 64 #[f2perm g1M, f2perm g2M] 20160

@[expose] def g1T : Array Nat := actTab g1M

@[expose] def g2T : Array Nat := actTab g2M

@[expose] def b3T : Array Nat := actTab b3M

@[expose] def b5T : Array Nat := actTab b5M

@[expose] def orbitStep (k : Nat) (t : Tab) : Tab := formStepT (if k = 0 then g1T else g2T) t

@[expose] def rootForm (j : Nat) : Tab := formStep (rootsM[j]!).1 n0Tab

@[expose] def orbits : Array Enum :=
  (Array.range 20).map fun j => bfs orbitStep 2 (rootForm j) 20160

@[expose] def formIndex : Std.HashMap Tab Nat :=
  (List.range 20).foldl (fun m j => (orbits[j]!).tabs.foldl (fun m t => m.insert t j) m) {}

@[expose] def matsOK : Bool :=
  [x0M, tauM, cM, b3M, b5M, g1M, g2M, g1iM, g2iM].all (fun M => isomOK M && f2Mat M) &&
    matMul g1M g1iM == idMat && matMul g2M g2iM == idMat && matMul cM x0M == matMul x0M cM &&
    matMul tauM tauM == idMat &&
    rootsM.size == 20 && (rootsM[0]!).1 == idMat &&
    allBelow 20 fun j => isomOK (rootsM[j]!).1 && isomOK (rootsM[j]!).2 &&
      matMul (rootsM[j]!).1 (rootsM[j]!).2 == idMat

@[expose] def lOK : Bool :=
  enumOK 64 #[f2perm g1M, f2perm g2M] lEnum && lEnum.tabs.size == 20160 &&
    !(lEnum.tabs.contains (f2perm tauM)) && !(lEnum.tabs.contains (f2perm cM))

@[expose] def formsOK : Bool :=
  orbits.size == 20 && allBelow 20 (fun j => treeOK orbitStep 2 (rootForm j) orbits[j]!) &&
    (List.range 20).foldl (fun s j => s + (orbits[j]!).tabs.size) 0 == 48960 &&
    allBelow 20 fun j => (orbits[j]!).tabs.all fun t => formIndex.get? t == some j

@[expose] def m1OK : Bool :=
  allBelow 20 fun j => (orbits[j]!).tabs.all fun t =>
    !(formStepT b3T t == t && formStepT b5T t == t) || t == n0Tab

@[expose] def goodOK : Bool :=
  goodData.map (·.1) == goodOrbits &&
  goodData.all fun (j, y, l) =>
    decide (j < 20) && formStep x0M (rootForm j) == rootForm j &&
    isomOK y && f2Mat y && isomOK l && f2Mat l && matMul x0M l == matMul l y &&
    matMul (rootsM[j]!).1 y == matMul x0M (rootsM[j]!).1

@[expose] def badOK : Bool :=
  (List.range 20).all (fun j => j == 0 || goodOrbits.contains j ||
    ((List.range 2).all fun e => badData.any fun (j', e', _) => j' == j && e' == e)) &&
  badData.all fun (j, e, w) =>
    decide (j < 20) && decide (e < 2) && w.all (fun a => decide (a < 4)) &&
    (let h := if e = 0 then (rootsM[j]!).1 else matMul (rootsM[j]!).1 tauM
     let hi := if e = 0 then (rootsM[j]!).2 else matMul tauM (rootsM[j]!).2
     let t := formStep (wordMat #[g1M, g2M, h, hi] w) n0Tab
     matMul h hi == idMat && goodOrbits.any fun j' => (orbits[j']!).tabs.contains t)

@[expose] def censusCheck : Bool := matsOK && lOK && formsOK && m1OK && goodOK && badOK

end CFSG.ComponentClassification.AS81.Census

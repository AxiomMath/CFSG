module

public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.SpBranchT1Data
public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.SpBranchChar

public section

namespace CFSG.EvenSmallLie.OmegaEight.SpBranch

@[expose] def s2Surv : List (ℕ × ℕ × ℕ) :=
  [(0, 16, 0), (0, 21, 0), (0, 26, 0), (0, 31, 0), (1, 16, 24), (1, 21, 24), (1, 26, 24),
    (1, 31, 24)]

@[expose] def s2K (j : ℕ) : ℕ := (s2Surv.getD j (0, 0, 0)).1
@[expose] def s2M (j : ℕ) : ℕ := (s2Surv.getD j (0, 0, 0)).2.1
@[expose] def s2Z (j : ℕ) : ℕ := (s2Surv.getD j (0, 0, 0)).2.2

@[expose] def s2F (j : ℕ) : Array ℕ := sFTab (s2K j) (s2M j)

variable (mul : ℕ → ℕ → ℕ) (inv : ℕ → ℕ)

@[expose] def s2InSp (vec : Array ℕ) (c : ℕ) : Bool := !chiV 10 768 vec[c]!

@[expose] def s2Rel (vec : Array ℕ) (c i : ℕ) : ℕ :=
  vec[mul c (t1Gens.getD i 0)]! ^^^ vec[c]! ^^^ 2 ^ i

@[expose] def s2RelV (vec : Array ℕ) (W : Array (ℕ × ℕ)) : List ℕ :=
  (List.range 1024).filter fun r =>
    decide (W[r]!.1 < 131072) && decide (W[r]!.2 < 10) && s2Rel mul vec W[r]!.1 W[r]!.2 == r

@[expose] def s2CharOK (tr : Array ℕ × Array ℕ × Array ℕ × Array ℕ) (I O RV : List ℕ) : Bool :=
  treeOK mul t1Gens 131072 (fun c => tr.1[c]!) (fun c => tr.2.1[c]!) (fun c => tr.2.2.1[c]!) &&
    vecOK 131072 (fun c => tr.1[c]!) (fun c => tr.2.1[c]!) (fun c => tr.2.2.2[c]!) &&
    ((List.range 1024).all fun b =>
      b == 512 || b == 768 || RV.any (fun r => chiV 10 b r) ||
      (I.filter fun c => !chiV 10 b tr.2.2.2[c]!).length != 3839 ||
      (O.filter fun c => !chiV 10 b tr.2.2.2[c]!).length != 41216) &&
    (List.range 131072).all fun c => (!chiV 10 512 tr.2.2.2[c]!) == decide (c < 65536)

@[expose] def s2Iota : List (List ℕ) := [
  [8, 1124, 1036, 3158, 10520, 5632, 16544, 24, 32, 1536, 2315, 2304, 128, 11520, 18560, 102144],
  [8, 1124, 1036, 3158, 10520, 5632, 16568, 24, 32, 1536, 2315, 2304, 128, 11520, 18584, 102144],
  [3, 8260, 8231, 24669, 3352, 5640, 2208, 24, 32, 1536, 2315, 2304, 128, 11552, 18592, 102272],
  [3, 8260, 8231, 24669, 3352, 5640, 2232, 24, 32, 1536, 2315, 2304, 128, 11552, 18616, 102272],
  [8, 1124, 1076, 3190, 10552, 4107, 16512, 24, 32, 1536, 2315, 2304, 128, 11520, 18560, 102144],
  [8, 1124, 1076, 3190, 10552, 4107, 16536, 24, 32, 1536, 2315, 2304, 128, 11520, 18584, 102144],
  [3, 8260, 8223, 24701, 3384, 4099, 2176, 24, 32, 1536, 2315, 2304, 128, 11552, 18592, 102272],
  [3, 8260, 8223, 24701, 3384, 4099, 2200, 24, 32, 1536, 2315, 2304, 128, 11552, 18616, 102272]
]

@[expose] def s2IotaTab (im : List ℕ) : Array ℕ :=
  let W := (List.range 128).toArray.map fun e => wprodN mul 7 (fun l => im.getD l 0) e
  let L := (List.range 512).toArray.map fun a => wprodN mul 9 (fun i => im.getD (7 + i) 0) a
  (List.range 65536).toArray.map fun x =>
    mul (if sAutData.nfE x < 128 then W[sAutData.nfE x]! else 0)
      (if sAutData.nfA x < 512 then L[sAutData.nfA x]! else 0)

@[expose] def s2B (ι : Array ℕ) (F : ℕ → ℕ) (w c : ℕ) : ℕ :=
  if c < 65536 then ι[F c]! else mul (ι[F (c - 65536)]!) w

@[expose] def s2Cj0 : Array ℕ := (List.range 131072).toArray.map fun v => cconj mul inv v 3

@[expose] def s2V (cj0 : Array ℕ) (B : ℕ → ℕ) : List ℕ :=
  let bb := t1Gens.map fun g => B (B g)
  (List.range 131072).filter fun v =>
    cj0[v]! == bb.getD 0 0 &&
      ((List.range 10).all fun i => cconj mul inv v (t1Gens.getD i 0) == bb.getD i 0) && B v == v

@[expose] def s2Canon : List (List (ℕ × ℕ × ℕ × ℕ)) := [
  [(0, 0, 65536, 67072), (0, 4, 65536, 67072), (0, 8, 65536, 67072), (0, 12, 65536, 67072),
    (1, 0, 65536, 67072), (1, 4, 65536, 67072), (1, 8, 65536, 67072), (1, 12, 65536, 67072)],
  [(0, 0, 65536, 67072), (0, 4, 65536, 67072), (0, 8, 65536, 67072), (0, 12, 65536, 67072),
    (1, 0, 65536, 67072), (1, 4, 65536, 67072), (1, 8, 65536, 67072), (1, 12, 65536, 67072)],
  [(0, 2, 65536, 2304), (0, 6, 65536, 2304), (0, 10, 65536, 2304), (0, 14, 65536, 2304),
    (1, 2, 65536, 2304), (1, 6, 65536, 2304), (1, 10, 65536, 2304), (1, 14, 65536, 2304)],
  [(0, 2, 65536, 2304), (0, 6, 65536, 2304), (0, 10, 65536, 2304), (0, 14, 65536, 2304),
    (1, 2, 65536, 2304), (1, 6, 65536, 2304), (1, 10, 65536, 2304), (1, 14, 65536, 2304)],
  [(0, 2, 65536, 67072), (0, 6, 65536, 67072), (0, 10, 65536, 67072), (0, 14, 65536, 67072),
    (0, 18, 65536, 67072), (0, 22, 65536, 67072), (0, 26, 65536, 67072), (0, 30, 65536, 67072)],
  [(0, 2, 65536, 67072), (0, 6, 65536, 67072), (0, 10, 65536, 67072), (0, 14, 65536, 67072),
    (0, 19, 65536, 67072), (0, 23, 65536, 67072), (0, 27, 65536, 67072), (0, 31, 65536, 67072)],
  [(0, 0, 65560, 2304), (0, 4, 65560, 2304), (0, 8, 65560, 2304), (0, 12, 65560, 2304),
    (0, 18, 65560, 2304), (0, 22, 65560, 2304), (0, 26, 65560, 2304), (0, 30, 65560, 2304)],
  [(0, 0, 65560, 2304), (0, 4, 65560, 2304), (0, 8, 65560, 2304), (0, 12, 65560, 2304),
    (0, 19, 65560, 2304), (0, 23, 65560, 2304), (0, 27, 65560, 2304), (0, 31, 65560, 2304)]
]

@[expose] def fpCount : ℕ := ((List.range 65536).filter fun c => fpArr[c]!).length

@[expose] def s2BasicCheck : Bool :=
  fpCount == 128 && (kInv sMul 65536).length == 3839 && (kOrd4 sMul 65536).length == 41216

end CFSG.EvenSmallLie.OmegaEight.SpBranch

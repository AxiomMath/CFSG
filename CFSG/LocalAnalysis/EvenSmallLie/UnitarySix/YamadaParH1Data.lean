module

public import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.YamadaParLin

public section

namespace CFSG.EvenSmallLie.UnitarySix.YamadaPar

@[expose] def genBits : Fin 3 → Array ℕ
  | 0 => #[1, 2, 5, 10, 81, 162, 64, 128]
  | 1 => #[80, 160, 64, 128, 145, 226, 229, 122]
  | 2 => #[29, 38, 91, 173, 5, 10, 4, 8]

@[expose] def h1Rels : List (List (Fin 3)) :=
  [[0, 0],
    [1, 2],
    [2, 2, 2, 2, 2, 2],
    [1, 0, 1, 0, 1, 0, 1, 0, 1, 0],
    [1, 1, 0, 1, 1, 0, 1, 1, 0, 2, 2, 0, 2, 2, 0, 2, 2, 0],
    [1, 0, 2, 0, 1, 0, 2, 0, 1, 0, 2, 0, 1, 0, 2, 0, 1, 0, 2, 0, 1, 0, 2, 0],
    [0, 1, 0, 1, 0, 2, 0, 2, 0, 1, 0, 1, 0, 2, 2, 0, 2, 0, 1, 1, 0, 2, 0, 2, 2]]

@[expose] def id8 : Array ℕ := #[1, 2, 4, 8, 16, 32, 64, 128]

@[expose] def zero8 : Array ℕ := #[0, 0, 0, 0, 0, 0, 0, 0]

@[expose] def wordBits : List (Fin 3) → Array ℕ
  | [] => id8
  | s :: w => bmul 8 8 (genBits s) (wordBits w)

@[expose] def urPair (C : Fin 3 → Array ℕ) : List (Fin 3) → Array ℕ × Array ℕ
  | [] => (id8, zero8)
  | s :: w =>
    let p := urPair C w
    (bmul 8 8 (genBits s) p.1, bxor 8 (bmul 8 8 (genBits s) p.2) (bmul 8 8 (C s) p.1))

@[expose] def h1Fb (v : ℕ) : ℕ :=
  packBlks 7 fun k => (urPair (fun s => unpackBlk v s) (h1Rels.getD k [])).2

@[expose] def cobFb (v : ℕ) : ℕ :=
  packBlks 3 fun s =>
    bxor 8 (bmul 8 8 (genBits (Fin.ofNat 3 s)) (unpackBlk v 0))
      (bmul 8 8 (unpackBlk v 0) (genBits (Fin.ofNat 3 s)))

@[expose] def relCheck : Bool := h1Rels.all fun w => bIsId 8 (wordBits w)

@[expose] def h1Check : Bool :=
  certCheck (3 * 64) 64 (7 * 64) (linBits (3 * 64) (7 * 64) h1Fb)
    (Array.ofFn (n := 64) fun j => cobFb (2 ^ (j : ℕ)))

end CFSG.EvenSmallLie.UnitarySix.YamadaPar

module

public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoSuz.CoverCheck
public import CFSG.Sporadic.SuzOddCore.InvGraphCheckInputs

public section

namespace CFSG.EvenSporadicStandard.TwoSuz

open CFSG.Monster.B.Co2.Native CFSG.Sporadic.Schreier.Tits CFSG.Sporadic.SuzOddCore

@[expose] def outerWordsText : String := include_str "OuterWords.txt"

@[expose] def outerParseWord (s : String) : List ℤ :=
  ((s.splitOn " ").filter fun t => t ≠ "").map fun t => t.toInt?.getD 0

structure OuterBlock where
  gens : List (List ℤ)
  us : List (List ℤ)
  vs : List (List ℤ)
  zs : List (List ℤ)
  neg : List ℤ

@[expose] def outerParseBlock (ls : Array (List ℤ)) (p : ℕ) : OuterBlock × ℕ :=
  let K := ((ls.getD p []).getD 0 0).toNat
  let M := ((ls.getD p []).getD 1 0).toNat
  (⟨(List.range K).map fun s => ls.getD (p + 1 + s) [],
    (List.range M).map fun j => ls.getD (p + 1 + K + 2 * j) [],
    (List.range M).map fun j => ls.getD (p + 2 + K + 2 * j) [],
    (List.range K).map fun s => ls.getD (p + 1 + K + 2 * M + s) [],
    ls.getD (p + 1 + K + 2 * M + K) []⟩, p + 2 + 2 * K + 2 * M)

@[expose] def outerLines : Array (List ℤ) :=
  ((outerWordsText.splitOn "\n").filter fun l => l ≠ "").toArray.map outerParseWord

@[expose] def outerBlock2 : OuterBlock := (outerParseBlock outerLines 0).1

@[expose] def outerBlock3 : OuterBlock :=
  (outerParseBlock outerLines (outerParseBlock outerLines 0).2).1

@[expose] def outerBlock (i : ℕ) : OuterBlock := if i = 2 then outerBlock2 else outerBlock3

@[expose] def outerInvW (w : List ℤ) : List ℤ := w.reverse.map Neg.neg

@[expose] def outerCommW (u v : List ℤ) : List ℤ := u ++ v ++ outerInvW u ++ outerInvW v

@[expose] def GenSys.outerSub (G : GenSys) (n : ℕ) (w : ℕ → List ℤ) : GenSys :=
  ⟨(Array.range n).map fun s => G.eval ((w s).map zCode),
    (Array.range n).map fun s => G.eval ((outerInvW (w s)).map zCode)⟩

@[expose] def outerLvl0 : GenSys :=
  ⟨#[mulM negM matA, mulM negM matB], #[invM (mulM negM matA), invM (mulM negM matB)]⟩

@[expose] def outerLvl1 (b : OuterBlock) : GenSys :=
  outerLvl0.outerSub b.gens.length fun s => b.gens.getD s []

@[expose] def outerLvl2 (b : OuterBlock) : GenSys :=
  (outerLvl1 b).outerSub b.us.length fun j => outerCommW (b.us.getD j []) (b.vs.getD j [])

@[expose] def outerCommutesT (i : ℕ) (w : List ℤ) : Bool :=
  eqA 1782 (compA 1782 (wordArr 1782 #[b0Arr, b1Arr] w) (tArr i))
    (compA 1782 (tArr i) (wordArr 1782 #[b0Arr, b1Arr] w))

@[expose] def outerBlockOK (i : ℕ) (b : OuterBlock) : Bool :=
  outerLvl0.valid && (outerLvl1 b).valid && (outerLvl2 b).valid &&
    b.us.length == b.vs.length && b.zs.length == b.gens.length &&
    b.gens.all (fun w => lettersOK 2 w && outerCommutesT i w) &&
    (b.us ++ b.vs).all (lettersOK b.gens.length) && b.zs.all (lettersOK b.us.length) &&
    lettersOK b.gens.length b.neg &&
    (List.range b.gens.length).all (fun s =>
      (outerLvl2 b).eval ((b.zs.getD s []).map zCode) == (outerLvl1 b).mats.getD s oneM) &&
    (outerLvl1 b).eval (b.neg.map zCode) == negM

@[noinline, expose] def outerCheck : Bool :=
  outerBlockOK 2 (outerBlock 2) && outerBlockOK 3 (outerBlock 3)

end CFSG.EvenSporadicStandard.TwoSuz

module

public import CFSG.RankThree.Asc83Table.MatCertDefs
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.FongSporLocalPermDefs
public import Mathlib.Data.Nat.Prime.Defs

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.FongSporLocal

open CFSG.RankThree.Asc83Table.Native CFSG.SectionRank.Native

@[expose] def mwordPow (w : Word) (k : ℕ) : Word := (List.replicate k w).flatten

@[expose] def pwToWord (w : PW) : Word := w.map fun q => (if q.1 then 1 else 0, q.2)

@[expose] def PGen.regW (c : PGen) (i : ℕ) : Word :=
  if i < c.ns.length then pwToWord (c.ns.getD i ([], 0, 0)).1
  else pwToWord (c.ms.getD (i - c.ns.length) ([], 0)).1

@[expose] def PGen.idxWord (c : PGen) (w : List (ℕ × ℕ)) : Word :=
  w.flatMap fun q => mwordPow (c.regW q.1) q.2

structure MGen where
  g : PGen
  oa : ℕ
  ob : ℕ
  zt : ℕ
  tts : List ℕ

@[expose] def MGen.baseFacts (c : MGen) : List MFact :=
  let zW := pwToWord c.g.z
  [.ord 0 c.oa, .ord 1 c.ob, .eq (mwordPow zW c.g.p) [], .ne zW [] c.zt] ++
  (c.g.ts.zip c.tts).flatMap (fun q =>
    let tW := pwToWord q.1
    [.eq (tW ++ tW) [], .ne tW [] q.2, .eq (zW ++ tW) (tW ++ zW)]) ++
  c.g.ns.flatMap (fun n =>
    let nW := pwToWord n.1
    [.eq (nW ++ zW) (mwordPow zW n.2.1 ++ nW), .eq (nW ++ mwordPow zW n.2.2) (zW ++ nW)]) ++
  c.g.ms.flatMap (fun m =>
    let mW := pwToWord m.1
    let tW := pwToWord (c.g.ts.getD m.2 [])
    [.eq (mW ++ tW) (tW ++ mW)])

@[expose] def MGen.facts (c : MGen) : List MFact :=
  c.baseFacts ++ [.eq [(0, 1)] (c.g.idxWord c.g.wa), .eq [(1, 1)] (c.g.idxWord c.g.wb)]

@[expose] def MGen.wf (c : MGen) : Bool :=
  decide c.g.p.Prime && decide (c.tts.length = c.g.ts.length) &&
  c.g.ms.all (fun m => decide (m.2 < c.g.ts.length)) &&
  c.g.wa.all (fun q => decide (q.1 < c.g.ns.length + c.g.ms.length)) &&
  c.g.wb.all (fun q => decide (q.1 < c.g.ns.length + c.g.ms.length))

@[expose] def MGen.check {M V : Type} [Inhabited M] (O : Ops M V) (sA sB : String) (c : MGen) : Bool :=
  c.wf && mcertCheck O sA sB ⟨2, [], c.facts⟩

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.FongSporLocal

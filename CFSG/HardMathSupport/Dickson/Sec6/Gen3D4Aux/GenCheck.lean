module

public import CFSG.HardMathSupport.Dickson.Sec6.Gen3D4Aux.EGroup
public import CFSG.HardMathSupport.Dickson.Sec6.Gen3D4Aux.GenData

public section

namespace CFSG.HardMathSupport.Dickson.Sec6.Gen3D4

open CFSG.AGLEmbedding.ChevOuter

@[expose] def prodP (alph : ℕ → Pr) (w : List ℕ) : Pr := w.foldl (fun acc s => mulP acc (alph s)) oneP

@[expose] def negW (w : List ℕ) : List ℕ := w.reverse.map fun s => if s % 2 = 0 then s + 1 else s - 1

@[expose] def eAlph (c s : ℕ) : Pr := if s % 2 = 0 then eP c (s / 2) else powP (eP c (s / 2)) 2

@[expose] def pEntry (c j : ℕ) : List ℕ × List ℕ × List ℕ :=
  (genPool.getD c []).getD j ([], [], [])

@[expose] def nTable : Array Pr :=
  #[wordP (pEntry 0 0).2.2, wordP (pEntry 0 1).2.2, wordP (pEntry 0 2).2.2,
    wordP (pEntry 1 0).2.2, wordP (pEntry 1 1).2.2, wordP (pEntry 1 2).2.2,
    wordP (pEntry 2 0).2.2, wordP (pEntry 2 1).2.2, wordP (pEntry 2 2).2.2,
    wordP (pEntry 3 0).2.2, wordP (pEntry 3 1).2.2, wordP (pEntry 3 2).2.2]

@[expose] def nInvTable : Array Pr :=
  #[wordP (invWord (pEntry 0 0).2.2), wordP (invWord (pEntry 0 1).2.2),
    wordP (invWord (pEntry 0 2).2.2), wordP (invWord (pEntry 1 0).2.2),
    wordP (invWord (pEntry 1 1).2.2), wordP (invWord (pEntry 1 2).2.2),
    wordP (invWord (pEntry 2 0).2.2), wordP (invWord (pEntry 2 1).2.2),
    wordP (invWord (pEntry 2 2).2.2), wordP (invWord (pEntry 3 0).2.2),
    wordP (invWord (pEntry 3 1).2.2), wordP (invWord (pEntry 3 2).2.2)]

@[expose] def nP (c j : ℕ) : Pr := nTable.getD (3 * c + j) oneP

@[expose] def nInvP (c j : ℕ) : Pr := nInvTable.getD (3 * c + j) oneP

theorem nP_eq {c j : ℕ} (hc : c < 4) (hj : j < 3) : nP c j = wordP (pEntry c j).2.2 := by
  interval_cases c <;> interval_cases j <;> rfl

theorem nInvP_eq {c j : ℕ} (hc : c < 4) (hj : j < 3) :
    nInvP c j = wordP (invWord (pEntry c j).2.2) := by
  interval_cases c <;> interval_cases j <;> rfl

@[expose] def pAlph (c s : ℕ) : Pr := if s % 2 = 0 then nP c (s / 2) else nInvP c (s / 2)

@[expose] def rWord (c i : ℕ) : List ℕ := ((genRW.getD c []).getD i [])

@[expose] def rBase (c : ℕ) : Array Pr :=
  #[prodP (pAlph c) (rWord c 0), prodP (pAlph c) (negW (rWord c 0)),
    prodP (pAlph c) (rWord c 1), prodP (pAlph c) (negW (rWord c 1))]

@[expose] def slpStep (tab : Array Pr) (r : ℕ × ℕ) : Array Pr :=
  tab.push (mulP (tab.getD r.1 oneP) (tab.getD r.2 oneP))

@[expose] def symTab (c : ℕ) : Array Pr := (genRules.getD c []).foldl slpStep (rBase c)

@[expose] def symTabs : Array (Array Pr) := #[symTab 0, symTab 1, symTab 2, symTab 3]

theorem symTabs_eq {c : ℕ} (hc : c < 4) : symTabs.getD c #[] = symTab c := by
  interval_cases c <;> rfl

@[expose] def sAlph (c s : ℕ) : Pr := (symTabs.getD c #[]).getD s oneP

@[expose] def tWord (c k : ℕ) : List ℕ := (genTW.getD c []).getD k []

@[expose] def genPoolCheck (c j : ℕ) : Bool :=
  let e := pEntry c j
  let u := prodP (eAlph c) e.1
  let v := prodP (eAlph c) e.2.1
  let n := nP c j
  e.1.all (· < 6) && e.2.1.all (· < 6) && e.2.2.all (· < 16) &&
    decide (powP u 3 = oneP) && decide (powP v 3 = oneP) && decide (mulP u v = mulP v u) &&
    (List.range 3).all (fun a => (List.range 3).all fun b =>
      (a == 0 && b == 0) || decide (mulP (powP u a) (powP v b) ≠ oneP)) &&
    decide (mulP u n = mulP n u) && decide (mulP v n = mulP n v) &&
    decide (mulP n (nInvP c j) = oneP)

@[expose] def genRCheck (c : ℕ) : Bool :=
  (genRW.getD c []).length == 2 && (genRW.getD c []).all (fun w => w.all (· < 6)) &&
    decide (mulP ((rBase c).getD 0 oneP) ((rBase c).getD 1 oneP) = oneP) &&
    decide (mulP ((rBase c).getD 2 oneP) ((rBase c).getD 3 oneP) = oneP)

@[expose] def genSlpCheck (c : ℕ) : Bool :=
  (genTW.getD c []).length == 16 && (List.range 16).all fun k =>
    decide (prodP (sAlph c) (tWord c k) = (letterArr k, 0))

@[expose] def genCheckClass (c : ℕ) : Bool :=
  genPool.length == 4 && (genPool.getD c []).length == 3 && (List.range 3).all (genPoolCheck c) &&
    genRCheck c && genSlpCheck c

@[expose] def genCheckI : Bool := genCheckClass 0 && genCheckClass 1

@[expose] def genCheckII : Bool := genCheckClass 2 && genCheckClass 3

end CFSG.HardMathSupport.Dickson.Sec6.Gen3D4

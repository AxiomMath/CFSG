module

public import CFSG.Sporadic.SmallOddCore.HSLocalCheckInputs
public import CFSG.Sporadic.SmallOddCore.HSCheckInputs

public section

namespace CFSG.EvenSporadicStandard.HSStd.Zassenhaus.InnerCert

open CFSG.Sporadic.Th.Native CFSG.Sporadic.SmallOddCore.Native CFSG.PSL3Four.Native
open CFSG.Sporadic.SmallOddCore

@[expose] def innerHex : String := include_str "InnerTbl.txt"

@[expose] def innerTbl (k : ℕ) : Table := hexT 3 3850 (3850 * k) innerHex

@[expose] def itab (k : ℕ) : Tab := natArr (innerTbl k)

@[expose] def tG : Tab := itab 0
@[expose] def tA : Tab := itab 1
@[expose] def tH : Tab := itab 2
@[expose] def tY (i : ℕ) : Tab := itab (3 + i)
@[expose] def tCP (i : ℕ) : Tab := itab (7 + i)
@[expose] def tU : Tab := itab 9
@[expose] def tGS (j : ℕ) : Tab := itab (10 + j)
@[expose] def tCS (i : ℕ) : Tab := itab (10 + i)
@[expose] def tT1 : Tab := natArr (hsCentTbl 5)

@[expose] def tGi : Tab := invTab 3850 tG

@[expose] def codeTab (g gi y : Tab) : ℕ → Tab
  | 0 => g
  | 1 => gi
  | _ => y

@[expose] def wordTab (g gi y : Tab) (w : List ℕ) : Tab :=
  w.foldr (fun c acc => comp 3850 (codeTab g gi y c) acc) (idTab 3850)

@[expose] def wT (y : Tab) (w : List ℕ) : Tab := wordTab tG tGi y w

@[expose] def fixN (t : Tab) : ℕ := (List.range 3850).countP fun i => t[i]! == i

opaque c1TabsSeal : {t : Array Tab // t = hsC1Enum.tabs} := ⟨hsC1Enum.tabs, rfl⟩

@[expose] def c1Tabs : Array Tab := c1TabsSeal.1

theorem c1Tabs_def : c1Tabs = hsC1Enum.tabs := c1TabsSeal.2

attribute [irreducible] c1Tabs

@[expose] def inC1 (t : Tab) : Bool := c1Tabs.contains t

@[expose] def isInv (x : Tab) : Bool := comp 3850 x x == idTab 3850

@[expose] def pow5 (t : Tab) : Tab :=
  let t2 := comp 3850 t t
  comp 3850 (comp 3850 t2 t2) t

@[expose] def memOK : Bool :=
  inC1 tG && inC1 tA && inC1 tH && (List.range 4).all (fun i => inC1 (tY i)) &&
    (List.range 2).all (fun i => inC1 (tCP i)) && inC1 (tCS 2) && inC1 (tCS 3) &&
    permOK 3850 (innerTbl 9) && hsSift (innerTbl 9) &&
    permOK 3850 (innerTbl 10) && hsSift (innerTbl 10) &&
    permOK 3850 (innerTbl 11) && hsSift (innerTbl 11) &&
    permOK 3850 (hsCentTbl 5) && tGi.size == 3850 && comp 3850 tGi tG == idTab 3850

@[expose] def orderOK : Bool :=
  pow5 tG == idTab 3850 && tG != idTab 3850 && comp 3850 tH tG == comp 3850 tG tH &&
    c1Tabs.all fun t => !(pow5 t == idTab 3850 && t != idTab 3850) ||
      c1Tabs.any fun c => comp 3850 c t == comp 3850 tG c

@[expose] def rep (o : ℕ) (W : List ℕ) : List ℕ := (List.replicate o W).flatten

@[expose] def filtV : List (List ℕ × Bool) :=
  [(rep 2 [2], true), (rep 1 [2], false),
    (rep 8 [0, 2], true), (rep 4 [0, 2], false),
    (rep 6 [0, 0, 2], true), (rep 3 [0, 0, 2], false), (rep 2 [0, 0, 2], false),
    (rep 6 [0, 2, 1, 2], true), (rep 3 [0, 2, 1, 2], false), (rep 2 [0, 2, 1, 2], false)]

@[expose] def patOK (y : Tab) : Bool :=
  filtV.all fun p => (wT y p.1 == idTab 3850) == p.2

@[expose] def hPow : ℕ → Tab
  | 0 => idTab 3850
  | k + 1 => comp 3850 tH (hPow k)

@[expose] def hPows : Array Tab := (Array.range 20).map hPow

@[expose] def hitOK (y : Tab) : Bool :=
  hPows.any fun hk => (List.range 4).any fun i => comp 3850 hk y == comp 3850 (tY i) hk

@[expose] def filterOK : Bool :=
  patOK tA && c1Tabs.all fun y => !patOK y || hitOK y

@[expose] def eWc : List (List ℕ) :=
  [[0, 0, 2, 1, 1, 2, 0, 0, 2, 1, 1, 2], [1, 1, 2, 0, 0, 2, 1, 1, 2, 0, 0, 2],
    [0, 2, 0, 0, 2, 0, 2, 0, 2, 0, 2, 1, 2, 1], [2]]

@[expose] def eGens (y : Tab) : Array Tab :=
  Array.ofFn (n := 4) fun j => wT y (eWc.getD j.val [])

@[expose] def eEnum : Enum := enumBFS 3850 (eGens tA) 16

@[expose] def eOK : Bool :=
  enumOK 3850 (eGens tA) eEnum && eEnum.tabs.size == 16 &&
    eEnum.tabs.all (fun x => eEnum.tabs.all fun y => comp 3850 x y == comp 3850 y x) &&
    eEnum.tabs.all isInv && eEnum.tabs.contains tT1 &&
    eEnum.tabs.all fun x => x == idTab 3850 || fixN x == 170

@[expose] def presOK : Bool :=
  (List.range 2).all (fun i => isInv (tY i) && fixN (tY i) == 170 &&
    (List.range 4).all fun j =>
      eEnum.tabs.any fun x => comp 3850 (tCP i) (wT (tY i) (eWc.getD j [])) == comp 3850 x (tCP i)) &&
  (List.range 2).all (fun i => isInv (tY (i + 2)) && fixN (tY (i + 2)) == 30)

@[expose] def wbc : List ℕ := [0, 2, 0, 0, 2, 0, 0, 2, 0]

@[expose] def tB : Tab := wT tA wbc

@[expose] def classOK : Bool :=
  permOK 3850 (hsCentTbl 12) && fixN (natArr (hsCentTbl 12)) == 30 &&
    fixN tT1 == 170 && fixN tA == 170 && isInv tA && isInv tB && fixN tB == 30 &&
    isInv tU && fixN (tU) == 30 &&
    comp 3850 (tU) tB == comp 3850 tB (tU) &&
    fixN (comp 3850 (tU) tB) == 30 &&
    (List.range 2).all fun i => isInv (wT (tY (i + 2)) wbc) && fixN (wT (tY (i + 2)) wbc) == 170

@[expose] def yWc : List (List ℕ) :=
  [[], [2],
    [0, 2, 1, 2, 0, 2, 1, 2, 0, 2, 1, 2],
    [0, 2, 1, 2, 0, 2, 1, 2, 0, 2, 1],
    [0, 2, 0, 0, 2, 0, 0, 2, 0],
    [0, 2, 0, 0, 2, 0, 0, 2, 0, 2],
    [0, 2, 0, 0, 2, 1, 1, 2, 1, 2, 0, 2, 1, 2, 0, 2],
    [0, 2, 0, 0, 2, 1, 1, 2, 1, 2, 0, 2, 1, 2, 0]]

@[expose] def zmulL : List ℕ := [2, 3, 0, 1, 6, 7, 4, 5]

@[expose] def sigmaL : List (List ℕ) := [[0, 1, 3, 2, 4, 5, 7, 6], [0, 2, 1, 3, 7, 5, 6, 4]]

@[expose] def psiL : List (List ℕ) := [[0, 6, 2, 4, 1, 7, 3, 5], [0, 4, 2, 6, 3, 7, 1, 5]]

@[expose] def tE8 (e : ℕ) : Tab := wT tA (yWc.getD e [])

@[expose] def tE8Y (i e : ℕ) : Tab := wT (tY i) (yWc.getD e [])

@[expose] def stabOK : Bool :=
  (List.range 8).all (fun e => comp 3850 (tE8 e) tT1 == tE8 (zmulL.getD e 0)) &&
    tE8 0 == idTab 3850 && tE8 1 == tA &&
    (List.range 2).all (fun j => (List.range 8).all fun e =>
      comp 3850 (tGS j) (tE8 e) == comp 3850 (tE8 ((sigmaL.getD j []).getD e 0)) (tGS j)) &&
    (List.range 2).all (fun i => (List.range 8).all fun e =>
      comp 3850 (tCS (i + 2)) (tE8Y (i + 2) e) ==
        comp 3850 (tE8 ((psiL.getD i []).getD e 0)) (tCS (i + 2)))

@[expose] def innerOK : Bool :=
  memOK && orderOK && filterOK && eOK && presOK && classOK && stabOK

end CFSG.EvenSporadicStandard.HSStd.Zassenhaus.InnerCert

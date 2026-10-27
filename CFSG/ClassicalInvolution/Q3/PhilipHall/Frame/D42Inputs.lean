module

public import CFSG.ClassicalInvolution.Q3.Q3TLTO8Inputs
public import CFSG.Sporadic.SmallOddCore.LocalCheck
public import Certificates.Data.PhilipHallD42

public section

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.D42

open CFSG.EvenSmallLie.OmegaEight CFSG.Certificates.Native CFSG.Monster.B.Co2.Native
  CFSG.Sporadic.Th.Native CFSG.Sporadic.Schreier.Native CFSG.Sporadic.SmallOddCore.Native
  CFSG.Sporadic.SmallOddCore CFSG.ComponentClassification.J2Cover CFSG.ClassicalInvolution.Q3.O8
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.D42Data CFSG.ClassicalInvolution.O8Data

@[expose] def closeGTA : Array Table := closeGT.push (arrTable 360 rhoArr)

@[expose] def closeGIA : Array Table := closeGI.push (arrTable 360 (invCand 360 rhoArr))

@[expose] def classC2Check : Bool :=
  isInvA 360 rhoArr (invCand 360 rhoArr) &&
    (let b := arrTable 360 (mainArrs.getD 1 #[])
     let c := conjClosureH 360 closeGTA closeGIA b 11340
     conjTreeOK 360 closeGTA closeGIA b c.1 c.2.1 c.2.2 && hkeysDistinct 360 c.1.toList &&
       decide (11340 ≤ c.1.size))

@[expose] def mainIdx (j : ℕ) : ℕ := if j = 0 then 0 else 2

@[expose] def zTbl (j : ℕ) : Table := arrTable 360 (mainArrs.getD (mainIdx j) #[])

@[expose] def pGens (j : ℕ) : List Table := (pWords.getD j []).map fun w => arrTable 360 (autW w)

@[expose] def cgTbls (j : ℕ) : List Table :=
  let T := (centGens.getD (mainIdx j) []).map fun w => arrTable 360 (omegaW w)
  T ++ T.map (invT 360)

@[expose] def uGens (j : ℕ) : List Table := (uWords.getD j []).map (wordTbl 360 (cgTbls j))

@[expose] def omegaLevels : Array Level := rawLevels 360 omegaS (omegaBase.map Fin.val).toArray

@[expose] def siftOmega (lv : Array Level) (T : Table) : Bool :=
  siftA 360 lv (omegaBase.map Fin.val).toArray 0 (natArr T)

@[expose] def pOrder (j : ℕ) : ℕ := if j = 0 then 81 else 9

@[expose] def sylowCheck (j : ℕ) : Bool :=
  (pWords.getD j []).all (fun w => lettersOK 18 w) &&
    (pGens j).all (fun g => permOK 360 g && invOK 360 g (invT 360 g) && commTT 360 g (zTbl j)) &&
    enumOK 360 (pOrder j) (pOrder j) (pGens j)

@[expose] def uCheck (j : ℕ) : Bool :=
  let lv := omegaLevels
  (uGens j).all (fun g => permOK 360 g && siftOmega lv g && commTT 360 g (zTbl j)) &&
    enumOK 360 512 512 (uGens j) && normOK 360 512 (uGens j) (pGens j)

@[expose] def commTbl (u y : Table) : Table :=
  compT 360 (compT 360 (compT 360 u y) (invT 360 u)) (invT 360 y)

@[expose] def pickDistinct (EU : Array Table) (y : Table) (m : ℕ) : List ℕ := Id.run do
  let mut seen : List UInt64 := []
  let mut out : List ℕ := []
  for k in [0:EU.size] do
    if out.length < m then
      let h := hkey 360 (commTbl EU[k]! y)
      if !(seen.contains h) then
        seen := h :: seen
        out := k :: out
  return out.reverse

@[expose] def commOK (EU : Array Table) (y : Table) : Bool :=
  let sel := pickDistinct EU y 9
  sel.length == 9 && sel.all (fun k => decide (k < EU.size)) && invOK 360 y (invT 360 y) &&
    sel.all (fun k => invOK 360 EU[k]! (invT 360 EU[k]!)) &&
    hkeysDistinct 360 (sel.map fun k => commTbl EU[k]! y)

@[expose] def commCheck (j : ℕ) : Bool :=
  let EP := (mulClosureH 360 (pGens j).toArray (pOrder j)).1
  let EU := (mulClosureH 360 (uGens j).toArray 512).1
  let lv := omegaLevels
  EP.all fun y => siftOmega lv y || commOK EU y

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.D42

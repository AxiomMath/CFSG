module

public import CFSG.Certificates.Kernel.Spor.RawOrbSound
public import CFSG.Certificates.Kernel.SporSch.PairClTDefs
import CFSG.Certificates.Kernel.SporSch.PairClTProof

public section

namespace CFSG.KS.SporSch

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.Monster.B.Co2.Native CFSG.Certificates.Native
open CFSG.Sporadic.Schreier.PairNative

theorem closNFT_sound {n w kS nb BP NS CH NR NL NT BT NQ BQ kg c cap nS R H nB B : Nat}
    {PS PSI LR Ts LT PT QT «GL» X W K C SO SOI : Nat → Nat}
    {S : Array (Array Nat)} {base : Array Nat} {bs RP : List Nat}
    {gens gensInv : Array (Array Nat)} {rep : List (Array Nat)}
    (hb : Binds n w PS kS nb BP S base)
    (hp : allN kS (fun j => permOK n w (mask w) (n * w) (PS j) (PSI j)) = true)
    (ho : OrbsOK n w PS PSI LR kS nb BP NS CH) (hN : n ≤ NS * CH)
    (ht : TabsT n w kS nb BP NR NL PS PSI LR Ts LT PT QT NT BT NQ BQ) (hbs : base.toList = bs)
    (hg : gens.size = kg ∧ gensInv.size = kg ∧
      ∀ l < kg, gens[l]! = unpack n w (letterK PS PSI kS («GL» l)) ∧
        gensInv[l]! = unpack n w (letterK PS PSI kS (invL kS («GL» l))))
    (hrep : rep = RP.map (unpack n w))
    (h : ClosNFT n w kS nb NR NL LR LT PT QT bs kg «GL» RP c cap nS R H nB B X W K C SO SOI) :
    closureOK (rawLevels n S base) bs gens gensInv rep
        (conjClosureNF n (rawLevels n S base) bs gens gensInv
          (decodeNF (rawLevels n S base) (baseImgs bs rep).toArray) cap).1
        (conjClosureNF n (rawLevels n S base) bs gens gensInv
          (decodeNF (rawLevels n S base) (baseImgs bs rep).toArray) cap).2.1
        (conjClosureNF n (rawLevels n S base) bs gens gensInv
          (decodeNF (rawLevels n S base) (baseImgs bs rep).toArray) cap).2.2 = true ∧
      (conjClosureNF n (rawLevels n S base) bs gens gensInv
          (decodeNF (rawLevels n S base) (baseImgs bs rep).toArray) cap).1.size = c ∧
      (conjClosureNF n (rawLevels n S base) bs gens gensInv
          (decodeNF (rawLevels n S base) (baseImgs bs rep).toArray) cap).1.toList.map
          (fun nf => imgKey n (baseImgs bs (nfWord (rawLevels n S base) nf))) =
        (List.range c).map K :=
  ClTP.closNFT_proved hb hp ho hN ht hbs hg hrep h

end CFSG.KS.SporSch

end

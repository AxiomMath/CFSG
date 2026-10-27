module

public import CFSG.Certificates.Kernel.Spor.RawDefs
public import Certificates.Data.Kernel.Spor.Prim
import CFSG.Certificates.Kernel.Spor.RawSiftK
public import Certificates.Data.CFSGNative.Co3Schreier.Basic

public section

namespace CFSG.KS.Raw

open CFSG.KC.Enum CFSG.KS CFSG.Monster.B.Co2.Native CFSG.Certificates.Native

theorem rawChainK_sound {n w kS kO nb BP NS CH chunks : Nat} {PS PSI LR TR TRI : Nat → Nat}
    {S : Array (Array Nat)} {base : Array Nat} {D : List (List Int)}
    (hb : Binds n w PS kS nb BP S base)
    (hh : headK n w (mask w) (n * w) (pidn n w) PS PSI kS kO D nb BP = true)
    (hl : LevelsOK n w PS PSI LR TR TRI kS nb BP)
    (hNS : n ≤ NS * CH)
    (hs : ∀ i < nb, ∀ s < NS, schK n w (mask w) (n * w) (pidn n w) PS PSI LR TR TRI kS BP nb i
      (stepsAt n w PS kS BP i) (s * CH) CH = true) :
    rawChainOK n (S.extract 0 kO) S base (CFSG.Sporadic.Schreier.Co3.Native.wordsArr kO kS D)
      chunks = true :=
  Orb.rawChainOK_of_K hb hh hl hNS hs

theorem rawOrbitSizesK_sound {n w kS nb BP : Nat} {PS PSI LR TR TRI : Nat → Nat}
    {S : Array (Array Nat)} {base : Array Nat}
    (hb : Binds n w PS kS nb BP S base)
    (hp : allN kS (fun j => permOK n w (mask w) (n * w) (PS j) (PSI j)) = true)
    (hl : LevelsOK n w PS PSI LR TR TRI kS nb BP) :
    rawOrbitSizes n S base = (List.range nb).map fun i => rcnt (LR i) :=
  Orb.rawOrbitSizes_of_K hb hp hl

theorem siftK_sound {n w kS nb BP : Nat} {PS PSI LR TR TRI : Nat → Nat}
    {S : Array (Array Nat)} {base : Array Nat} {g : Array Nat} {G : Nat}
    (hb : Binds n w PS kS nb BP S base)
    (hp : allN kS (fun j => permOK n w (mask w) (n * w) (PS j) (PSI j)) = true)
    (hl : LevelsOK n w PS PSI LR TR TRI kS nb BP)
    (hg : g = unpack n w G) (hr : allN n (fun i => Nat.blt (pg w (mask w) G i) n) = true)
    (h : siftK n w (mask w) (n * w) (pidn n w) LR TRI BP nb 0 G = true) :
    siftA n (rawLevels n S base) base 0 g = true :=
  Orb.siftA_of_K hb hp hl hg hr h

theorem range_of_canonK {n w G : Nat} (h : CFSG.KS.Prim.canonK n w (mask w) (n * w) G = true) :
    allN n (fun i => Nat.blt (pg w (mask w) G i) n) = true := by
  unfold CFSG.KS.Prim.canonK at h
  obtain ⟨-, h2⟩ := (bAnd_iff _ _).1 h
  exact ((bAnd_iff _ _).1 h2).2

theorem range_of_permOK {n w G q : Nat} (h : permOK n w (mask w) (n * w) G q = true) :
    allN n (fun i => Nat.blt (pg w (mask w) G i) n) = true := by
  unfold permOK at h
  obtain ⟨-, h2⟩ := (bAnd_iff _ _).1 h
  obtain ⟨-, h3⟩ := (bAnd_iff _ _).1 h2
  refine allN_of_forall fun i hi => ?_
  have h4 := allN_spec h3 i hi
  rw [strictB_eq] at h4
  exact ((bAnd_iff _ _).1 h4).1

end CFSG.KS.Raw

end

module

public import Certificates.Data.Kernel.J2EnumQ
public import CFSG.Certificates.Kernel.J2EnumSound
public import Mathlib.Data.Nat.Prime.Defs
import CFSG.Certificates.Kernel.J2Enum.Count

public section

namespace CFSG.KC.J2Enum

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KC.Child3 CFSG.Monster.B.Co2.Native
open CFSG.Certificates.Native CFSG.Sporadic.Th.Native CFSG.Sporadic.Schreier.Native
open CFSG.ComponentClassification.J2Cover

theorem enumCntQ_sound {n w kS kO BP NS CH R₁ R₂ q r s : Nat} {PS PSI LR TR TRI : Nat → Nat}
    {D : List (List Int)} {S : Array (Array Nat)} {base : Array Nat}
    (hc : ChainOK3 n w kS kO BP NS CH PS PSI LR TR TRI D S base)
    (h20 : rcnt (LR 0) * rcnt (LR 1) * rcnt (LR 2) < 2 ^ 20)
    (h1 : canonK n w (mask w) (n * w) R₁ = true ∧
      siftK n w (mask w) (n * w) (pidn n w) LR TRI BP 3 0 R₁ = true)
    (h2 : canonK n w (mask w) (n * w) R₂ = true ∧
      siftK n w (mask w) (n * w) (pidn n w) LR TRI BP 3 0 R₂ = true)
    (hq : q.Prime) (hr : r.Prime) (hs : s.Prime) :
    (filterProducts n (ordTest n q) (chainTables n S base) (idT n) []).countP
        (pairTest n r s 2 q (arrTable n (unpack n w R₁))) =
      fld20 (sumF (rcnt (LR 0)) (blkCntQ n w LR TR BP (pidn n w) R₁ R₂ q r s)) 0 ∧
    (filterProducts n (ordTest n q) (chainTables n S base) (idT n) []).countP
        (pairTest n r s 2 q (arrTable n (unpack n w R₂))) =
      fld20 (sumF (rcnt (LR 0)) (blkCntQ n w LR TR BP (pidn n w) R₁ R₂ q r s)) 1 := by
  obtain ⟨hb, hh, hl, hNS, hsc, hp⟩ := hc
  exact CntPf.enumCntQ_sound' hb hh hl hNS hsc hp h20 h1 h2 hq hr hs

end CFSG.KC.J2Enum

end

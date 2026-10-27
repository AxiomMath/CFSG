module

public import CFSG.Certificates.Kernel.Misc.HypNative
public import CFSG.Certificates.Kernel.Misc.LinesSpec
import CFSG.Certificates.Kernel.Misc.LinesAlg

public section

namespace CFSG.KC.Misc.Hyp

open CFSG.F4.Native CFSG.Sporadic.Th.Native CFSG.Fischer.Native CFSG.KC.Misc.T46
  CFSG.KC.Misc.Lines CFSG.KC.Misc.Xi CFSG.KS.PK CFSG.KC.Ord CFSG.KC.LQT.P CFSG.KC.Misc
  CFSG.KC.Misc.O73 CFSG.KS.TW

theorem lineCG_eq {UL : List Nat} {UP PP : Nat} (H : Pts UL UP PP) {x y : Nat} (hx : x < 693)
    (hy : y < 693) : lineCG UL.toArray x y = (lineL UP PP x y).toArray := by
  have hx4 := H.lt x hx
  have hy4 := H.lt y hy
  unfold lineCG
  dsimp only
  rw [list_toArray_getElem! UL x, list_toArray_getElem! UL y,
    H.uPosG_get (normC_lt _), H.uPosG_get (normC_lt _), H.uPosG_get (normC_lt _)]
  simp only [lineL, lnP1, lnP2, lnP3, H.fd12 x hx, H.fd12 y hy]

private theorem hypLineFG_eq {UL : List Nat} {UP PP : Nat} (H : Pts UL UP PP) {x y : Nat}
    (hx : x < 693) (hy : y < 693) :
    lineFG UL.toArray (normTab ()) (scaleTab 2) (scaleTab 3) x y =
      (lineL UP PP x y).toArray := by
  have hx4 := H.lt x hx
  have hy4 := H.lt y hy
  unfold lineFG
  dsimp only
  rw [list_toArray_getElem! UL x, list_toArray_getElem! UL y, scaleTab_get 2 hy4,
    scaleTab_get 3 hy4,
    normTab_get (xor_lt_4096 hx4 hy4), normTab_get (xor_lt_4096 hx4 (scaleC_lt 2 _)),
    normTab_get (xor_lt_4096 hx4 (scaleC_lt 3 _)), H.uPosG_get (normC_lt _),
    H.uPosG_get (normC_lt _), H.uPosG_get (normC_lt _)]
  simp only [lineL, lnP1, lnP2, lnP3, H.fd12 x hx, H.fd12 y hy]

theorem lineTabG_perp {UL : List Nat} {UP PP : Nat} {PB : Nat → Nat} (H : Pts UL UP PP)
    (hP : ∀ x < 693, ∀ y < 693, ((perpTabG UL.toArray)[x]!)[y]! = bitK (PB x) y) {x y : Nat}
    (hx : x < 693) (hy : y < 693) :
    (lineTabG UL.toArray (perpTabG UL.toArray))[x * 693 + y]! =
      if bitK (PB x) y = true then (lineL UP PP x y).toArray else #[] := by
  unfold lineTabG
  rw [getElem!_pos _ _ (by simp; omega), Array.getElem_ofFn]
  have e1 : (x * 693 + y) / 693 = x := by omega
  have e2 : (x * 693 + y) % 693 = y := by omega
  simp only [e1, e2, hP x hx y hy]
  by_cases h : bitK (PB x) y = true
  · rw [if_pos h, if_pos h]
    exact hypLineFG_eq H hx hy
  · rw [if_neg h, if_neg h]

end CFSG.KC.Misc.Hyp

end

module

public import Certificates.Data.Kernel.GFR3K
public import CFSG.Certificates.Kernel.FiveLocKSound
public import CFSG.HardMathSupport.Solomon.Coordinator.GFR3Kit

public section

namespace CFSG.KC.GFR3K

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KC.Misc.ArrEnum CFSG.KC.B3S3K CFSG.KC.FiveLocK
open CFSG.Monster.B.Co2.Native CFSG.RankThree.Native CFSG.HardMathSupport.Solomon.Coordinator
open CFSG.Monster.B.Co2 (allLt_iff)

theorem card_filter_range (N : ℕ) (p : ℕ → Bool) :
    ((Finset.range N).filter fun j => p j = true).card = ((List.range N).filter p).length := by
  have e : ((Finset.range N).filter fun j => p j = true) = ((List.range N).filter p).toFinset := by
    ext x
    simp
  rw [e, List.toFinset_card_of_nodup (List.nodup_range.filter _)]

variable {n w : ℕ} (hw : szOK n w = true)
include hw

theorem commCount_eq {pts : Array (Array ℕ)} {N : ℕ} {T : ℕ → ℕ} (hs : pts.size = N)
    (hT : ∀ i < N, pts[i]! = unpack n w (T i)) (hp : ∀ i < N, permB n w (T i) = true)
    {x : ℕ} (hx : permB n w x = true) :
    gfr3CommCount n pts (unpack n w x) = gfr3CntK n w N T x := by
  unfold gfr3CommCount gfr3CntK
  rw [hs, card_filter_range, CFSG.KC.BfsPin.sumN_count]
  congr 1
  apply List.filter_congr
  intro j hj
  rw [hT j (List.mem_range.1 hj), commA_unpack hw (hp j (List.mem_range.1 hj)) hx]

theorem gfr3ClassOK_of {pts : Array (Array ℕ)} {N : ℕ} {T : ℕ → ℕ} (hs : pts.size = N)
    (hT : ∀ i < N, pts[i]! = unpack n w (T i)) (hp : ∀ i < N, permB n w (T i) = true)
    {Nc e f : ℕ} (h : ∀ i < N, gfr3AtK n w N T Nc e f i = true) :
    gfr3ClassOK n pts Nc e f = true := by
  unfold gfr3ClassOK
  rw [allLt_iff]
  intro i hi
  rw [hs] at hi
  have hi' := h i hi
  unfold gfr3AtK at hi'
  rw [hT i hi, powEq_id hw (hp i hi), powEq_id hw (hp i hi), eqA_id hw (hp i hi),
    commCount_eq hw hs hT hp (hp i hi)]
  exact hi'

end CFSG.KC.GFR3K

end

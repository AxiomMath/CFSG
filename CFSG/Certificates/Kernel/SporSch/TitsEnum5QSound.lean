module

public import CFSG.Certificates.Kernel.SporSch.TitsEnum5Sound
import CFSG.Certificates.Kernel.Spor.RawTreeDefs

public section

namespace CFSG.KS.SporSch

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.Sporadic.Schreier.Tits
open CFSG.Certificates.Native CFSG.Monster.B.Co2.Native

theorem all5KQ_sound {n w kS BP : Nat} {PS PSI LR TR TRI : Nat → Nat} {S : Array (Array Nat)}
    {base : Array Nat} {p : Array Nat → Bool} {Q : Nat → Nat → Nat → Nat → Nat → Nat → Bool}
    (hb : Binds n w PS kS 5 BP S base)
    (hp : allN kS (fun j => permOK n w (mask w) (n * w) (PS j) (PSI j)) = true)
    (hl : LevelsOK n w PS PSI LR TR TRI kS 5 BP)
    (hP : ∀ k t0 t1 t2 t3 t4, canonK n w (mask w) (n * w) t0 = true →
      canonK n w (mask w) (n * w) t1 = true → canonK n w (mask w) (n * w) t2 = true →
      canonK n w (mask w) (n * w) t3 = true → canonK n w (mask w) (n * w) t4 = true →
      isInvA n (unpack n w (prod5K n w (mask w) t0 t1 t2 t3 t4))
        (invCand n (unpack n w (prod5K n w (mask w) t0 t1 t2 t3 t4))) = true →
      Q k t0 t1 t2 t3 t4 = true → p (unpack n w (prod5K n w (mask w) t0 t1 t2 t3 t4)) = true)
    (h : all5K n (n * w) LR TR Q = true) :
    all5 n (rawLevels n S base) p = true := by
  have c0 := (lev_trAt hb hp hl (i := 0) (by omega)).1
  have c1 := (lev_trAt hb hp hl (i := 1) (by omega)).1
  have c2 := (lev_trAt hb hp hl (i := 2) (by omega)).1
  have c3 := (lev_trAt hb hp hl (i := 3) (by omega)).1
  have c4 := (lev_trAt hb hp hl (i := 4) (by omega)).1
  unfold all5
  rw [c0, c1, c2, c3, c4]
  refine CFSG.Monster.B.Co2.allLt_iff.2 fun a ha => CFSG.Monster.B.Co2.allLt_iff.2 fun b hb' =>
    CFSG.Monster.B.Co2.allLt_iff.2 fun c hc => CFSG.Monster.B.Co2.allLt_iff.2 fun d hd =>
    CFSG.Monster.B.Co2.allLt_iff.2 fun e he => ?_
  obtain ⟨⟨k0, k1, k2, k3, k4⟩, eg, σ, hσ⟩ := prod5_facts hb hp hl ha hb' hc hd he
  have hinv : isInvA n (unpack n w (prod5K n w (mask w) (trAt n (n * w) LR TR 0 a)
      (trAt n (n * w) LR TR 1 b) (trAt n (n * w) LR TR 2 c) (trAt n (n * w) LR TR 3 d)
      (trAt n (n * w) LR TR 4 e))) (invCand n (unpack n w (prod5K n w (mask w)
      (trAt n (n * w) LR TR 0 a) (trAt n (n * w) LR TR 1 b) (trAt n (n * w) LR TR 2 c)
      (trAt n (n * w) LR TR 3 d) (trAt n (n * w) LR TR 4 e)))) = true := by
    rw [← eg]
    exact isInvA_of_rep hσ (rep_invCand hσ)
  rw [eg]
  exact hP _ _ _ _ _ _ k0 k1 k2 k3 k4 hinv (all5K_at h ha hb' hc hd he)

end CFSG.KS.SporSch

end

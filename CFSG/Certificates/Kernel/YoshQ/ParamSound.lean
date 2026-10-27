module

public import Certificates.Data.Kernel.YoshQ.Param
public import CFSG.Certificates.Kernel.YoshQ.ReplaySound
public import CFSG.Certificates.Kernel.YoshQ.IdxSound

public section

namespace CFSG.KC.YoshQ

open CFSG.KC.Enum CFSG.KS CFSG.KS.MulH CFSG.Sporadic.Th.Native CFSG.Sporadic.Schreier.Native
open CFSG.Sporadic.SmallOddCore.Native CFSG.EvenSporadicStandard.Fin76b
open CFSG.EvenSporadicStandard.M12Std.Yosh

theorem gensOK_spec {n w : Nat} {g : Array Table} {GS : List Nat} (h : gensOK n w g GS = true) :
    g = (GS.map (tabN n w)).toArray ∧
      g.all (fun x => CFSG.Sporadic.SmallOddCore.permOK n x) = true := by
  unfold gensOK at h
  rw [Bool.and_eq_true, beq_iff_eq] at h
  exact h

theorem modelCheck_of {n m k size : Nat} {g : Array Table} {ws : List (List (Fin k × Bool))}
    (he : enumOK n m g (mulClosureS n m g 4000) size = true) (hw : wordsOK n k g ws = true) :
    modelCheck n m k g ws size = true := by
  unfold modelCheck
  unfold wordsOK at hw
  rw [Bool.and_assoc, he, hw]
  rfl

theorem distinct_of {n w m cap cnt EP PL POS : Nat} {GS SM SF : List Nat}
    (h : replayK n w m cap GS cnt EP PL POS SM SF = true) : Distinct n w cnt EP := by
  unfold Distinct
  intro a ha b hb e
  exact (replayK_sound h).finj a ha b hb (by rw [e])

end CFSG.KC.YoshQ

end

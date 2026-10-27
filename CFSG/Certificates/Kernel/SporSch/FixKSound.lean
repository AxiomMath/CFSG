module

public import Certificates.Data.Kernel.SporSch.FixK
public import CFSG.Certificates.Kernel.Misc.PairCountSound
public import Certificates.Data.CFSGNative.Schreier.SetOrbit

public section

namespace CFSG.KS.SporSch

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.Certificates.Native CFSG.KC.Misc.PairCount

theorem fixK_sound {n w T : Nat} {L : List Nat} (h : fixK n w T L = true) :
    fixedList n (unpack n w T) = L := by
  unfold fixK at h
  rw [← beq_iff_eq.1 h]
  unfold fixedList
  refine List.filter_congr fun p hp => ?_
  rw [unpack_get (List.mem_range.1 hp)]
  cases e : Nat.beq (pg w (mask w) T p) p
  · have : pg w (mask w) T p ≠ p := fun h' => by rw [h', Nat.beq_refl] at e; exact absurd e (by decide)
    simp [this]
  · simp [Nat.eq_of_beq_eq_true e]

end CFSG.KS.SporSch

end

module

public import Certificates.Data.Kernel.O8.SAM
public import CFSG.Certificates.Kernel.O8SASound
public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEightMinus.NativeSylowDefs

public section

namespace CFSG.KC.O8

open CFSG.KC.Enum

theorem actsMK_sound {NS NI P M : Nat}
    (hNS : ∀ p < 136, CFSG.EvenSmallLie.OmegaEightMinus.nsArr[p]! = pg 8 255 NS p)
    (hNI : ∀ v < 256, CFSG.EvenSmallLie.OmegaEightMinus.nsIdx[v]! = pg 8 255 NI v)
    (h : actsMK NS NI P M = true) :
    CFSG.EvenSmallLie.OmegaEightMinus.ActsOn (CFSG.KS.Raw.unpack 136 8 P) M := fun p hp => by
  have h1 := CFSG.KS.allN_spec h p hp
  rw [CFSG.KLC.E8.strictB_eq', CFSG.KS.bAnd_iff] at h1
  obtain ⟨h1, h2⟩ := h1
  have hm : CFSG.KS.mask 8 = 255 := rfl
  rw [matAppK_eq] at h2
  rw [CFSG.KC.Misc.PairCount.unpack_get hp, hm, hNS p hp, hNI _ (CFSG.EvenSmallLie.OmegaEight.matApp_lt _ _)]
  exact ⟨by simpa using h1, Nat.eq_of_beq_eq_true h2⟩

end CFSG.KC.O8

end

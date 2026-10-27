module

public import CFSG.Certificates.Kernel.LocalQTBaseWProved
public import CFSG.Certificates.Kernel.LocalQTPcWSound
import all CFSG.Certificates.Kernel.LocalQTPcWSound

public section

namespace CFSG.KC.LQT.PcW

open CFSG.KC.Enum CFSG.KS CFSG.KS.PF
open CFSG.QuasithinUnique.Ch1.SporLat (idTab)
open CFSG.QuasithinUnique.K1.SporadicPerm (img)

variable {n w : Nat}

theorem rep_of_bw (hn : n < 2 ^ 32) (hw : 0 < w) {idn c : Nat} {t : Array Nat}
    (hid : Rep n w idn (idTab n)) (h : CFSG.KC.LQT.BW.Pf.Rep n w c t) :
    Rep n w (pcS n w (mask w) idn c) t := by
  obtain ⟨h1, h2⟩ := h
  have hpg : ∀ i < n, pg w (mask w) c i = img t i := fun i hi => (h2 i hi).2
  have hidg : ∀ j < n, pg w (mask w) idn j = j := fun j hj => by
    rw [← rep_get hid j hj, idTab, getElem!_pos _ j (by simpa using hj), Array.getElem_range]
  have hval : ∀ i < n, pg w (mask w) (pcS n w (mask w) idn c) i = img t i := fun i hi => by
    rw [pcS_eq, pg_pcomp hn hi, hpg i hi, hidg _ (h2 i hi).1]
  refine ⟨h1, fun i hi => ?_, ?_, fun i hi => ?_⟩
  · rw [hval i hi, img, Array.getD_eq_getD_getElem?, getElem!_pos t i (by omega),
      Array.getElem?_eq_getElem (by omega), Option.getD_some]
  · rw [pcS_eq]
    exact pcomp_shr _ _ hn hw
  · rw [hval i hi]
    exact (h2 i hi).1

end CFSG.KC.LQT.PcW

end

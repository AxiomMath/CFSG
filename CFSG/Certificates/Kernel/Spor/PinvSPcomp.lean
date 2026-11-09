module

public import CFSG.Certificates.Kernel.Spor.PinvSSound

public section

namespace CFSG.KS.PinvS

open CFSG.KC.Enum CFSG.KS CFSG.KS.Prim CFSG.KS.PF

variable {n w : Nat}

theorem inv_of_pcomp {g gi : Nat} (hg : canonK n w (mask w) (n * w) g = true)
    (hgi : canonK n w (mask w) (n * w) gi = true) (h : pcomp n w (mask w) g gi = pidn n w) :
    InjK n w g ∧ InjK n w gi ∧
      ∀ i < n, pg w (mask w) g (pg w (mask w) gi i) = i ∧
        pg w (mask w) gi (pg w (mask w) g i) = i := by
  obtain ⟨hn, hw, -, hlt⟩ := canon_facts hg
  have hlti := (canon_facts hgi).2.2.2
  have h1 : ∀ i < n, pg w (mask w) g (pg w (mask w) gi i) = i := fun i hi => by
    have h' : pg w (mask w) (pcomp n w (mask w) g gi) i = pg w (mask w) (pidn n w) i :=
      congrArg (fun p => pg w (mask w) p i) h
    rwa [pg_pcomp (by omega) hi, pg_pidn hn hw hi] at h'
  have hI : InjK n w gi :=
    ⟨hlti, fun a ha b hb e => by rw [← h1 a ha, ← h1 b hb, e]⟩
  have h2 : ∀ i < n, pg w (mask w) gi (pg w (mask w) g i) = i := fun i hi => by
    obtain ⟨x, hx, rfl⟩ := surj_of_injK hI i hi
    rw [h1 x hx]
  refine ⟨⟨hlt, fun a ha b hb e => ?_⟩, hI, fun i hi => ⟨h1 i hi, h2 i hi⟩⟩
  rw [← h2 a ha, ← h2 b hb, e]

theorem pinvS_of_pcomp {g gi : Nat} (hg : canonK n w (mask w) (n * w) g = true)
    (hgi : canonK n w (mask w) (n * w) gi = true) (h : pcomp n w (mask w) g gi = pidn n w) :
    pinvS n w (mask w) g = gi := by
  obtain ⟨-, hw, -, -⟩ := canon_facts hg
  obtain ⟨-, -, hgi0, hlti⟩ := canon_facts hgi
  obtain ⟨hI, -, hinv⟩ := inv_of_pcomp hg hgi h
  have hc := canonK_pinvS hg hI
  refine eq_of_fields (w_pos hw) (canon_facts hc).2.2.1 hgi0 fun i hi => ?_
  have := pg_pinvS (by omega) hI (hlti i hi)
  rwa [(hinv i hi).1] at this

end CFSG.KS.PinvS

end

module

public import CFSG.ClassicalInvolution.Q3.TL4ExitDichT
public import CFSG.ClassicalInvolution.Q3.TL4ExitDichX
public import CFSG.ClassicalInvolution.Q3.TL4S289U2

public section

namespace CFSG.ClassicalInvolution.Q3.TL4

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic

theorem secIdExitDich3_proved :
    SecIdExitDich3 := by
  intro X _ _ Φ _ _ _ _ hE hF M hM a ha P hP β hβ2 hβP
  obtain ⟨-, -, R, S, z, hm, heq, -, hout⟩ := hE
  obtain ⟨hs, -, hF⟩ := hF
  have := hs
  exact MF163.Concl163Syl.of_conj hm.datum
    (MF163.concl163Syl_of_exit hm (hout.imp_left And.left) hF) (by rw [heq]; exact hM) ha hP
    hβ2 hβP

end CFSG.ClassicalInvolution.Q3.TL4

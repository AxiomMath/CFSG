module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinE4tModel
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinE4tSp6
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinE4tO8

public section

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThmE

open CFSG.ClassicalInvolution.Q3.TL4

theorem e189E4ModelT_of_certs :
    E189E4ModelT := by
  intro M _ _ hM
  rcases hM with hM | hM
  · obtain ⟨e⟩ := CFSG.EvenSmallLie.Sp6.nonempty_mulEquiv_co3X36 hM
    exact e189E4Wt_of_model CFSG.Sporadic.Schreier.Co3.co3X36 E4Sp6.K0
      (fun K s hq hinv htw => exists_emb_of_ident e
        (fun K s hd => E4Sp6.ident_ambient hd) hq hinv htw)
      (fun sc hsc h hh t ht hst hne => E4Sp6.twinT_fin hsc hh ht hst hne)
  · obtain ⟨e⟩ := CFSG.EvenSmallLie.OmegaEight.nonempty_mulEquiv_omegaT hM
    exact e189E4Wt_of_model CFSG.EvenSmallLie.OmegaEight.omegaT E4O8.K0
      (fun K s hq hinv htw => exists_emb_of_ident e
        (fun K s hd => E4O8.ident_omega hd) hq hinv htw)
      (fun sc hsc h hh t ht hst hne => E4O8.twinT_fin hsc hh ht hst hne)

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThmE

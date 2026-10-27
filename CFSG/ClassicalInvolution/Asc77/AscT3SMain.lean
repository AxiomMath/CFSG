module

public import CFSG.ClassicalInvolution.Asc77.AscT3SOrb
public import CFSG.ClassicalInvolution.Asc77.AscT3SC3
public import CFSG.ClassicalInvolution.Asc77.AscT3RFinal

public section

namespace CFSG.ClassicalInvolution.Asc77.T3CII

open CFSG.ClassicalInvolution.Generic

variable {p f : ℕ} [Fact p.Prime]

theorem c20_3_of_hyp51 (hH : Res20_7Hyp51 p f) : C20_3 p f := by
  intro G _ _ _ K K' J S R R' W V z t d
  have hex : Hex20 (CoreAssembly.conjClass K) K J W := ⟨d.late_JW, d.late_hW⟩
  exact d.concl20_3_of_mod hex
    (res20_7NoC3_of_hyp51 hH G K K' J S R R' W V z t d (d.concl20_4_of_hex hex))

theorem res20_3_of_hyp51 (hH : Res20_7Hyp51 p f) : Res20_3 p f :=
  res20_3_of_c20_3 (c20_3_of_hyp51 hH)

theorem c20_5_of_hyp51 (hH : Res20_7Hyp51 p f) : C20_5 p f :=
  c20_5_of_res20_7 (res20_7_of_hyp51 hH)

theorem t3CaseII_of_hyp51 (hH : Res20_7Hyp51 p f) (hP1 : Res10bP1 p f) (hY : Res10aY p f) :
    T3CaseII p f :=
  t3CaseII_of_residuals p f (res20_3_of_hyp51 hH) (res20_7_of_hyp51 hH) hP1 hY


theorem c20_3_of_hyp51At (hH : Res20_7Hyp51At p f) : C20_3 p f :=
  c20_3_of_hyp51 (res20_7Hyp51_of_at hH)

theorem res20_3_of_hyp51At (hH : Res20_7Hyp51At p f) : Res20_3 p f :=
  res20_3_of_hyp51 (res20_7Hyp51_of_at hH)

theorem res20_7_of_hyp51At (hH : Res20_7Hyp51At p f) : Res20_7 p f :=
  res20_7_of_hyp51 (res20_7Hyp51_of_at hH)

theorem c20_5_of_hyp51At (hH : Res20_7Hyp51At p f) : C20_5 p f :=
  c20_5_of_hyp51 (res20_7Hyp51_of_at hH)

theorem t3CaseII_of_hyp51At (hH : Res20_7Hyp51At p f) (hP1 : Res10bP1 p f)
    (hY : Res10aY p f) : T3CaseII p f :=
  t3CaseII_of_hyp51 (res20_7Hyp51_of_at hH) hP1 hY

end CFSG.ClassicalInvolution.Asc77.T3CII

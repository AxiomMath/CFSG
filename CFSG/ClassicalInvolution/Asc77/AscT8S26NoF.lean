module

public import CFSG.ClassicalInvolution.Asc77.AscT8S26E4
public import CFSG.ClassicalInvolution.Asc77.AscT8Route
public import CFSG.ClassicalInvolution.Asc77.AscT8S26Four
public import CFSG.ClassicalInvolution.Asc77.AscT8S26Wyl

public section

namespace CFSG.ClassicalInvolution.Asc77

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Asc77.Thompson

variable {p f : ℕ} [Fact p.Prime]

theorem c27_2_of_c26_2_c26_13 (h2 : C26_2 p f) (h13 : C26_13 p f) : C27_2 p f := by
  intro G _ _ _ Ω K J S R T W z t hs hdisc
  by_contra hne
  have hP : PartIHyp p f Ω := ⟨hs.stand.odd, hs.stand.five, hs.stand.hyp, hs.stand.aEmpty⟩
  have hW : W ∈ WSet Ω := hs.hW.1
  have hnc : ¬ DbarConnected Ω W := thompsonGraphAll G Ω hP hs.stand.mem hne hW
  rcases l7_10_proved G Ω hP W hW hnc with h3 | h4 | h5
  · exact T8.not_muIsoS3_of_std8 hs h3
  · exact h2 G Ω K J S R T W z t hs hdisc h4
  · exact h13 G Ω K J S R T W z t hs hdisc h5

theorem thm8A_of_c26_2_c26_13 (h2 : C26_2 p f) (h13 : C26_13 p f) (h274a : C27_4a p f)
    (h278 : C27_8 p f) : Thm8A p f :=
  thm8A_of_steps c27_nbr_proved c27_setup_proved
    (c27_4_of_steps (c27_2_of_c26_2_c26_13 h2 h13) h274a) h278

theorem thm8A_of_s26_residuals_noF (h2u : C26_2_u p f) (h13 : C26_13_sc p f) (h274a : C27_4a p f)
    (h278 : C27_8 p f) : Thm8A p f :=
  thm8A_of_c26_2_c26_13 (c26_2_of_u h2u) (c26_13_of_sc h13) h274a h278

theorem thm8A_of_s26_split (h2u : C26_2_u p f) (h13 : C26_13_sc p f) (h274a : C27_4a p f)
    (h8E4 : C27_8E4 p f) (h8nE4 : C27_8nE4 p f) : Thm8A p f :=
  thm8A_of_s26_residuals_noF h2u h13 h274a (c27_8_of_split h8E4 h8nE4)

end CFSG.ClassicalInvolution.Asc77

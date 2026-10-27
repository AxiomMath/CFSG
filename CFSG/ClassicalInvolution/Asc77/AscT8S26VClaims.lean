module

public import CFSG.ClassicalInvolution.Asc77.AscT8S26VMu
public import CFSG.ClassicalInvolution.Asc77.AscT8S26VProper

public section

namespace CFSG.ClassicalInvolution.Asc77

variable {p f : ℕ} [Fact p.Prime]

theorem c26_3_S4_of_claims (h752 : L7_5_2 p f) (hMu : Ih8MuTableSect p f) (hT : S26XTop p f)
    (hZ : S26XMuZ2 p f) : C26_3_S4 p f :=
  c26_3_S4_of_x hMu s26XProper_proved (s26XEdgeless_of_muZ2 h752 hZ) hT hZ

theorem c26_2_u_of_claims (h752 : L7_5_2 p f) (hMu : Ih8MuTableSect p f) (hT : S26XTop p f)
    (hZ : S26XMuZ2 p f) : C26_2_u p f :=
  c26_2_u_of_c26_3 (c26_3_S4_of_claims h752 hMu hT hZ)

theorem c26_2_of_claims (h752 : L7_5_2 p f) (hMu : Ih8MuTableSect p f) (hT : S26XTop p f)
    (hZ : S26XMuZ2 p f) : C26_2 p f :=
  c26_2_of_c26_3 (c26_3_S4_of_claims h752 hMu hT hZ)

theorem thm8A_of_s26_claims (h752 : L7_5_2 p f) (hMu : Ih8MuTableSect p f) (h1 : C26_1 p f)
    (hZ : S26XMuZ2 p f) (h13 : C26_13_sc p f) (h274a : C27_4a p f) (h8E4 : C27_8E4 p f)
    (h8nE4 : C27_8nE4 p f) : Thm8A p f :=
  thm8A_of_s26_c26_3 (c26_3_S4_of_claims h752 hMu (s26XTop_of_c26_1 h1) hZ) h13 h274a h8E4 h8nE4

end CFSG.ClassicalInvolution.Asc77

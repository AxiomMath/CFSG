module

public import CFSG.ClassicalInvolution.Asc77.AscT8Final
public import CFSG.ClassicalInvolution.Asc77.AscT8S26Hull
public import CFSG.ClassicalInvolution.Asc77.AscT8S26Four
public import CFSG.ClassicalInvolution.Asc77.AscT8S26Wyl

public section

namespace CFSG.ClassicalInvolution.Asc77

variable {p f : ℕ} [Fact p.Prime]

theorem cf26_of_c26_6 (h6 : C26_6 p f) : CF26 p f :=
  cf26_of_c26_7 (c26_7_of_c26_6 h6)

theorem thm8A_of_s26_residuals (h2u : C26_2_u p f) (h13 : C26_13_sc p f) (h6 : C26_6 p f)
    (h274a : C27_4a p f) (h278 : C27_8 p f) : Thm8A p f :=
  thm8A_of_residuals (c26_2_of_u h2u) (c26_13_of_sc h13) (c26_7_of_c26_6 h6) h274a h278

end CFSG.ClassicalInvolution.Asc77

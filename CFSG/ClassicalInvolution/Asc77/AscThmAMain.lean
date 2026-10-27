module

public import CFSG.ClassicalInvolution.Asc77.AscThmA173
public import CFSG.ClassicalInvolution.Asc77.AscSix67
public import CFSG.ClassicalInvolution.Asc77.AscQuot613

public section

namespace CFSG.ClassicalInvolution.Asc77

variable {p f : ℕ} [Fact p.Prime]

theorem lThmA_of_l6_2 (h62 : L6_2 p f) : LThmA p f :=
  lThmA_of_l6_13 (l6_13 (l6_7 p f h62))

theorem l17_3_of_l6_2 (h62 : L6_2 p f) : L17_3 p f :=
  l17_3_of_l6_13 (l6_13 (l6_7 p f h62))

end CFSG.ClassicalInvolution.Asc77

module

public import CFSG.ClassicalInvolution.Asc77.AscP1SevenCubeKey
public import CFSG.ClassicalInvolution.Asc77.AscP1SevenStar
public import CFSG.ClassicalInvolution.Asc77.AscP1ThompsonTwelve
public import CFSG.ClassicalInvolution.AschTight.Sec7KeyD

public section

namespace CFSG.ClassicalInvolution.Asc77

variable {p f : ℕ} [Fact p.Prime]

theorem thompsonKey : ThompsonKey p f :=
  CFSG.ClassicalInvolution.Disconnected.AschTight.Sec7.l7_1Key p f

theorem thompsonCube : ThompsonCube p f := thompsonCube_of_key thompsonKey

theorem thompsonStar : ThompsonStar p f := thompsonStar_of_key thompsonKey

theorem l7_10_of_clique (h3 : ThompsonClique p f) : L7_10 p f :=
  l7_10_of_inputs thompsonCube thompsonStar h3

theorem l7_12_of_clique_sub (h3 : ThompsonClique p f) (h4 : ThompsonSub p f) : L7_12 p f :=
  l7_12_of_inputs thompsonCube thompsonStar h3 h4

end CFSG.ClassicalInvolution.Asc77

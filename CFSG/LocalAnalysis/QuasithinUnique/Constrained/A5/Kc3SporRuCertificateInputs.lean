module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.Kc3SporPermCode
public import CFSG.LocalAnalysis.QuasithinUnique.K1.SporadicBase
public import CFSG.LocalAnalysis.QuasithinUnique.K1.SporadicRuInputs
public import CFSG.Sporadic.HS.Group

public section

namespace CFSG.QuasithinUnique.A5.Kc3SporRu
open CFSG.QuasithinUnique.K1.SporadicPerm CFSG.QuasithinUnique.A5.Kc3SporPerm
open CFSG.Sporadic.Ru.Native (ruData)

@[expose] def ruPD : PD where
  n := ruData.n
  B := ruB
  G := ruQp.map fun p => ruSLP[p.1]!
  Gi := ruQp.map fun p => ruSLP[p.2]!
  Ts := ruEnum.1
  par := ruEnum.2.1
  cl := ruEnum.2.2

open CFSG.Sporadic.SmallF2 in
@[expose] noncomputable def ruSg : List (J ruData) :=
  ruQp.map fun p => (slpElts (a ruData) (b ruData) ruProg).getD p.1 1

open CFSG.Sporadic.SmallF2 in
@[expose] noncomputable def ruR : Subgroup (J ruData) := Subgroup.closure {x | x ∈ ruSg}

open CFSG.Sporadic.SmallF2 in
noncomputable instance ruAct : MulAction (J ruData) (Fin ruPD.n) :=
  inferInstanceAs (MulAction (J ruData) (Fin ruData.n))

end CFSG.QuasithinUnique.A5.Kc3SporRu

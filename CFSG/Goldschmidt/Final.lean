module

import CFSG.Goldschmidt.Steps.PaperClosure
import CFSG.Goldschmidt.Steps.G37
import CFSG.Goldschmidt.Steps.G76
import CFSG.Goldschmidt.Steps.G310Z
import CFSG.Goldschmidt.Steps.GAssembly
import CFSG.Goldschmidt.Steps.G4
import CFSG.Goldschmidt.Steps.G72
import CFSG.Goldschmidt.Steps.G28
import CFSG.Goldschmidt.Steps.G312
import CFSG.Goldschmidt.Steps.G51
import CFSG.Goldschmidt.Steps.G52
import CFSG.Goldschmidt.Steps.G53
import CFSG.Goldschmidt.Steps.G54
import CFSG.Goldschmidt.Steps.G56
import CFSG.Goldschmidt.Steps.Sec81
import CFSG.Goldschmidt.Steps.Sec82
import CFSG.Goldschmidt.Steps.Sec83
import CFSG.Goldschmidt.Steps.Sec84
import CFSG.Goldschmidt.Steps.Sec86
import CFSG.Goldschmidt.Steps.Sec87
import CFSG.Goldschmidt.Steps.Sec88
import CFSG.Goldschmidt.Steps.Sec89
public import CFSG.Goldschmidt.StatementsG
public import CFSG.Goldschmidt.StatementsG2
public import CFSG.Goldschmidt.StatementsG3

public section

namespace CFSG.Goldschmidt

theorem G7 :
    S_G7 :=
  G7_of G4 (G72_of G4 (G71_of_steps G37 G311)) (G76_of G37 G311)

theorem coreStatement_of_G89
    (h89 : S_G89) : CoreStatement :=
  coreStatement_of_paperSteps G37 G311 (G76_of G37 G311) h89

theorem G51 :
    S_G51 :=
  have h55 := G55_of G31 G37 (G52_of G37) (G53_of G37) (G54_of G28 G37)
  G51_of h55 (G56_of G31 G37 (G53_of G37) h55)

theorem G64 :
    S_G64 :=
  G64_of_steps G37 G311

theorem G89 :
    S_G89 :=
  have h81 := G81_of G64 G31 G37
  have h83 := G83_of G64 G31 (G82_of G64 G31 G37 G35 G51 G312)
  have h86 := G86_of h81 h83 (G84_of G64 G31 G37 h83)
  G89_of (G87_of h86) (G88_of h81 h86)

theorem G8 :
    S_G8 :=
  G8_of G4 G89

theorem coreStatement :
    CoreStatement :=
  coreStatement_of_G89 G89

theorem topStatement :
    TopStatement :=
  topStatement_of_coreStatement coreStatement

end CFSG.Goldschmidt

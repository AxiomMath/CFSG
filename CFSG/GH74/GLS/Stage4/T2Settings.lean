module

public import CFSG.GH74.GLS.Stage4.T2Q9
public import CFSG.GH74.GLS.Stage4.T2Q3n
public import CFSG.GH74.GLS.Stage4.T2F1Gen

public section

namespace CFSG.GH74.GLS.Stage4.Rest

theorem q9SettingOf_final
    (hRemL : Ch6T2Rem) (hOrd : Ch6P56bOrder) :
    Stage4.Q9.Q9SettingOf :=
  q9SettingOf_of_order hRemL hOrd

theorem q3nSettingOf_final
    (hRemL : Ch6T2Rem) (hF1 : Ch6T2F1PrimeGe5) (hOrd : Ch6P56bOrder) :
    Stage4.Q3n.Q3nSettingOf :=
  q3nSettingOf_of_order hRemL (ch6T2F1Gt9_of_leaf hRemL hF1) hOrd

end CFSG.GH74.GLS.Stage4.Rest

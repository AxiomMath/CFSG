module

public import Certificates.Data.TabMSevenQ
public import CFSG.Certificates.Kernel.KDenseP.MonThreeB.Pairs

public section

namespace CFSG.KC.KDenseP.Q7

open CFSG.Monster.AxisCount CFSG.KC.KDenseP.MonThreeB CFSG.HardMathSupport.Dickson.I271.TabMSeven
  CFSG.YGroups.Y443

@[expose] def q7Eqs : Prs :=
  [(powL 7 qZ, []), (powL 5 qF, []), (qT ++ qT, []), (qZ ++ qF, qF ++ qZ), (qZ ++ qT, qT ++ qZ),
    (qF ++ qT, qT ++ qF), (qZ ++ qA, qA ++ qZ), (qZ ++ qX, qX ++ qZ), (powL 4 qA, qT),
    (powL 2 qX, qT), (qA ++ qX ++ qA, qX)]

@[expose] def q7Nes : Prs :=
  [(qZ ++ [.xi, .tau], [.xi, .tau]), (qF ++ [.xi, .tau], [.xi, .tau]), (qT ++ [.tau], [.tau])]

end CFSG.KC.KDenseP.Q7

end

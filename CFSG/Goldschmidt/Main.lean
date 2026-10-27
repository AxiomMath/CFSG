module

public import CFSG.Goldschmidt.Assembly
public import CFSG.Goldschmidt.StatementsX
import CFSG.Goldschmidt.Steps.GoldType
import CFSG.Goldschmidt.Steps.QSForm
import CFSG.Goldschmidt.Steps.IHConseq
import CFSG.Goldschmidt.Steps.Red1
import CFSG.Goldschmidt.Steps.Red2
import CFSG.Goldschmidt.Steps.Red2Split
import CFSG.Goldschmidt.Steps.Red2Omega
import CFSG.Goldschmidt.Steps.BaseB1
import CFSG.Goldschmidt.Steps.BaseB2
import CFSG.Goldschmidt.Steps.BaseB3
import CFSG.Goldschmidt.Steps.PropHSetup
import CFSG.Goldschmidt.Steps.NonComp
import CFSG.Goldschmidt.Steps.RankTwo
import CFSG.Goldschmidt.Steps.Rank2List
import CFSG.Goldschmidt.Steps.PropHReduce
import CFSG.Goldschmidt.Steps.LemmaX
import CFSG.Goldschmidt.Steps.CorX
import CFSG.Goldschmidt.Steps.Completion
import CFSG.Goldschmidt.Steps.Balance

public section

namespace CFSG.Goldschmidt

theorem coreStatement_of_propH_compType
    (hH : S_propH_compType) : CoreStatement :=
  N41 N20 (N21_of N19) (N22_of N19) (N23_of (N17_of N11b) N19) simpleConcl B3setup
    (N24_of N11a) (N25_of N11a) B2setup (N26_of N11a) (N27_of N11a N11c N13) (N28_of N11b)
    (N29_of N11a N11b) N30 N31_exists N31 N39 (N40_of N15) hH

theorem topStatement_of_propH_compType
    (hH : S_propH_compType) : TopStatement :=
  topStatement_of_coreStatement (coreStatement_of_propH_compType hH)

theorem coreStatement_of_open
    (hZ : S_caseZ) (h1 : S_HC1) (h2 : S_HC2) : CoreStatement :=
  coreStatement_of_propH_compType
    (propH_compType_of lemmaX (corX_of (N37_of N36) lemmaX) hZ h1 h2)

theorem topStatement_of_open
    (hZ : S_caseZ) (h1 : S_HC1) (h2 : S_HC2) : TopStatement :=
  topStatement_of_coreStatement (coreStatement_of_open hZ h1 h2)

end CFSG.Goldschmidt

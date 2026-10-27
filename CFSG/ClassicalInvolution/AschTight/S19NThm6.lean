module

public import CFSG.ClassicalInvolution.AschTight.S19NMain
public import CFSG.ClassicalInvolution.AschTight.S19CCons
public import CFSG.ClassicalInvolution.AschTight.S19FFactM1
public import CFSG.ClassicalInvolution.AschTight.S19LMain
public import CFSG.ClassicalInvolution.AschTight.S19RMain
public import CFSG.ClassicalInvolution.AschTight.T6AThm6
public import CFSG.ClassicalInvolution.AschTight.S19KFG2

public section

namespace CFSG.ClassicalInvolution.Disconnected.AschTight.S19N

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic

variable (p f : ℕ) [Fact p.Prime]

theorem c19_16F_of (h11b : C19_11bTmp p f) (hFG2 : S19Q.FactFG2) : C19_16FTmp p f :=
  c19_16FTmp_of_split
    (S19C.c19_16FNe9_of'
      (S1916.c19_16Inv_of p f h11b
        (S1916.c19_14SC_of p f (S1916.c19_14Z_of p f (S19Q.c19_14C_of p f h11b)))
        goldschmidtB3Tmp_holds)
      S19F.factM1 (S19L.c19_16FusL3Graph_of' p f h11b hFG2))
    (c19_16F9_of' p f h11b)

theorem thm6A_of_c19_11b (h11b : C19_11bTmp p f) (hFG2 : S19Q.FactFG2) : Asc77.Thm6A p f :=
  T6A.thm6A_of_c19_main p f (S19R.c19_main_of p f h11b (c19_16F_of p f h11b hFG2))

theorem thm6A_of_c19_11b' (h11b : C19_11bTmp p f) : Asc77.Thm6A p f :=
  thm6A_of_c19_11b p f h11b S19K.factFG2

end CFSG.ClassicalInvolution.Disconnected.AschTight.S19N

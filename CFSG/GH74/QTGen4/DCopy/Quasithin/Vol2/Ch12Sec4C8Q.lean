module

public import CFSG.Quasithin.Vol2.Ch12Sec4C8Q
public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch12Sec4C8Stmt

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.Quasithin S1248

theorem oddCentQ1248_of_F4 (h331 : Stmt3_3_1_F4) (h1222 : Stmt12_2_2_F4) (hpre : Pre1242_F4) :
    OddCentQ1248_F4 := by
  intro G _ _ T L V U hS U₀ hU₀ _
  obtain ⟨z, hf⟩ := CxFacts.of_F4 h331 h1222 hpre hS.cx hS.quot
  have hVp : IsPGroup 2 V := hS.cx.hyp.sylow.1.to_le hf.le_T
  exact S1248.oddCoreIn_centralizer_le (hVp.to_le hS.le) hU₀
    fun u hu => Subgroup.centralizer_le (hU₀.trans hS.le) (hf.le_centralizer (hS.le hu))

end CFSG.Quasithin.H13

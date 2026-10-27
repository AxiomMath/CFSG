module

public import CFSG.Goldschmidt.StatementsG3
import CFSG.Goldschmidt.Steps.Sec81
import CFSG.Goldschmidt.Steps.Sec82b
import CFSG.Goldschmidt.Steps.Sec82c
import CFSG.Goldschmidt.Steps.Sec82d
import CFSG.Goldschmidt.Steps.Sec82e
import CFSG.Goldschmidt.Steps.Sec82g
public import CFSG.Goldschmidt.StatementsG
public import CFSG.Goldschmidt.StatementsG2

public section

namespace CFSG.Goldschmidt

open CFSG.Open

theorem G82_of (h64 : S_G64) (h31 : S_G31) (h37 : S_G37) (h35 : S_G35) (h51 : S_G51)
    (h312 : S_G312) : S_G82 := by
  intro G _ _ S A hset h4 a ha ha1 H hH p hp hP1 M hM hPM hMH haF
  obtain ⟨L, c⟩ := Sec82.exists_ctx h64 h31 h37 hset h4 ha ha1 hH hp hP1 hM hPM hMH haF
  have hE := Sec82.componentLayerOf_eq_bot h37 c
  refine Sec82.false_of_ctx h31 h35 hE (Sec82.qCoreOf_two_eq_bot c) (fun q hq hq2 => ?_) c
  by_cases h3 : 3 ≤ CFSG.Open.pRank q (GorensteinWalter.qCoreOf H q)
  · exact Sec82.isCyclic_qCoreOf_of_three_le h64 h51 (G81_of h64 h31 h37) hE c hq hq2 h3
  · exact Sec82.isCyclic_qCoreOf_of_le_two h312 hE c hq hq2 (by omega)

end CFSG.Goldschmidt

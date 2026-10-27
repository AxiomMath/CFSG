module

public import CFSG.Goldschmidt.StatementsG3
import CFSG.Goldschmidt.Steps.Sec81a
import CFSG.Goldschmidt.Steps.Sec81c
public import CFSG.Goldschmidt.StatementsG
public import CFSG.Goldschmidt.StatementsG2

public section

namespace CFSG.Goldschmidt

theorem G81_of (h64 : S_G64) (h31 : S_G31) (h37 : S_G37) : S_G81 := by
  intro G _ _ S A hset h4 a ha ha1 H hH
  obtain ⟨-, hHa⟩ := Sec8.mem_qCoreOf_two_and_eq h64 hset h4 ha ha1 hH
  refine ⟨hHa, (Sec8.eq_oddCoreOf_sup hset h4 ha ha1 hH).2,
    Sec8.commutator_ne_bot hset h4 ha ha1 hH, ?_⟩
  intro p hp hp2 V hVF hVp hVc hVC M hM haVM
  by_contra hMH
  exact Sec8.false_of_le_sup h31 h37 h64 hset h4 ha ha1 hH hp hp2 hVF hVp hVc hVC hM hMH haVM

end CFSG.Goldschmidt

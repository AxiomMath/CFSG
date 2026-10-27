module

public import CFSG.Certificates.Kernel.O8EnumProved
public import CFSG.Certificates.Kernel.O8FindProved
public import CFSG.Certificates.Kernel.O8ListProved
public import CFSG.Certificates.Kernel.O8MulProved
public import CFSG.Certificates.Kernel.O8VecProved

public section

namespace CFSG.KC.O8

open CFSG.EvenSmallLie.OmegaEight.Stage2

theorem enum_sound {G GI D : Nat → Nat} {ng m z nb : Nat} (hm : m ≤ 256 * nb) (hm' : m < 2 ^ 17)
    (hng : ng < 32) (hh : enumHeadOK G GI ng m D z = true)
    (hb : ∀ b < nb, enumBlockOK G ng m D b = true) :
    enumOK (genPairsK G GI ng) (decE D m) = true := by
  apply enum_sound_proved <;> assumption

theorem exists_of_enMemK {D : Nat → Nat} {m k : Nat} (h : enMemK D m k = true) :
    ∃ i < m, enKey D i = k := by
  apply exists_of_enMemK_proved <;> assumption

theorem contains_decE {D : Nat → Nat} {m k : Nat} (h : enNotMemK D m k = true) :
    (decE D m).keys.contains k = false := by
  apply contains_decE_proved <;> assumption

theorem mulK_eq (a b : ℕ) : mulK a b = mul12K a b := by
  apply mulK_eq_proved

theorem mulVecK_eq (k v : ℕ) : mulVecK k v = mulVec12K k v := by
  apply mulVecK_eq_proved

theorem fixCount_eq (k : ℕ) :
    fixCount k = CFSG.KLie.CT.sumN 4096 fun v => nIf(Nat.beq (mulVec12K k v) v, 1, 0) := by
  apply fixCount_eq_proved

theorem decE_toList (D : Nat → Nat) (m : Nat) :
    (decE D m).keys.toList = (List.range m).map (enKey D) := by
  apply decE_toList_proved

theorem memK_decE_eq {D : Nat → Nat} {m : Nat} (hs : sortedK (decE D m).keys = true)
    (hm : m < 2 ^ 17) (k : ℕ) : memK (decE D m).keys k = enMemK D m k := by
  apply memK_decE_eq_proved <;> assumption

theorem contains_decE_eq (D : Nat → Nat) (m k : Nat) :
    (decE D m).keys.contains k = !enNotMemK D m k := by
  apply contains_decE_eq_proved

end CFSG.KC.O8

end

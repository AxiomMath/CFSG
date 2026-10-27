module

public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Core
public import CFSG.Monster.GMS.Facts.BabyTables
public import CFSG.Monster.GMS.OrbitCount

public section

namespace CFSG.HardMathSupport.Timmesfeld.SporadicBalance

open CFSG.Blueprint CFSG.Monster.GMS

theorem card_isPGroup_five_le_of_babyInv {k : Fin 4} {t : NativeSporadic.B} (ht : BabyInv k t)
    {Q : Subgroup NativeSporadic.B} (hQ : IsPGroup 5 Q)
    (hle : Q ≤ Subgroup.centralizer ({t} : Set NativeSporadic.B)) : Nat.card Q ≤ 5 ^ 3 := by
  have hdvd := Subgroup.card_dvd_of_le hle
  rw [ht.2] at hdvd
  refine card_le_of_isPGroup_of_dvd (by norm_num) hQ ?_ hdvd
  fin_cases k <;> norm_num [babyCentOrder]

end CFSG.HardMathSupport.Timmesfeld.SporadicBalance

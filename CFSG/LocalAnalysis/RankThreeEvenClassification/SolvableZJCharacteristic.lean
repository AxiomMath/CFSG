module

public import CFSG.LocalAnalysis.RankThreeEvenClassification.ZJCharacteristic
public import CFSG.LocalAnalysis.RankThreeEvenClassification.SolvableActionStability

public section

open CFSG.Open

namespace CFSG.RankThreeEvenClassification.Helpers

universe u

theorem solvable_stable_normal_prime_actions {G : Type u}
    [Group G] [Finite G] [Group.IsSolvable G]
    (prime : ℕ) (hprime : prime.Prime) (hodd : Odd prime)
    (halternative : 5 ≤ prime ∨ Odd (Nat.card G)) : StableNormalPrimeActions prime G := by
  intro normal hnormal hpgroup
  have : normal.Normal := hnormal
  exact solvable_prime_stable_action prime hprime hodd hpgroup MulAut.conjNormal halternative

theorem solvable_thompsonCenterOf_characteristic {G : Type u}
    [Group G] [Finite G] [Group.IsSolvable G]
    (prime : ℕ) (hprime : prime.Prime) (hodd : Odd prime)
    (sylow : Sylow prime G)
    (hcharacteristic : Subgroup.centralizer (pCore prime G : Set G) ≤ pCore prime G)
    (halternative : 5 ≤ prime ∨ Odd (Nat.card G)) :
    (thompsonCenterOf (sylow : Subgroup G)).Characteristic := by
  exact thompsonCenterOf_characteristic_of_stable_normal_actions prime hprime hodd sylow
    hcharacteristic (solvable_stable_normal_prime_actions prime hprime hodd halternative)

end CFSG.RankThreeEvenClassification.Helpers

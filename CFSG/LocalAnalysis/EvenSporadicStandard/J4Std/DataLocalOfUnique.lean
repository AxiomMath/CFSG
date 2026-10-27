module

public import CFSG.LocalAnalysis.EvenSporadicStandard.J4Std.DataLocalMap
public import CFSG.LocalAnalysis.EvenSporadicStandard.J4Std.DataLocalJ

public section

namespace CFSG.EvenSporadicStandard.J4Std

open CFSG.Sporadic.J4 CFSG.Sporadic.J4.QT

theorem localData_J4_of_unique
    {G : Type} [Group G] (ι : CFSG.Sporadic.J4.J →* G) (hι : Function.Injective ι)
    (huniq : ∀ A : Subgroup CFSG.Sporadic.J4.J, A ≤ P0 → (∀ a ∈ A, a * a = 1) →
      (∀ a ∈ A, ∀ b ∈ A, a * b = b * a) → 2 ^ 11 ≤ Nat.card A → A = Eg uJ 11) :
    LocalData ι.range ((Eg uJ 11).map ι) (P0.map ι) :=
  DataLocal.localData_map ι hι (DataLocal.localData_J_of_unique huniq)

end CFSG.EvenSporadicStandard.J4Std

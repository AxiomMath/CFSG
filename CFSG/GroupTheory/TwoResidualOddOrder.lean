module

public import CFSG.Quasithin.Background.F6Basic

public section

namespace CFSG.GroupTheory

open CFSG.Quasithin

variable {G : Type*} [Group G] [Finite G]

theorem le_twoResidual_of_odd_card {H X : Subgroup G} (hXH : X ≤ H)
    (hodd : Odd (Nat.card X)) : X ≤ twoResidual H := fun x hx =>
  CFSG.Quasithin.F6.mem_twoResidual_of_odd (hXH hx)
    (hodd.of_dvd_nat (Subgroup.orderOf_dvd_natCard X hx))

end CFSG.GroupTheory

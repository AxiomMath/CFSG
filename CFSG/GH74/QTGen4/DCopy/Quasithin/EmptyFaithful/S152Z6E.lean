module

public import CFSG.Quasithin.EmptyFaithful.S152Z6E
public import CFSG.GH74.QTGen4.DCopy.Quasithin.EmptyFaithful.S152UOff

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits
open scoped commutatorElement

namespace S152Z6

variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G]

theorem input15209Offender_proved_F4 (h15201 : StageLemma15201_F4) : Input15209Offender_F4 := by
  intro G _ _ T Mc M hs H hH hc hW A hA
  obtain ⟨φ⟩ := hW
  rcases relIndex_delta_two_or_four ⟨φ⟩ hA with h2 | h4
  · have hVH : V154 T Mc M ≤ H := (S152N.V154_le_T hs).trans hH.1.1
    have hUH : conjClosure (V154 T Mc M) H ≤ H :=
      conjClosure_le fun h hh z hz => H.mul_mem (H.mul_mem hh (hVH hz)) (H.inv_mem hh)
    refine ⟨A, le_rfl, h2, ?_⟩
    rw [S152U.card_inf_centralizer_eq hA.1 hc.elemAbelian hUH]
  · exact offender_of_data4 hs hH (h15201 G T Mc M hs) φ (data4_of_delta hs hH hc hA h4)

theorem input15209Lift_proved_F4 (h15201 : StageLemma15201_F4) (h1511one : StageLemma15111One) :
    Input15209Lift_F4 :=
  input15209Lift_of_offender_F4 h1511one (input15209Offender_proved_F4 h15201)

end S152Z6

end CFSG.Quasithin

module

public import CFSG.Quasithin.H13.A6S1372L76Od2
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.A6S1372L76Od1

public section

namespace CFSG.Quasithin.H13.A6

open Equiv CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin CFSG.LieType.BorelTits
open CFSG.QuasithinUnique.Bridge
open scoped Pointwise IsMulCommutative Matrix

namespace Setting4

variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G] {T L V : Subgroup G} {S : Setting4 G T L V}

theorem false_of_comm_odd_F4 (h139 : Stmt13_3_9_F4)
    (h37 : A37ForSQTK) (h38 : A38ForSQTK) (h13315 : Stmt13_3_15_F4) {H : Subgroup G}
    (hH : H ∈ S.Hz) [IsMulCommutative ↥(conjClosure S.V3 H)] {K : Subgroup G}
    (hK : K ∈ cComp H)
    (hmod : (∃ n, Odd n ∧ BinaryNaturalSL (autSec (autOn K (conjClosure S.V3 H)) ⊤
          ((fsuV1 T V).subgroupOf (conjClosure S.V3 H)))
        (commV (autSec (autOn K (conjClosure S.V3 H)) ⊤
          ((fsuV1 T V).subgroupOf (conjClosure S.V3 H))))
        (fixV (autSec (autOn K (conjClosure S.V3 H)) ⊤
            ((fsuV1 T V).subgroupOf (conjClosure S.V3 H))) ⊓
          commV (autSec (autOn K (conjClosure S.V3 H)) ⊤
            ((fsuV1 T V).subgroupOf (conjClosure S.V3 H)))) 3 n) ∨
        AlternatingNatural (autSec (autOn K (conjClosure S.V3 H)) ⊤
            ((fsuV1 T V).subgroupOf (conjClosure S.V3 H)))
          (commV (autSec (autOn K (conjClosure S.V3 H)) ⊤
            ((fsuV1 T V).subgroupOf (conjClosure S.V3 H))))
          (fixV (autSec (autOn K (conjClosure S.V3 H)) ⊤
              ((fsuV1 T V).subgroupOf (conjClosure S.V3 H))) ⊓
            commV (autSec (autOn K (conjClosure S.V3 H)) ⊤
              ((fsuV1 T V).subgroupOf (conjClosure S.V3 H)))) 5)
    (hcomm : ∀ x (hx : x ∈ S.X1375), ∀ y ∈ autSec (autOn K (conjClosure S.V3 H)) ⊤
        ((fsuV1 T V).subgroupOf (conjClosure S.V3 H)),
      A6Mod.secAct (le_normalizer_conjClosure S.V3 H) (S.le_normalizer_UV1 hH)
          ⟨x, X1375_le_H hH hx⟩ * y =
        y * A6Mod.secAct (le_normalizer_conjClosure S.V3 H) (S.le_normalizer_UV1 hH)
          ⟨x, X1375_le_H hH hx⟩) :
    False := by
  refine false_of_trivial_on_UK_F4 hH hK rfl (X1375_le_H hH) h139 h37 h38 h13315
    (fun x hx y hy => ?_) V3_le_commutator_X1375 (A6L76Od.faithful_of_odd hmod)
    (fun x hx => ?_)
  · rw [hcomm x hx y hy, mul_inv_cancel_right]
    exact hy
  · obtain ⟨k, hk⟩ := pow_eq_one_of_mem_L1 (X1375_le_L1 hx)
    refine A6L76Od.trivial_of_commute_odd hmod (hcomm x hx) (k := k) ?_
    have h1 : (⟨x, X1375_le_H hH hx⟩ : ↥H) ^ (18 * 2 ^ k) = 1 :=
      Subtype.ext (by simpa using hk)
    rw [← map_pow, h1, map_one]

end Setting4

end CFSG.Quasithin.H13.A6

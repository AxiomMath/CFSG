module

public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.A6S1513
public import CFSG.Quasithin.H13.A5SitY
public import CFSG.Quasithin.H13.A6S4L0
public import CFSG.Quasithin.H13.A6S4L1

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin

namespace A6.Setting4

variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G] {T L V : Subgroup G} (S : A6.Setting4 G T L V)

@[expose] def toA5Sit_F4
    (hNS : ¬ LieModel G .PSp 3 2 1) (h13315 : Stmt13_3_15_F4)
    (h1356two : Input1356Two_F4) {H : Subgroup G} (hH : H ∈ S.Hz)
    (hna : ¬ IsElemAbelian 2 (conjClosure S.V3 H)) : A5Sit G T V (fsuV1 T V) S.V3 S.L1 H where
  L := L
  h13 := S.h13
  hF := S.hypF91_F4 hNS h13315 h1356two hH
  L1_eq := rfl
  card_V := S.card_V
  card_V3 := S.card_V3
  nonabelian := hna
  isPGroup_sup := fun _ hg hlt => S.isPGroup_sup_of_lt_F4 hNS h1356two h13315 hH hg hlt
  comm_centralizer := S.comm_centralizer_V3_F4 h13315 H
  commutator_V_L1 := S.commutator_V_L1
  commutator_V3_L1 := S.commutator_V3_L1
  NV_le := S.NV_le_M

@[expose] noncomputable def toA5SitY_F4
    (hNS : ¬ LieModel G .PSp 3 2 1) (h13315 : Stmt13_3_15_F4)
    (h1356two : Input1356Two_F4) {H : Subgroup G} (hH : H ∈ S.Hz)
    (hna : ¬ IsElemAbelian 2 (conjClosure S.V3 H)) (hhat : ¬ IsHatA6 L) :
    A5SitY (S.toA5Sit_F4 hNS h13315 h1356two hH hna) S.L1 :=
  (S.toA5Sit_F4 hNS h13315 h1356two hH hna).toA5SitY (S.cL1 hhat : G) (S.cL1_mem hhat)
    (S.cL1_cube hhat) (S.cL1_not_mem hhat) fun _ hx => S.L1_decomp hhat hx

@[expose] noncomputable def toA5SitY_L0_F4
    (hNS : ¬ LieModel G .PSp 3 2 1) (h13315 : Stmt13_3_15_F4)
    (h1356two : Input1356Two_F4) {H : Subgroup G} (hH : H ∈ S.Hz)
    (hna : ¬ IsElemAbelian 2 (conjClosure S.V3 H)) (hhat : IsHatA6 L) :
    A5SitY (S.toA5Sit_F4 hNS h13315 h1356two hH hna) (l0 L) where
  Y_le_L1 := S.l0_le_L1
  normalizer_le := fun _ hx => S.normalizer_le_l0 hx.2
  oTwoRes_eq := oTwoRes_oTwoRes (o2Z L)
  c := Classical.choose (l0_decomp hhat)
  c_mem := (Classical.choose_spec (l0_decomp hhat)).1
  c_cube := (Classical.choose_spec (l0_decomp hhat)).2.1
  c_not_mem := (Classical.choose_spec (l0_decomp hhat)).2.2.1
  decomp := (Classical.choose_spec (l0_decomp hhat)).2.2.2

end A6.Setting4

end CFSG.Quasithin.H13

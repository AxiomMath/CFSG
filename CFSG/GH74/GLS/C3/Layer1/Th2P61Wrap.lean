module

public import CFSG.GH74.GLS.C3.Layer1.Th2P61Strong
public import CFSG.GH74.GLS.C3.Layer1.Th2BalK10Proof

public section

namespace CFSG.GH74.GLS.Th2.Obs

open CFSG CFSG.GH74.GLS

theorem exists_obstr52
    (hGKF : Generic.GenericKnownFacts) (hE2 : E2.E2ComponentFacts) (hL34 : B_gen4_noL34_elem)
    {G : Type} [Group G] [Finite G] (hG : C3Hyp G) {B : Subgroup G} (hB : IsE 4 ⊤ B)
    (hnot : ¬ IsWeakKBal 2 B) : ∃ (b : G) (J : Subgroup G), Obstr52 B b J :=
  exists_obstr52_of_comp hB.2.1
    (fun _ ha _ hL hnb => (Th2.Bal.component_local hGKF hE2 b_ivk_10_5 hL34 hG ha hL).2 hnb) hnot

end CFSG.GH74.GLS.Th2.Obs

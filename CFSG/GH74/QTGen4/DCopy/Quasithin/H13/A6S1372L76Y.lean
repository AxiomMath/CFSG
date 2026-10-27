module

public import CFSG.Quasithin.H13.A6S1372L76Y
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.A6S13812

public section

namespace CFSG.Quasithin.H13.A6

open Equiv CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin CFSG.LieType.BorelTits
open CFSG.QuasithinUnique.Bridge
open scoped IsMulCommutative Pointwise

namespace Setting4

variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G] {T L V : Subgroup G} (S : Setting4 G T L V)

include S

variable {S}

variable (S)

theorem lem1375_seven_F4 (h139 : Stmt13_3_9_F4) (h37 : A37ForSQTK)
    (h38 : A38ForSQTK) {H : Subgroup G} (hH : H ∈ S.Hz) [IsMulCommutative ↥(conjClosure S.V3 H)]
    {K : Subgroup G} (hK : K ∈ cComp H) (hXK : S.X1375 ≤ K) (hL1K : ¬ S.L1 ≤ K)
    (hrad : ∀ N : Subgroup ↥(autSec (autOn K (conjClosure S.V3 H)) ⊤
        ((fsuV1 T V).subgroupOf (conjClosure S.V3 H))), N.Normal → Group.IsSolvable ↥N → N = ⊥) :
    ¬ S.L1 ≤ S.X1375 ⊔ centralizerMod (pCoreOf 2 K) S.L1 K := by
  intro hyp
  by_cases hhat : IsHatA6 L
  · rw [S.X1375_of_hat hhat] at hXK hyp
    have P : S14.PlusData S (l1plus T L V) := S14.plusData_l1plus S (S.hatL1Plus hhat)
    have hHK := le_normalizer_of_plus hH h37 h38 P hK hXK hrad
    have hTH : T ≤ H := le_sup_right.trans hH.1.1
    have hL1H : S.L1 ≤ H := le_sup_left.trans hH.1.1
    have h0 := S.l0_le_centralizerMod hhat (hL1H.trans hHK) (hTH.trans hHK) hyp
    have hKM : K ≤ Subgroup.normalizer (L : Set G) :=
      (S.le_normalizer_l0_of hH hK h0).trans (S.normalizer_l0_le_M hhat)
    exact (S.lem13812_one_F4 h139 h37 h38 hH hK).1 hKM
  · rw [S.X1375_of_not_hat hhat] at hXK
    exact hL1K hXK

end Setting4

end CFSG.Quasithin.H13.A6

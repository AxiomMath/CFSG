module

public import CFSG.Quasithin.H13.GoldschmidtM22EndN4c
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.GoldschmidtM22EndCtx

public section

namespace CFSG.Quasithin.H13.GM22

open CFSG.Open CFSG.Blueprint CFSG.Quasithin.E3 CFSG.Quasithin

variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G] {T M L V : Subgroup G}

namespace KData

variable {g : G} {D : Subgroup G} (hk : KData T L V g D) (h : Hyp6Sec2 G T M L V)
  (hZ : Nat.card (quasithinOmegaOneCenter T) = 2)

include h in

theorem card_V0_F4 (h6211 : Stmt6_2_11_F4) : Nat.card ↥(V ⊓ CHU T L V) = 8 := by
  have h1 := Subgroup.relIndex_mul_card (H := V ⊓ CHU T L V) (K := V)
  rw [inf_eq_left.mpr (inf_le_left : V ⊓ CHU T L V ≤ V), relIndex_V_CHU_F4 h h6211,
    card_V h] at h1
  omega

include hk h hZ in

theorem card_V1_F4 (h6211 : Stmt6_2_11_F4) : Nat.card ↥(conjSubgroup V g ⊓ CHU T L V) = 8 := by
  rw [hk.V1_eq h hZ, CFSG.QuasithinUnique.C5.card_conjSubgroup, card_V0_F4 h h6211]

include hk h hZ in

theorem exists_mul_V0_V1_F4 (h6211 : Stmt6_2_11_F4) :
    ∀ d ∈ D, ∃ u ∈ V ⊓ CHU T L V, ∃ w ∈ conjSubgroup V g ⊓ CHU T L V, d = u * w := by
  refine exists_mul_eq_of_card_mul hk.V0_le_D hk.V1_le_D ?_
  rw [card_V0_F4 h h6211, hk.card_V1_F4 h hZ h6211, hk.V0_inf_V1 h hZ, hZ, hk.extra.2.1]
  norm_num

end KData

end CFSG.Quasithin.H13.GM22

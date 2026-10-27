module

public import CFSG.Quasithin.H13.L32NLem14413b
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.L32NLem14332h

public section

namespace CFSG.Quasithin.H13.L14413

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin
open scoped IsMulCommutative
open CFSG.Quasithin.H13.L32A

variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G]

theorem quasithinO2QuotientIso_LT_F4 (h1332 : Stmt13_3_2_F4) (h1334 : A6.Stmt13_3_4_F4)
    (h1222 : Stmt12_2_2_F4) {T L V V₂ : Subgroup G} (h : Hyp14310One G T L V)
    (hV₂ : IsL32NPlane T V V₂) :
    quasithinO2QuotientIso (L ⊔ T) (Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)) := by
  obtain ⟨_, S'⟩ := L14332.exists_setting_F4 h1332 h1334 h1222 h hV₂
  have htop : autOn (L ⊔ T) V = ⊤ := by
    have h1 : autOn L V = ⊤ := autOn_eq_top_of_hyp1281One S'.h1281_F4
    rw [eq_top_iff, ← h1]
    exact autOn_mono le_sup_left
  exact quasithinO2QuotientIso_SL3_of (sup_le S'.LV_F4 S'.TV_F4) (fun v hv => S'.sq_V_F4 hv)
    (by rw [S'.card_V_F4]; norm_num) htop S'.isPGroup_cent_sup_F4

end CFSG.Quasithin.H13.L14413

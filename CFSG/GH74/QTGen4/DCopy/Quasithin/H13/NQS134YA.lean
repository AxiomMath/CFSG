module

public import CFSG.Quasithin.H13.NQS134YA
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.StatementsL2

public section

namespace CFSG.Quasithin.H13.NQS134

open Subgroup Equiv CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.QuasithinUnique
open CFSG.Quasithin.H13.A6 CFSG.Quasithin.InternalSec
open scoped IsMulCommutative

variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G] {T L V : Subgroup G}

namespace KWData

variable {S : A6.Setting134 G T L V} {K W : Subgroup G} [IsMulCommutative ↥W]
  (D : KWData S K W)
include D

theorem normalizer_W_le_F4 (h1332 : Stmt13_3_2_F4) :
    normalizer (W : Set G) ≤ normalizer (K : Set G) := by
  obtain ⟨-, ⟨-, -, -, huniqK⟩, -, -⟩ := h1332 G T L S.h13 K D.Kf
  obtain ⟨M', hM', hle⟩ := exists_maxTwoLocal_ge
    (⟨W, D.Wirr.2.1, S.h13.sylow.1.to_le D.W_le_T, rfl⟩ : IsTwoLocal (normalizer (W : Set G)))
  have := huniqK M' hM' ((sup_le D.Wirr.2.2.1 D.TW).trans hle)
  exact this ▸ hle

end KWData

end CFSG.Quasithin.H13.NQS134

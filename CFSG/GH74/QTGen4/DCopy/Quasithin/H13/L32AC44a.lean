module

public import CFSG.Quasithin.H13.L32AC44a
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.L32AC43d

public section

namespace CFSG.Quasithin.H13.L32A.C

open CFSG.Open hiding StatedSL StatedSU StatedSp StatedProj StatedClassicalModel StatedScalars
open CFSG.Blueprint CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin
open CFSG.Assembly.LowTwoRank
open scoped IsMulCommutative

variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G] {T L V H : Subgroup G}

namespace Top43

variable {W K : Subgroup G} (C : Top43 T L V H W K) [IsMulCommutative ↥(conjClosure V H)]
include C

theorem card_autK_of_isPSL34_F4 (h1222 : Stmt12_2_2_F4) (h1332 : Stmt13_3_2_F4)
    (h1334 : A6.Stmt13_3_4_F4) (hP : IsPSL 3 2 2 (cStar K ⧸ Subgroup.center (cStar K))) :
    Odd (Nat.card (Subgroup.center ↥C.autK)) ∧
      Nat.card ↥C.autK = Nat.card (Subgroup.center ↥C.autK) * 20160 ∧
      IsPSL 3 2 2 (↥C.autK ⧸ Subgroup.center ↥C.autK) := by
  obtain ⟨φ⟩ := C.nonempty_quotCenter_autK_F4 h1222 h1332 h1334
  refine ⟨C.odd_card_center_autK_F4 h1222 h1332 h1334, ?_, isPSL_congr φ hP⟩
  obtain ⟨-, F, _, _, hF, ⟨e⟩⟩ := hP
  rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (Subgroup.center ↥C.autK),
    ← Nat.card_congr φ.toEquiv, Nat.card_congr e.toEquiv, card_psl34 hF, mul_comm]

end Top43

end CFSG.Quasithin.H13.L32A.C

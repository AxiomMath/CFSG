module

public import CFSG.Quasithin.H13.L32AC43d
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.L32AC43c

public section

namespace CFSG.Quasithin.H13.L32A.C

open CFSG.Open hiding StatedSL StatedSU StatedSp StatedProj StatedClassicalModel
open CFSG.Blueprint CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin
open CFSG.Assembly.LowTwoRank
open scoped IsMulCommutative

variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G] {T L V H : Subgroup G}

namespace Top43

variable {W K : Subgroup G} (C : Top43 T L V H W K) [IsMulCommutative ↥(conjClosure V H)]
include C

theorem nonempty_quotCenter_autK_F4 (h1222 : Stmt12_2_2_F4) (h1332 : Stmt13_3_2_F4)
    (h1334 : A6.Stmt13_3_4_F4) :
    Nonempty ((cStar K ⧸ Subgroup.center (cStar K)) ≃*
      (↥C.autK ⧸ Subgroup.center ↥C.autK)) := by
  refine quotCenter_mulEquiv_of_central_ker C.autKSurj C.autKSurj_surjective ?_ ?_
  · rcases CFSG.LieType.CurtisTits.le_center_or_eq_top_of_isQuasisimple C.hq C.autKSurj.ker
      with h | h
    · exact h
    · exfalso
      obtain ⟨x, hxK, -, hx1⟩ := C.exists_act_ne_one_F4 h1222 h1332 h1334
      apply hx1
      have h1 : C.autKSurj (QuotientGroup.mk ⟨x, hxK⟩) = 1 := by
        rw [← MonoidHom.mem_ker, h]
        exact Subgroup.mem_top _
      exact congrArg Subtype.val h1
  · have := C.hq.1.commutator_eq_top
    rwa [_root_.commutator_def] at this

theorem odd_card_center_autK_F4 (h1222 : Stmt12_2_2_F4) (h1332 : Stmt13_3_2_F4)
    (h1334 : A6.Stmt13_3_4_F4) : Odd (Nat.card (Subgroup.center ↥C.autK)) := by
  refine odd_card_center_of_pCore_eq_bot ?_
  have h := C.pCoreOf_autK_F4 h1222 h1332 h1334
  rw [pCoreOf, Subgroup.map_eq_bot_iff_of_injective _ C.autK.subtype_injective] at h
  rw [A3.pCore_eq_openCore]
  exact h

theorem card_autK_of_isPSU_F4 (h1222 : Stmt12_2_2_F4) (h1332 : Stmt13_3_2_F4) (h1334 : A6.Stmt13_3_4_F4)
    (hU : IsPSU 3 2 3 (cStar K ⧸ Subgroup.center (cStar K))) :
    ∃ z : ℕ, Odd z ∧ Nat.card ↥C.autK = z * 5515776 := by
  obtain ⟨-, F, _, _, hF, ⟨e⟩⟩ := hU
  obtain ⟨φ⟩ := C.nonempty_quotCenter_autK_F4 h1222 h1332 h1334
  refine ⟨Nat.card (Subgroup.center ↥C.autK), C.odd_card_center_autK_F4 h1222 h1332 h1334, ?_⟩
  rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (Subgroup.center ↥C.autK),
    ← Nat.card_congr φ.toEquiv, Nat.card_congr e.toEquiv, card_psu3_eight hF, mul_comm]

end Top43

end CFSG.Quasithin.H13.L32A.C

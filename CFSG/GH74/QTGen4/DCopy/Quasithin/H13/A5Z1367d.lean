module

public import CFSG.Quasithin.H13.A5Z1367d
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.A5X1367d

public section

namespace CFSG.Quasithin.H13.A5

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.A5Model
open scoped IsMulCommutative commutatorElement

namespace Setting

variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G] {T L V : Subgroup G} (S : Setting G T L V)

theorem autOn_LvQ_le_TvS_F4 (h1222 : Stmt12_2_2_F4)
    (h517 : Stmt5_1_7_one_F4) : autOn S.LvQ S.Uv ≤ autOn S.Tv S.Uv := by
  have hsyl := S.isSylowTwoOf_TvS_F4 h1222 h517
  have hQU : S.LvQ ≤ Subgroup.normalizer (S.Uv : Set G) :=
    (S.LvQ_le_Lv.trans S.Lv_le_Gv).trans S.Gv_le_normalizer_Uv
  have hQ2 : IsPGroup 2 (autOn S.LvQ S.Uv) := by
    have := S.isPGroup_LvQ
    have h1 : IsPGroup 2 ↥(S.LvQ.subgroupOf (Subgroup.normalizer (S.Uv : Set G))) :=
      this.of_equiv (Subgroup.subgroupOfEquivOfLe hQU).symm
    exact h1.map _
  exact le_of_isPGroup_of_le_normalizer hsyl hQ2
    (S.autOn_le_GvS (S.LvQ_le_Lv.trans S.Lv_le_Gv))
    (autOn_le_normalizer_autOn S.Tv_le_normalizer_LvQ)

theorem card_LvS_le_F4 (h1222 : Stmt12_2_2_F4) (h517 : Stmt5_1_7_one_F4) :
    Nat.card ↥(autOn S.Lv S.Uv) ≤ 3 * Nat.card ↥(autOn S.Lv S.Uv ⊓ autOn S.Tv S.Uv) := by
  have hLU : S.Lv ≤ Subgroup.normalizer (S.Uv : Set G) := S.Lv_le_Gv.trans S.Gv_le_normalizer_Uv
  set φ := InternalSec.autOnHom hLU with hφ
  have hsφ : Function.Surjective φ := InternalSec.autOnHom_surjective hLU
  set Q : Subgroup ↥S.Lv := S.LvQ.subgroupOf S.Lv with hQ
  have hidx : (Q.map φ).index ≤ 3 :=
    (Nat.le_of_dvd (Nat.pos_of_ne_zero Subgroup.FiniteIndex.index_ne_zero)
      (Subgroup.index_map_dvd Q hsφ)).trans S.relIndex_LvQ_le

  have hQS : ((Q.map φ).map (autOn S.Lv S.Uv).subtype) ≤ autOn S.Lv S.Uv ⊓ autOn S.Tv S.Uv := by
    rintro _ ⟨_, ⟨x, hx, rfl⟩, rfl⟩
    refine ⟨(φ x).2, S.autOn_LvQ_le_TvS_F4 h1222 h517 ?_⟩
    refine Setup.mem_autOn_iff.2 ⟨⟨x, hLU x.2⟩, Subgroup.mem_subgroupOf.mp hx, ?_⟩
    rfl
  have h1 := Subgroup.card_mul_index (Q.map φ)
  have h2 : Nat.card ↥(Q.map φ) ≤ Nat.card ↥(autOn S.Lv S.Uv ⊓ autOn S.Tv S.Uv) := by
    have e := Nat.card_congr ((Q.map φ).equivMapOfInjective _
      (autOn S.Lv S.Uv).subtype_injective).toEquiv
    rw [e]
    exact Subgroup.card_le_of_le hQS
  calc Nat.card ↥(autOn S.Lv S.Uv) = Nat.card ↥(Q.map φ) * (Q.map φ).index := h1.symm
    _ ≤ Nat.card ↥(autOn S.Lv S.Uv ⊓ autOn S.Tv S.Uv) * 3 := Nat.mul_le_mul h2 hidx
    _ = 3 * Nat.card ↥(autOn S.Lv S.Uv ⊓ autOn S.Tv S.Uv) := mul_comm _ _

end Setting

end CFSG.Quasithin.H13.A5

module

public import CFSG.Quasithin.H13.A6S1372L76M
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.A6S1372L76H

public section

namespace CFSG.Quasithin.H13.A6

open Equiv CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin CFSG.LieType.BorelTits
open CFSG.QuasithinUnique.Bridge
open scoped Pointwise IsMulCommutative

namespace Setting4

variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G] {T L V : Subgroup G} (S : Setting4 G T L V)
include S

theorem exists_ctx_F4 (h37 : A37ForSQTK) (h38 : A38ForSQTK)
    (h13315 : Stmt13_3_15_F4) (h1356two : Input1356Two_F4) (hNS : ¬ LieModel G .PSp 3 2 1)
    {H : Subgroup G} (hH : H ∈ S.Hz) (hab : IsElemAbelian 2 (conjClosure S.V3 H))
    [IsMulCommutative ↥(conjClosure S.V3 H)] {K : Subgroup G} (hK : K ∈ cComp H)
    (hL1K : S.L1 ≤ K) {D : FFModel} [IsSimpleGroup D.Gam] (hD : ¬ Group.IsSolvable D.Gam)
    (hR : D.Realizes (autSec (autOn K (conjClosure S.V3 H)) ⊤
        ((fsuV1 T V).subgroupOf (conjClosure S.V3 H)))
      (commV (autSec (autOn K (conjClosure S.V3 H)) ⊤
        ((fsuV1 T V).subgroupOf (conjClosure S.V3 H))))
      (fixV (autSec (autOn K (conjClosure S.V3 H)) ⊤
          ((fsuV1 T V).subgroupOf (conjClosure S.V3 H))) ⊓
        commV (autSec (autOn K (conjClosure S.V3 H)) ⊤
          ((fsuV1 T V).subgroupOf (conjClosure S.V3 H))))) :
    Nonempty (S.Ctx76_F4 H K D) := by
  obtain ⟨π, β, hR⟩ := (CFSG.Quasithin.H.Mathieu.realizes_iff _ _ _ _).1 hR
  have hKH : K ≤ H := le_of_mem_cComp hK
  have := S.nontrivial_tilde_of_L1_le hH hKH hL1K
  have hπ := A6L76L.injective_of_simple π hR.1
  have hrad := A6L76A.rad_eq_bot_of_surjective hD π hR.1
  have hHK := S.le_normalizer_of_L1_le hH h37 h38 hK hL1K hrad
  have hUK := S.commutator_UH_eq_of_L1_le hKH hHK hL1K
  exact ⟨⟨hNS, h13315, h1356two, hH, hab, hK, hL1K, hHK, hUK, π, β, hR, hπ⟩⟩

variable {S}

namespace Ctx76_F4
open CFSG.Quasithin.H13.A6.Setting4.Ctx76_F4

variable {H K : Subgroup G} [IsMulCommutative ↥(conjClosure S.V3 H)]

theorem false_nat_ge_five_F4 (h13314 : Stmt13_3_14_F4) {F : Type}
    [Field F] [Finite F] (hF : Nat.card F = 2) {n : ℕ} (hn : 5 ≤ n)
    (C : S.Ctx76_F4 H K (FFModel.nat (CFSG.Assembly.LowTwoRank.StatedSL n F))) : False := by
  obtain ⟨m, hxm⟩ := QuotientGroup.mk_surjective (C.βU_F4 ⟨S.v2, S.v2_mem_UH H⟩)
  set x : Fin n → F := Multiplicative.toAdd (show Multiplicative (Fin n → F) from m.1) with hx
  have hm1 : x ≠ 0 := by
    intro h
    apply C.βU_v2_ne_one_F4
    have : m = 1 := Subtype.ext
      (show (show Multiplicative (Fin n → F) from m.1) = 1 from toAdd_eq_zero.1 h)
    rw [← hxm, this, QuotientGroup.mk_one]
  obtain ⟨a, b, hE, ha, hb⟩ := A6L76M.exists_e9_fix hF hn x hm1
  have hfix : ∀ g : ↥(CFSG.Assembly.LowTwoRank.StatedSL n F),
      ((g : GL (Fin n) F) : Matrix (Fin n) (Fin n) F).mulVec x = x →
      (FFModel.nat (CFSG.Assembly.LowTwoRank.StatedSL n F)).act g m.1 * m.1⁻¹ ∈
        (FFModel.nat (CFSG.Assembly.LowTwoRank.StatedSL n F)).ker := by
    intro g hg
    show natAct _ g m.1 * (show Multiplicative (Fin n → F) from m.1)⁻¹ ∈
      (⊥ : Subgroup (Multiplicative (Fin n → F)))
    rw [Subgroup.mem_bot, mul_inv_eq_one]
    show Multiplicative.ofAdd (((g : GL (Fin n) F) : Matrix (Fin n) (Fin n) F).mulVec x) = m.1
    rw [hg]
    rfl
  exact C.not_e9_F4 h13314 m.2 hxm.symm hE (hfix a ha) (hfix b hb)

end Ctx76_F4

end Setting4

end CFSG.Quasithin.H13.A6

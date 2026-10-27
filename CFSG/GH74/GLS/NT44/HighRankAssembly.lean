module

public import CFSG.GH74.GLS.Stage1.Thm4.Defs
public import CFSG.GH74.GLS.C3.Layer1.Th2Defs
import CFSG.GH74.GLS.NT44.HighRankPair
import CFSG.GH74.GLS.Bg.Pu5.ZStructBasic
import CFSG.GroupTheory.OmegaOneE9
import CFSG.Foundations.HigherElementaryThompson

public section

set_option autoImplicit false

namespace CFSG.GH74.GLS.NT44

open CFSG.GH74.GLS.Stage1.Thm4

theorem high_rank_omega_balance_of_rigid_center_sylow
    {G : Type} [Group G] [Finite G] [IsSimpleGroup G]
    {fullQ : Type} [Group fullQ]
    {x : G} {W : Subgroup G}
    (hnonab : ∃ u v : G, u * v ≠ v * u)
    (hx2 : orderOf x = 2)
    (hmax : ∀ z : G, orderOf z = 2 →
      (RigidSet fullQ z).ncard ≤ (RigidSet fullQ x).ncard)
    (hW : CFSG.ABGLocalTools.IsSylowOf 2 W (zStar (Kz fullQ x)))
    (hhigh : 3 ≤ CFSG.pRank 2 W) :
    let A := (CFSG.omega₁ W (p := 2)).map W.subtype;
    A ≤ W ∧ CFSG.GH74.GLS.IsE 3 ⊤ A ∧
      CFSG.GH74.GLS.IsKBal 2 A ∧ CFSG.GH74.GLS.IsWeakKBal 1 A := by
  dsimp only
  let A := (CFSG.omega₁ W (p := 2)).map W.subtype
  have hfact2 : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hWle : W ≤ zStar (Kz fullQ x) := hW.le
  have hW2 : IsPGroup 2 W := hW.isPGroup
  have hcomm : IsMulCommutative W :=
    ⟨⟨fun u v => Subtype.ext (CFSG.GH74.GLS.Bg.Pu5.comm_of_mem_cSec
      (T := W) (K := Kz fullQ x) hW2 u.2 v.2
      (hWle u.2).1 (hWle v.2).2)⟩⟩
  have hΩelem : CFSG.IsElementaryAbelian 2 (CFSG.omega₁ W (p := 2)) :=
    @CFSG.IsElementaryAbelian.omega₁_of_isMulCommutative 2 hfact2 W _ hcomm
  have hAelem : CFSG.IsElementaryAbelian 2 A := by
    dsimp [A]
    exact @CFSG.IsElementaryAbelian.map_subtype 2 hfact2 G _ W (CFSG.omega₁ W (p := 2)) hΩelem
  have hAW : A ≤ W := by
    dsimp [A]
    exact Subgroup.map_subtype_le _
  have hcardΩ : Nat.card (CFSG.omega₁ W (p := 2)) = 2 ^ CFSG.pRank 2 W :=
    @CFSG.GroupTheory.card_omega₁_eq_pow_pRank_of_isMulCommutative W _ _ hcomm 2 hfact2
  have hcardA : Nat.card A = 2 ^ CFSG.pRank 2 W := by
    dsimp [A]
    rw [Subgroup.card_map_of_injective W.subtype_injective]
    exact hcardΩ
  have hrankA : CFSG.pRank 2 A = CFSG.pRank 2 W :=
    @CFSG.pRank_eq_of_card_eq_pow A _ _ 2 (CFSG.pRank 2 W) (by norm_num) hAelem hcardA
  have hhighA : 3 ≤ CFSG.pRank 2 A := by
    rw [hrankA]
    exact hhigh
  have hE : CFSG.GH74.GLS.IsE 3 ⊤ A := ⟨le_top, hAelem, hhighA⟩
  have hpair : CFSG.GH74.GLS.IsKBal 2 A ∧ CFSG.GH74.GLS.IsWeakKBal 1 A :=
    CFSG.GH74.GLS.NT44.isKBal_two_and_isWeakKBal_one_of_le_rigid_center_sylow
      (G := G) (fullQ := fullQ) (x := x) (W := W) (A := A)
      hnonab hx2 hmax hW hAelem hAW
  change A ≤ W ∧ CFSG.GH74.GLS.IsE 3 ⊤ A ∧
      CFSG.GH74.GLS.IsKBal 2 A ∧ CFSG.GH74.GLS.IsWeakKBal 1 A
  exact ⟨hAW, hE, hpair⟩

end CFSG.GH74.GLS.NT44

end

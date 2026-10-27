module

public import CFSG.LocalAnalysis.OddStandard.AltStdSmall4ChainHolds
public import CFSG.LocalAnalysis.OddStandard.AltStdSmall4TowerMain
public import CFSG.LocalAnalysis.OddStandard.AltHSInduction
public import CFSG.LocalAnalysis.OddStandard.AltStdSecTwoTen

public section

namespace CFSG.OddStandard.AltStdSmall4.CTOdd

open Subgroup
open scoped Pointwise

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {n : ℕ}

theorem orderTwoE_of_sylow (hS : StandardSetting G L) (θ : L ≃* alternatingGroup (Fin n))
    (hn : 8 ≤ n) (S : Sylow 2 (centralizer (L : Set G)))
    (hc : IsCyclic (S : Subgroup (centralizer (L : Set G)))) (h2 : Nat.card S = 2) :
    ∃ z, OrderTwoE G L (AltStdBal.sylowSub S) n θ z := by
  obtain ⟨z, d⟩ := AltStdCycTwo.cyc_of_sylow hS S hc
  exact ⟨z, hS, hn, d, (AltStdBal.card_sylowSub S).trans h2⟩

theorem notMem_sup_centralizer {Q : Subgroup G} {z u : G} (h : AltStdBal.Setting G L n)
    (d : AltStdBal.Cyc L Q z) (hu : u ∈ centralizer ({z} : Set G)) (hout : u ∉ L ⊔ Q) :
    u ∉ L ⊔ centralizer (L : Set G) := by
  intro hmem
  have hset := Subgroup.coe_mul_of_right_le_normalizer_left L (centralizer (L : Set G))
    (Subgroup.centralizer_le_normalizer (L : Set G))
  have hmem' : u ∈ (L : Set G) * (centralizer (L : Set G) : Set G) := by
    rw [← hset]
    exact hmem
  obtain ⟨l, hl, k, hk, rfl⟩ := Set.mem_mul.1 hmem'
  apply hout
  have hkz : k ∈ centralizer ({z} : Set G) := by
    have hk' : k = l⁻¹ * (l * k) := by group
    rw [hk']
    exact mul_mem (inv_mem (AltStdBal.le_centralizer_single h d hl)) hu
  have hkQ : k ∈ Q := by
    rw [← AltStdBal.cent_inf_eq h d]
    exact ⟨hk, hkz⟩
  exact mul_mem (mem_sup_left hl) (mem_sup_right hkQ)

theorem altStdBalancedOrder2InnerSmallAt_holds
    (G : Type) [Group G] [Finite G] :
    AltHSInduction.AltStdBalancedOrder2InnerSmallAt G := by
  intro L hS n hn8 hn11 ⟨θ⟩ S hc h2 _ hin
  obtain ⟨z, T⟩ := orderTwoE_of_sylow hS θ hn8 S hc h2
  exact cycTwoInnerSmallFalseE_of_tower Tower.wrFalse_holds Tower.slFalse_holds G L _ n θ z T
    hn11 (hin z (T.cyc.le T.cyc.mem) T.cyc.order)

theorem shapeTwoSmallNineAt_holds
    (G : Type) [Group G] [Finite G] :
    AltHSInduction.ShapeTwoSmallNineAt G := by
  intro L Q n z u h d T hn9
  obtain ⟨θ⟩ := h.iso
  exact cycTwoShapeTwoSmallFalse_of_tower Tower.wrFalse_holds Tower.slFalse_holds G L Q n θ z u
    ⟨h.std, h.hn, d, T.card⟩ hn9 T.cent (notMem_sup_centralizer h d T.cent T.outer) T.sq

theorem altStdBalancedOrder2InnerSmall_holds :
    AltStdSec.AltStdBalancedOrder2InnerSmall :=
  fun G _ _ => altStdBalancedOrder2InnerSmallAt_holds G

theorem shapeTwoSmallNine_holds :
    AltStdSec.ShapeTwoSmallNine :=
  fun G _ _ => shapeTwoSmallNineAt_holds G

end CFSG.OddStandard.AltStdSmall4.CTOdd

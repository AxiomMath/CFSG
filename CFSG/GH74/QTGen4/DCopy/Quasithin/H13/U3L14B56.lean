module

public import CFSG.Quasithin.H13.U3L14B56
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.U3L14Q

public section

namespace CFSG.Quasithin.H13.U3

open Subgroup CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.QuasithinUnique
open CFSG.Quasithin.InternalSec
open scoped IsMulCommutative commutatorElement

variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G]

namespace Set14

variable {T L V V₂ V₃ Lp : Subgroup G} (S : Set14 G T L V V₂ V₃ Lp)
include S

theorem b51Part1_KT_F4 (h1332 : Stmt13_3_2_F4) (hC58 : TheoremC58) (h317 : AS317Sylow) (h56 : AsB56)
    {K : Subgroup G} (hD : KData14 T L V V₂ Lp K) :
    ∃ _ : IsMulCommutative ↥(reducedAggregate (K ⊔ T)),
      B51Part1 (ffJ (autOn (K ⊔ T) (reducedAggregate (K ⊔ T))))
        (autOn K (reducedAggregate (K ⊔ T))) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set W := reducedAggregate (K ⊔ T) with hWdef
  have hred : IsTwoReducedIn (K ⊔ T) W := isTwoReducedIn_reducedAggregate (K ⊔ T)
  have hWe : IsElemAbelian 2 W := hred.2.2.1
  have hWc : IsMulCommutative ↥W := hWe.1
  refine ⟨hWc, ?_⟩
  have hTsyl : IsSylowTwoOf T (K ⊔ T) := S.syl le_sup_right
  have hYK : K ⊔ T ≤ normalizer (K : Set G) := sup_le le_normalizer hD.T_K
  have hKW : K ≤ normalizer (W : Set G) := le_sup_left.trans hred.2.1
  have hKq : CFSG.IsQuasisimple (↥K ⧸ CFSG.pCore 2 ↥K) :=
    CFSG.LocalCores.isQuasisimple_of_mulEquiv
      (QuotientGroup.quotientMulEquivOfEq (A3.pCore_eq_openCore 2 ↥K)).symm
      (A3.isQuasisimple_iff_open.2 hD.quasi)
  have hnt : ¬ K ≤ centralizer (W : Set G) := (S.reduced_K_F4 h1332 hD.faithful hD.quasi).1

  have hO2Y : pCoreOf 2 (autOn (K ⊔ T) W) = ⊥ := Setup.pCoreOf_autOn_eq_bot hred
  have hO2K : pCoreOf 2 (autOn K W) = ⊥ := by
    have hn : ((autOn K W).subgroupOf (autOn (K ⊔ T) W)).Normal := by
      refine ⟨fun k hk x => ?_⟩
      rw [mem_subgroupOf] at hk ⊢
      exact autOn_normal_of hYK _ x.2 _ hk
    have := CFSG.RankThreeEvenClassification.Helpers.pCoreOf_le_pCoreOf_of_normal 2 _ _
      (autOn_le_autOn_of_le le_sup_left) hn
    rw [hO2Y] at this
    exact le_bot_iff.1 this
  have hq : CFSG.IsQuasisimple ↥(autOn K W) := isQuasisimple_autOn hKW hKq hO2K hnt
  have hJ : K = ⁅K, thompsonJ T⁆ := (S.K_eq_comm_J_F4 h1332 hC58 h317 hD).symm
  have hSY : SQTKGroup ↥(K ⊔ T) :=
    sqtkGroup_of_pCoreOf_ne_bot S.h13.qtke S.h13.simple S.h13.nonabelian hD.faithful.1.2.2.2
  obtain ⟨A₀, -, hA, hKA⟩ := exists_offender_of hTsyl le_sup_left hYK hred hq hnt hJ
  obtain ⟨hKJ, hn, hQ, -, hcases⟩ := b56Cases_ffJ_autOn h56 (fun w hw => hWe.2 w hw) hred.2.1
    le_sup_left hYK hSY hO2Y hA hKA
  have h2 : ∀ g ∈ ffJ (autOn (K ⊔ T) W), ∃ m : ℕ, g ^ 2 ^ m ∈ autOn K W := fun g hg =>
    pow_two_mem_autOn_sup hD.T_K S.isP_T hred.2.1 g (B6.ffJ_le _ hg)
  obtain ⟨h1, hF⟩ := b56Case1_of_pow_two hKJ hn hq hQ h2 hcases
  have hB51 := h1.2.1
  rw [hF] at hB51
  exact hB51.1

end Set14

end CFSG.Quasithin.H13.U3

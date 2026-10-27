module

public import CFSG.LocalAnalysis.AGL81TheoremCD.Section14.S14Facts
public import CFSG.LocalAnalysis.AGL81TheoremCD.Section15.OraclesGen
import CFSG.LocalAnalysis.AGL81TheoremCD.Section14.L34ConfigAut
import CFSG.LocalAnalysis.AGL81TheoremCD.Section14.L34ConfigNorm
import CFSG.LocalAnalysis.AGL81TheoremCD.Section14.L34ConfigQuot
import CFSG.LocalAnalysis.AGL81TheoremCD.Section14.L34ConfigSolvable

public section

namespace CFSG.LocalAnalysis.AGL81TheoremCD.Section15

open CFSG.Open Subgroup
open CFSG.LocalAnalysis.AGL81TheoremCD.Section14
open CFSG.LocalAnalysis.RankThreeUC.AGL81C

variable {G : Type} [Group G] [Finite G]

theorem exists_l34Config
    {M E H : Subgroup G} (hC : CStarGen G)
    (hM : CFSG.Open.rankThreeIsMaxTwoLocal M) (hσ : (sigmaSet G M).Nonempty)
    (hF : Section14.S14FactsAt M) (hEM : E ≤ M)
    (hE : CFSG.Open.IsElemAbelian 3 E) (hEc : Nat.card E = 9)
    (hΓ : CFSG.Open.rankThreeGamma 1 3 E ≤ M) (hH : CFSG.Open.rankThreeIsMaxTwoLocal H)
    (hEH : E ≤ H) (hHM : H ≠ M) :
    ∃ A T R H' : Subgroup G, CFSG.LocalAnalysis.RankThreeUC.S15.L34Config M A T R H' := by
  classical
  have h : HypCGen G M 3 E H :=
    hypCGen_of_isMaxTwoLocal hC hM hσ hEM hE hEc hΓ hH hEH hHM
  obtain ⟨A, H', h', hAK', hmax', hC3', hNA⟩ := hF.exists_l34Data h
  obtain ⟨W, T, hW, hT, hWT⟩ := h'.exists_sylowTwo_normalizer_inf_kSub_le hNA
  let R : Subgroup G := CFSG.Open.pCoreOf 2 (A ⊔ T)
  have hA : CFSG.ABGLocalTools.IsSylowOf 3 A (kSub 3 M H') :=
    h'.isSylowOf_three_E hC3' hAK'
  have htwo := hF.twoAt 3 A H' h' hAK' hmax' T hT
  have hNR : Subgroup.normalizer (R : Set G) ≤ H' :=
    h'.normalizer_pCoreOf_sup_le hC3' hF.two hF.normal hF.layer hF.kSubLe hAK' hmax' hT
  have hsolv :=
    h'.isSolvable_inf_normalizer_pCoreOf hC3' hF.two hF.normal hF.layer hAK' hNA hT
  have hquot := h'.l34Config_quotient hC3' hF.two hF.normal hF.layer hAK' hNA hW hT hWT
  have hquat := h'.l34Config_quaternion hC3' hA hW hWT
  have htrans := h'.l34Config_transitive hC3' hA hW hWT
  refine ⟨A, T, R, H', ?_⟩
  refine
    { le_M := h'.E_le_M
      elemAbelian := h'.elem
      card_eq := ?_
      gamma := h'.gamma
      sylow := htwo.1
      not_sylow := htwo.2
      perm := h'.coe_mul_comm_of_isSylowOf hC3' hF.two hF.normal hF.layer hAK' hNA hT
      core := rfl
      normalizer_le := hNR
      maximal := h'.isMaxInvariantTwo_pCoreOf hC3' hF.two hF.normal hF.layer hAK' hNA hT hNR
      maxLocal := h'.isMaxTwoLocal_of_mem_H2StarFam h'.mem
      le_H := hAK'.trans (kSub_le 3 M H')
      not_le_M := h'.not_le
      solvable := hsolv
      quotient := hquot
      quaternion := hquat
      transitive := htrans }
  rw [h'.card]
  norm_num

theorem o1521At_of_s14
    {M : Subgroup G} (hC : CStarGen G) (hM : CFSG.Open.rankThreeIsMaxTwoLocal M)
    (hσ : (sigmaSet G M).Nonempty) (hF : Section14.S14FactsAt M) : O1521At G M := by
  intro _h3 E hEM hE hEc hΓ H hH2 hEH hHM
  exact exists_l34Config hC hM hσ hF hEM hE hEc hΓ hH2 hEH hHM

theorem o1521Gen_of_s14
    (hF : Section14.S14FactsGen) : O1521Gen :=
  fun G _ _ hC M hM hσ _hemb => o1521At_of_s14 hC hM hσ (hF G hC M hM hσ)

end CFSG.LocalAnalysis.AGL81TheoremCD.Section15

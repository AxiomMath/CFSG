module

public import CFSG.Quasithin.Vol2.Ch6Sec1Lem5ResLie
public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch5Statements
public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch6Sec1Lem5Res
public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch5Sec1Basic

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Assembly.LowTwoRank CFSG.QuasithinUnique CFSG.Quasithin

open Res615Lie

theorem res615Blocks_of_F4 (h331 : Stmt3_3_1_F4) (h5172 : Stmt5_1_7_two_F4)
    (he23 : E2.E23Statement) (he22 : E2.E22StatementNoN) : Res615Blocks_F4 := by
  intro G _ _ T M L V H n hyp hH hZ hU I _ hJ htype K hK
  by_contra hne
  have hT : IsSylowTwoOf T H := hyp.toHyp5_0_1.isSylowTwoOf hH.1.1
  have hMP : MinParabolic H T (H ⊓ M) := (hyp.toHyp5_0_1.minParabolic_of_isHStar_F4 h331 hH).1
  have hch : CharTwo H := charTwo_of_inH' hyp.qtke hyp.sylow hH.1
  have hsq : SQTKGroup ↥H := by
    obtain ⟨hk, hq⟩ := isSQTKSub_of_inH hyp.qtke hyp.simple hyp.nonabelian hH.1
    exact ⟨hq, hk⟩
  obtain ⟨-, -, hred⟩ := conjClosure_isTwoReducedIn_of_charTwo hT hch le_rfl
  have hHU : ¬ H ≤ Subgroup.centralizer
      (conjClosure (quasithinOmegaOneCenter T) H : Set G) := by
    intro hle
    exact hZ (hle.trans
      (Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr (le_conjClosure _ H))))

  have hJT : ¬ thompsonJ T ≤ Subgroup.centralizer
      (conjClosure (quasithinOmegaOneCenter T) H : Set G) := by
    have hZH : ⁅quasithinOmegaOneCenter T, H⁆ ≠ ⊥ := by
      intro hb
      apply hZ
      rw [Subgroup.commutator_comm, Subgroup.commutator_eq_bot_iff_le_centralizer] at hb
      exact hb
    obtain ⟨-, hKeq, -⟩ := h5172 G T M L V H n hyp.toHyp5_0_1 hyp.module hH hZH
    have hJT : thompsonJ T ≤ T := thompsonJ_le_self T
    have hTJ : T ≤ Subgroup.normalizer (thompsonJ T : Set G) :=
      Subgroup.le_normalizer.trans (normalizer_le_normalizer_thompsonJ T)
    intro hJC
    have hJO : thompsonJ T ≤ pCoreOf 2 H := by
      rw [← hMP.inf_centralizer_eq_pCoreOf hred hHU]
      exact le_inf hJT hJC
    have hii := hMP.commutator_lt_iff_le_pCoreOf hJT hTJ
    rw [twoResidual_eq_oTwoUpper'] at hii
    have hlt := hii.mpr hJO
    rw [← hKeq] at hlt
    exact lt_irrefl _ hlt
  obtain ⟨-, I₀, hcard₀, hJ₀, hcomm₀, -, -, htype₀, -⟩ :=
    he23 G H T (H ⊓ M) _ hU hMP hsq hch hred hJT
  have h36 : Nat.card ↥(autI hU (thompsonJ H)) ≤ 36 :=
    card_le_thirtySix hJ₀ hcard₀ hcomm₀ fun L₀ hL₀ => E2.card_of_isL2Natural_one
      (isL2Natural_one_of_mem he22 hMP hsq hred hHU hU (hyp.noLie H hH) hJ₀ hcomm₀ htype₀ hL₀)
  have h60 := E2.sixty_le_card_of_block (htype K hK) hne
  have hKJ : K ≤ autI hU (thompsonJ H) := hJ ▸ le_iSup₂_of_le K hK le_rfl
  have hle := Subgroup.card_le_of_le hKJ
  omega

end CFSG.Quasithin.H13

module

public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.CPrimeModelLink
public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.Stage0Reduce

public section

namespace CFSG.EvenSmallLie.OmegaEight.CPrimeModel

open Subgroup Matrix CFSG.EvenSmallLie.UnitarySix.YamadaPar
open CFSG.EvenSmallLie.OmegaEight.Stage1 CFSG.EvenSmallLie.OmegaEight.Stage1.Model
open CFSG.EvenSmallLie.OmegaEight.Stage0
open CFSG.EvenSmallLie.OmegaEight.CPrime (reflRows)

theorem cData7 : CData7 := by
  intro G _ _ L t c hH hK hC
  obtain ⟨e⟩ := OmegaEight.nonempty_mulEquiv_omegaT hH.2.2
  obtain ⟨θ, m, hm, hsq, hact⟩ := exists_rechoice_plus hK
    ((OmegaEight.mulEquivQuotientCenter hH.2.1).symm.trans (e.trans OmegaEight.omegaRestrictEquiv))
    hC.cprime.c_mem_centralizer hC.c_not_mem (by rw [hC.cprime.sq]; exact mem_zpowers t)
  have hcmL : c * m ∈ normalizer (L : Set G) := mul_mem hC.c_mem_normalizer (le_normalizer hm)
  obtain ⟨hcact, hcU⟩ := link_act (ε := .plus) θ hcmL hact
  have hF := (Model.modelLinkFacts .plus).transport θ
  have hA := (Model.autCent .plus).transport (Model.modelLinkFacts .plus).Q_le_L θ
  exact ⟨m, hm, _, _, _, _, _, _, n0 .plus,
    hF.radicalData (OmegaEight.involutionsInOddPart_of_center_eq_bot hH.2.1 hH.2.2),
    hF.U_max, hA, hsq, hcU, n0_lt .plus, qfB_n0 .plus, hcact⟩

theorem dData7 : DData7 := by
  intro G _ _ L t c r hH hK hD
  obtain ⟨e⟩ := OmegaEight.nonempty_mulEquiv_omegaT hH.2.2
  obtain ⟨θ, m, hm, hsq, hact⟩ := exists_rechoice_plus hK
    ((OmegaEight.mulEquivQuotientCenter hH.2.1).symm.trans (e.trans OmegaEight.omegaRestrictEquiv))
    hD.cprime.c_mem_centralizer hD.c_not_mem (by rw [hD.cprime.sq]; exact mem_zpowers t)
  have hcL : c ∈ normalizer (L : Set G) := hK.le_normalizer hD.cprime.c_mem_centralizer
  have hcmL : c * m ∈ normalizer (L : Set G) := mul_mem hcL (le_normalizer hm)
  obtain ⟨hcact, hcU⟩ := link_act (ε := .plus) θ hcmL hact
  have hF := (Model.modelLinkFacts .plus).transport θ
  have hA := (Model.autCent .plus).transport (Model.modelLinkFacts .plus).Q_le_L θ
  have hNQ : ∀ n ∈ L ⊔ zpowers r, n ∈ normalizer (pull θ (QMm .plus) : Set G) → n ∈ L := by
    intro n hn hnQ
    have h2 := sq_mem_of_normalizer_plus hK θ (hD.le_centralizer hn) hnQ
    refine hD.odd n hn ?_
    obtain ⟨l, hl, h | h⟩ := hK.mem_sup_iff.1 h2
    · rw [h]
      exact hl
    · exfalso
      apply hD.t_not_mem
      have e : t = l⁻¹ * (n * n) := by rw [h]; group
      rw [e]
      exact mul_mem (mem_sup_left (inv_mem hl)) (mul_mem hn hn)
  exact ⟨m, hm, _, _, _, _, _, _, n0 .plus,
    hF.radicalData (OmegaEight.involutionsInOddPart_of_center_eq_bot hH.2.1 hH.2.2),
    hF.U_max, hA, hNQ, hsq, hcU, n0_lt .plus, qfB_n0 .plus, hcact⟩

theorem cData9 : CData9 := by
  intro G _ _ L t c hH hK hC
  obtain ⟨θ⟩ := OmegaEightMinus.nonempty_mulEquiv_omegaT hH.2.2
  obtain ⟨m, hm, hsq, hact⟩ :=
    exists_rechoice_minus hK θ hC.cprime.c_mem_centralizer hC.c_not_mem
  have hcmL : c * m ∈ normalizer (L : Set G) := mul_mem hC.c_mem_normalizer (le_normalizer hm)
  obtain ⟨hcact, hcU⟩ := link_act (ε := .minus) θ hcmL hact
  have hF := (Model.modelLinkFacts .minus).transport θ
  have hA := (Model.autCent .minus).transport (Model.modelLinkFacts .minus).Q_le_L θ
  exact ⟨m, hm, _, _, _, _, _, _, n0 .minus,
    hF.radicalData (OmegaEightMinus.involutionsInOddPart_of_lieModel_minus hH.2.2),
    hF.U_max, hA, hsq, hcU, n0_lt .minus, qfB_n0 .minus, hcact⟩

theorem endgameC'7 : EndgameC'7 :=
  endgameC'7_of cData7

theorem endgameD'7 : EndgameD'7 :=
  endgameD'7_of dData7

theorem endgameC'9 : EndgameC'9 :=
  endgameC'9_of cData9

end CFSG.EvenSmallLie.OmegaEight.CPrimeModel

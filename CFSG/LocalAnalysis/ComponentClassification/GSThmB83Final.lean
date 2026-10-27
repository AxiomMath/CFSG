module

public import CFSG.LocalAnalysis.ComponentClassification.GSThmB83S2Final
public import CFSG.LocalAnalysis.ComponentClassification.GSThmB83Q3Final
public import CFSG.LocalAnalysis.ComponentClassification.GSThmB5bLemma56
public import CFSG.LocalAnalysis.ComponentClassification.GSThmB5bLemma517

public section

namespace CFSG.ComponentClassification.GSThmB

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer
  CFSG.ComponentClassification.UnbalancedCorr

theorem Hyp52.table517_of_sec8Case {X : Type} [Group X] [Finite X] (h : Hyp52 X)
    (hc : h.Sec8Case) : h.Table517 := by
  rcases hc with ⟨hJ, hKa, hK⟩ | ⟨p, f, hp, hp2, hf, hJ, hKa, hK⟩
  · exact Or.inr (Or.inr (Or.inl ⟨hJ, hKa, hK⟩))
  · exact Or.inr (Or.inr (Or.inr ⟨p, f, hp, hp2, hf, hJ, hKa, hK⟩))

theorem lemma83 (hTB : GSLit.ThompsonBurgoyneInput)
    (hSA : SolAltLit.SolomonAlternatingOddInput) (hB1 : ConjFixStatement)
    (hB6 : SylowKernelStatement) (hCF23 : CFProp23Fusion) (hCF24 : CFProp24c)
    (hCFc : CFProp23Center) (hCFi : CFProp23IndexReduced) (hF : Cat8.Q3Facts)
    (hS2 : Cat8.S2Facts) (h12 : GS83Step12Input) : Lemma83Statement := by
  intro X _ _ h hset hP
  have H : Hyp52.L83Hyp h :=
    { setting := hset
      card_P := hP
      T_eq := (h.normalizer_P_eq hCFi (h.table517_of_sec8Case hset.2.2.2.2.2.2.2.2.2.2)).1
      C_eq := h.centralizer_P_eq hB1 hCF23 hCFc
      J_normal := (normal_subgroupOf_iff_le_normalizer h.J_le).mpr
        (h.centralizer_le_normalizer_J hB1 hB6 hCF23 hCF24 hCFc)
      S_sylow_C := (h.S_sylow_centralizer hB1 hB6 hCF23 hCF24 hCFc).2
      B_sylow_kernel := hB6 X h }
  exact H.false_of_q3 (H.isQ3 hTB hSA hF.simple hF.inner hS2) hF h12

end CFSG.ComponentClassification.GSThmB

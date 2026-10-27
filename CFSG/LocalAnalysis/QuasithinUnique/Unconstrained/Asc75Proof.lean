module

public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.Asc75
public import CFSG.LocalAnalysis.Asc75.Induct

public section

namespace CFSG.QuasithinUnique

theorem asc75Lemma34Disjoint_of_endgame (hE : CFSG.Asc75.Asc75Endgame) : Asc75Lemma34Disjoint := by
  intro G _ _ S A₁ A₂ H hdisj hS hA₁ hA₂ hcomm hr₁ hr₂ hH hsub hclosedH hc₁ hc₂
  left
  have hindex : (S.subgroupOf ⊤).index = S.index := Subgroup.relIndex_top_right S
  have hHyp : CFSG.Asc75.Hyp S A₁ A₂ H :=
    { pgroup := hS.2.1
      odd_index := by
        have := hS.2.2
        rwa [hindex] at this
      le₁ := hA₁
      le₂ := hA₂
      comm := hcomm
      rank₁ := hr₁
      rank₂ := hr₂
      hdef := hH
      closed_H := hclosedH
      closed₁ := hc₁
      closed₂ := hc₂ }
  exact CFSG.Asc75.disjointLemma_of_endgame hE G S A₁ A₂ H hHyp hdisj

end CFSG.QuasithinUnique

module

public import CFSG.LocalAnalysis.ComponentClassification.GMS78Sec5RuLeaf
public import CFSG.LocalAnalysis.ComponentClassification.GMS78Sec5RuCz
public import CFSG.LocalAnalysis.ComponentClassification.GMS78Sec5RuCzRigid
public import CFSG.LocalAnalysis.ComponentClassification.GMS78Sec5RuCzRigidRels
public import CFSG.LocalAnalysis.ComponentClassification.GMS78Sec5RuCzMatch
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoFoundationFinal
public import CFSG.Sporadic.Schreier.RuB1Native

public section

namespace CFSG.ComponentClassification.GMS78

open Subgroup CFSG.ComponentClassification.GMS78.RuAsm CFSG.ComponentClassification.GMS78.RuCz

theorem ruH1Stmt :
    RuH1Stmt := by
  intro G _ _ A₁ Q X R f hQC _ ⟨σ, hσ, hker⟩ hQ hR _ _ _ hXu hXQ f₂ hz₂ hA₂
  exact H1.exists_normCz
    ⟨ruM12_le_centralizer_ruZ0, czZ0_eq, czJ_rels, czJ_conjQ, czJ_conjV, czJ_conjW, card_czJ0⟩
    (fun _ _ y hr hc _ _ _ hq hw hn hgq h3 => czRigid y hr hc hq hw hn hgq h3)
    (fun _ _ y hr hc _ _ hs hh => czNorm y hr hc hs hh)
    (fun _ _ y hr hc _ _ hs4 hs8 hh => czClass2 y hr hc hs4 hs8 hh)
    (fun _ _ y hr hc hq hv hw hh _ hr' he => czSignCentral y hr hc hq hv hw hh hr' he)
    hQC σ hσ hker hQ f₂ hz₂ hA₂ (map_czJ0_eq f₂ hz₂ hA₂ hR hQ σ hker hXQ hXu)

theorem dempwolffRuMin :
    DempwolffRuMin :=
  dempwolffRuMin_of_open
    ⟨RankTwoFoundation.lemma32, RankTwoFoundation.lemma33One, RankTwoFoundation.lemma33Two,
      RankTwoFoundation.lemma33Three, RankTwoFoundation.asc75Theorem4⟩
    CFSG.Sporadic.RuSchreier.ruB1NativeFacts ruH1Stmt

end CFSG.ComponentClassification.GMS78

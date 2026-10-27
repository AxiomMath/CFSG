module

public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallGEVCoreAltSix
public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallFiKCFi22
public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallKCIn
public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallSmallP
import CFSG.LocalAnalysis.AGLEmbedding.OneSmallGEVCore
import CFSG.LocalAnalysis.AGLEmbedding.OneSmallGEVCoreKC
import CFSG.LocalAnalysis.AGLEmbedding.OneSmallGEVCoreL34
import CFSG.LocalAnalysis.AGLEmbedding.OneSmallGEVCoverFree
public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallGEVDefs
public import CFSG.LocalAnalysis.AGLEmbedding.UnitaryFacts

public section

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.PreuniquenessRankFour.Helpers
open CFSG.RankThreeCoreUniqueness.Helpers

theorem d1SmallGEVNormalThreeS_of (hUP : KFactUPrimeSmall) (hUE : KFactUPrimeExc)
    (hSch : KFactCatalogSchreier) (hΓ3 : KFactSmallGammaSolvableThree)
    (hOut : KFactSmallOutPPrime) (hExp : KFactSmallSylowExp) (hOrb : KFactSmallOrbits)
    (hSh3 : KFactSmallSylowShapeThree) (hO : KFactSmallThreeOrders)
    (hInvK : KFactAltSixSylowInvert) (hK : CitedBlockToralThree) (h84 : Asc81bEightFour)
    (h85 : Asc81bEightFive) (h86 : Asc81bEightSix) (h93 : Asc81bNineThree) (hD2 : D1NoXBlock)
    (hU : D1SmallGEVNormalU33) (hL : D1SmallGEVNormalL34U2) : D1SmallGEVNormalThreeS := by
  intro G _ _ p P M H R Rbar K hd z hz hI hB0 hEv hIso hp3 hK3 hOR hcomm hnot hV hCz hcore hA
  rcases hK3 with hA6 | hU3 | hL34
  · exact D1OneSmallData.false_of_a6_ia hUP hSch hΓ3 hOut hExp hOrb hSh3 hO hInvK hK h84 h85 h86
      h93 hD2 hd hz hI hB0 hp3 hA6 hCz
  · exact hU G p P M H R Rbar K hd z hz hI hB0 hEv hIso hp3 hU3 hcomm hnot hV hCz hcore hA
  · by_cases hU2 : D1SmallU2Fails p M H K
    · exact hL G p P M H R Rbar K hd z hz hI hB0 hEv hIso hp3 hL34 hOR hU2 hcomm hnot hV hCz
        hcore hA
    · exact D1OneSmallData.false_of_l34_ia hUE hSch hΓ3 hOut hExp hOrb hSh3 hO hK h84 h85 h86 h93
        hD2 hd hz hI hB0 hp3 hL34 hOR hU2 hCz

theorem d1SmallGEVIbNormal_of_all (hOut : KFactSmallOutPPrime) (h : D1SmallGEVIbNormalAll) :
    D1SmallGEVIbNormal := by
  intro G _ _ p P M H R Rbar K hd z hz hnIa hB0 hEv hIso _ _ hL hgp hcomm hnot hH hV hsm hall
  exact h G p P M H R Rbar K hd z hz hnIa hB0 hEv hIso
    (fun hOR => hOR (hd.rbar_le_sup_centralizer hOut (d1SmallLa_of_not hL))) hgp hcomm hnot hH
    hV hsm hall

theorem d1SmallGEVIbNormalThree_of_all (hGst : StmtSmallGuest) (h : D1SmallGEVIbNormalAll) :
    D1SmallGEVIbNormalThree := by
  intro G _ _ p P M H R Rbar K hd z hz hnIa hB0 hEv hIso _ _ hOR hcomm hnot hH hV hsm hall
  exact h G p P M H R Rbar K hd z hz hnIa hB0 hEv hIso hOR
    (fun h' => hGst G p P M H R Rbar K hd (Or.inl h')) hcomm hnot hH hV hsm hall

theorem d1SmallGEVCore_of_all (hOut : KFactSmallOutPPrime) (hSch : KFactCatalogSchreier)
    (hK1 : KFactOneLie) (hU : KFactUnitarySylowStructure) (hβ : KFactBeta) (hα : KFactAlphaW)
    (h2 : D1CaseTwo) (h3 : D1CaseThree) (hGst : StmtSmallGuest) (hN : D1SmallGEVNormal)
    (hN3 : D1SmallGEVNormalThreeS) (hNF : D1SmallGEVNormalFi22)
    (hIbA : D1SmallGEVIbNormalAll) : D1SmallGEVCore :=
  d1SmallGEVCore_of_normal hSch hK1 hU hβ hα h2 h3 hGst hN hN3 hNF
    (d1SmallGEVIbNormal_of_all hOut hIbA) (d1SmallGEVIbNormalThree_of_all hGst hIbA)

theorem d1SmallGEVStarIb_of_core (hOut : KFactSmallOutPPrime) (hExp : KFactSmallSylowExp)
    (hC : D1SmallGEVCore) : D1SmallGEVStarIb := by
  intro G _ _ p P M H R Rbar K hd _ z hz _ hB0 hEv hIso _ _ hL _ _ hcomm hnot _
  obtain ⟨hR, -⟩ := hd.card_le_and_decomp_of_b0 hOut hExp hz hB0 (d1SmallLa_of_not hL)
  exact fun _ _ _ _ _ _ _ _ _ _ _ _ => hC G p P M H R Rbar K hd z hz hB0 hEv hIso hR hcomm hnot

theorem d1SmallIbEV_of_core (hOut : KFactSmallOutPPrime) (hExp : KFactSmallSylowExp)
    (hNo2 : KFactSmallNoTwo) (hShape : KFactSmallSylowShape) (hOrb : KFactSmallOrbits)
    (hC : D1SmallGEVCore) : D1SmallIbEV := by
  intro G _ _ p P M H R Rbar K hd _ z hz _ hB0 hEv hIso hA6 _ hL hFi _ _
  obtain ⟨hR, -⟩ := hd.card_le_and_decomp_of_b0 hOut hExp hz hB0 (d1SmallLa_of_not hL)
  exact hC G p P M H R Rbar K hd z hz hB0 hEv hIso hR
    (hd.twoCore_comm_mem_core hNo2 hz hB0 hIso hFi hR)
    (hd.not_twoCore_inf_le hOut hExp hShape hOrb hz hB0 hA6 hL hFi)

theorem d1SmallFi22EV_of_core (hOut : KFactSmallOutPPrime) (hExp : KFactSmallSylowExp)
    (hC : D1SmallGEVCore) : D1SmallFi22EV := by
  intro G _ _ p P M H R Rbar K hd _ z hz hp5 _ _ hB0 hEv hIso hcomm hnot
  obtain ⟨hR, -⟩ := hd.card_le_and_decomp_of_b0 hOut hExp hz hB0 (fun h => absurd h (by omega))
  exact hC G p P M H R Rbar K hd z hz hB0 hEv hIso hR hcomm hnot

theorem d1CaseOneEven_of_normalForms (hUP : KFactUPrimeSmall) (hUE : KFactUPrimeExc)
    (hSch : KFactCatalogSchreier) (hΓ3 : KFactSmallGammaSolvableThree)
    (hOut : KFactSmallOutPPrime) (hExp : KFactSmallSylowExp) (hNo2 : KFactSmallNoTwo)
    (hShape : KFactSmallSylowShape) (hOrb : KFactSmallOrbits) (hSh3 : KFactSmallSylowShapeThree)
    (hO : KFactSmallThreeOrders) (hInvK : KFactAltSixSylowInvert) (hTor3 : CitedBlockToralThree)
    (h84 : Asc81bEightFour) (h85 : Asc81bEightFive) (h86 : Asc81bEightSix)
    (h93 : Asc81bNineThree) (hD2 : D1NoXBlock) (hK1 : KFactOneLie)
    (hU : KFactUnitarySylowStructure) (hβ : KFactBeta) (hα : KFactAlphaW) (h2 : D1CaseTwo)
    (h3 : D1CaseThree) (hGst : StmtSmallGuest) (hRk : KFactSmallOfRankTwo)
    (hInvC : KFactSmallInvolveCard) (hKC3 : KFactCoverThreeFix) (hN : D1SmallGEVNormal)
    (hN3s : D1SmallGEVNormalU33) (hN3l : D1SmallGEVNormalL34Ph)
    (hNF : D1SmallGEVNormalFi22) (hIbA : D1SmallGEVIbNormalAll) :
    D1SmallGEVStarIb ∧ D1SmallGEVStarFree ∧ D1SmallIbEV ∧ D1SmallFi22EV ∧ D1SmallKCLeft ∧
      D1SmallEvenA6U33 ∧ D1SmallL34LeftIso := by
  have hN3 : D1SmallGEVNormalThreeS :=
    d1SmallGEVNormalThreeS_of hUP hUE hSch hΓ3 hOut hExp hOrb hSh3 hO hInvK hTor3 h84 h85 h86 h93
      hD2 hN3s (d1SmallGEVNormalL34U2_of_ph hUE hSch hΓ3 hOut hExp hOrb hSh3 hO hTor3 h84 h85 h86
        h93 hD2 hN3l)
  have hC : D1SmallGEVCore :=
    d1SmallGEVCore_of_all hOut hSch hK1 hU hβ hα h2 h3 hGst hN hN3 hNF hIbA
  exact ⟨d1SmallGEVStarIb_of_core hOut hExp hC,
    d1SmallGEVStarFree_of hOut hExp hSch hK1 hU h2 h3,
    d1SmallIbEV_of_core hOut hExp hNo2 hShape hOrb hC, d1SmallFi22EV_of_core hOut hExp hC,
    d1SmallKCLeft_of hKC3
      (d1SmallKCLeftOut_of_core hOut hExp hSch hRk hInvC hK1 hU hβ hα h2 h3 hC),
    d1SmallEvenA6U33_of_core hOut hExp hNo2 hShape hOrb hO hC,
    d1SmallL34LeftIso_of_core hOut hExp hNo2 hShape hOrb hC⟩

end CFSG.AGLEmbedding

module

public import CFSG.LocalAnalysis.SectionRank.QTK.CentreFact.Defs
public import CFSG.Assembly.RankThreeEvenDefs
import CFSG.LocalAnalysis.SectionRank.QTK.A134Pi
public import CFSG.Foundations.QuasisimpleMulEquiv
public import CFSG.LocalAnalysis.SectionRank.QTK.Section

public section

namespace CFSG.SectionRank.QTK.CentreFact

open Subgroup
open CFSG.Assembly.RankThreeEven (localRank)

theorem OddBound.of_mulEquiv {S T : Type} [Group S] [Group T] [Finite S] [Finite T] {r : ℕ}
    (hr : 1 < r) (e : S ≃* T) (h : OddBound r T) : OddBound r S :=
  fun R hR hR2 => pRank_normalizer_le_of_mulEquiv e hr h R hR hR2

theorem qtCentreFact_of_sub (h : QTCentreFactSub) : QTCentreFact := by
  intro K _ _ hq hK he r hr hr2 hrZ R hR hR2
  let e : (⊤ : Subgroup K) ≃* K := Subgroup.topEquiv
  have hZ : r ∣ Nat.card (center (⊤ : Subgroup K)) := by
    rwa [Nat.card_congr (Subgroup.centerCongr e).toEquiv]
  have hob := h K he ⊤ (hq.of_mulEquiv e) (hK.subgroup ⊤) r hr hr2 hZ
  exact OddBound.of_mulEquiv hr.one_lt
    (QuotientGroup.congr (center (⊤ : Subgroup K)) (center K) e (Subgroup.map_center_eq e)).symm
    hob R hR hR2

end CFSG.SectionRank.QTK.CentreFact

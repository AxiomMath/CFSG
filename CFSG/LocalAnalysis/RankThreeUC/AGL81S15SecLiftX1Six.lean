module

public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15Vocab
import CFSG.LocalAnalysis.RankThreeUC.AGL81S15SecLiftX1Equiv
import CFSG.LocalAnalysis.RankThreeUC.AGL81S15SecLiftX1Shape
import CFSG.LocalAnalysis.RankThreeUC.AGL81S15SecLiftX1Cover
import CFSG.LocalAnalysis.RankThreeUC.AGL81S15SecLiftX1Setting
import CFSG.LocalAnalysis.RankThreeUC.AGL81S15C118Sub
public import CFSG.Quasithin.Background.C1GNNotation

public section

namespace CFSG.LocalAnalysis.RankThreeUC.S15

open CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData

@[expose] def JOutSupGuard : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (T : Subgroup X), GNSetting X T →
    ∀ (L : Subgroup X) (Ls : Subgroup (X ⧸ gnC T)), CFSG.Open.IsComponentOf Ls ⊤ →
      LiftOf T L Ls → L.Normal → GN15.JOutCentralAt (T.subgroupOf (L ⊔ T))

@[expose] def GNSixAll : Prop :=
  (∀ (X : Type) [Group X] [Finite X] (T : Subgroup X), GNSetting X T → T ≠ ⊥ →
    ∀ T₁ T₂ : Subgroup X, CFSG.Quasithin.IsC118Pair T T₁ T₂ →
      IsGNPair T T₁ T₂ ∧ GNParabolic T T₁ T₂ ∧ GNThree T T₁ T₂ ∧ GNCentre T T₁ T₂ ∧
        GNAlt7 T T₁ T₂ ∧ GNAltBig T T₁ T₂) ∧ JOutSupGuard

variable {X : Type} [Group X] [Finite X]

theorem gnGood_sup_of_normal (hSix : GNSixAll) {T T₁ T₂ L : Subgroup X}
    {Ls : Subgroup (X ⧸ gnC T)} (hX : GNSetting X T) (hg : GNGood T T₁ T₂)
    (hcomp : GNYComponent T T₁ T₂ Ls) (hlift : LiftOf T L Ls) (hLn : L.Normal) :
    GNGood (T.subgroupOf (L ⊔ T)) (T₁.subgroupOf (L ⊔ T)) (T₂.subgroupOf (L ⊔ T)) := by
  have hgn₁ := gnSetting_sup_of_normal hX hLn
  have hc := CFSG.Quasithin.IsC118Pair.subgroupOf (le_sup_right : T ≤ L ⊔ T) hg.c118
  have hT : T.subgroupOf (L ⊔ T) ≠ ⊥ := fun h => hc.1 (le_bot_iff.mp
    ((hc.2.1.trans (CFSG.Quasithin.C1GN.omegaOneCenterOf_le_self _)).trans h.le))
  have hJ₁ : GN15.JOutCentralAt (T.subgroupOf (L ⊔ T)) :=
    hSix.2 X T hX L Ls hcomp.1 hlift hLn
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hSix.1 ↥(L ⊔ T) (T.subgroupOf (L ⊔ T)) hgn₁ hT _ _ hc
  exact
    { pair := h1
      parabolic := h2
      three := h3
      centre := h4
      alt7 := h5
      altBig := h6
      factor := hg.factorSub (L ⊔ T) le_sup_right hgn₁ hJ₁
      shape := gnShape_sup_of_normal hX hg hcomp hlift hLn
      c118 := hc
      factorSub := gnFactor_subgroupOf_subgroupOf hg le_sup_right
      cover := ⟨gnCoverP_sup_of_normal hX hcomp hlift hLn,
        gnCoverSec_sup_of_normal hX hg.pair.le_center hcomp hlift hLn⟩ }

end CFSG.LocalAnalysis.RankThreeUC.S15

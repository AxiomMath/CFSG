module

public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch5Sec2LocalLem522
public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch5Sec2LocalLem522NeS331

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin

@[expose] def Stmt5_2_2_ne_core_F4 : Prop :=
  ∀ (G : Type) [Group G] [CFSG.GH74.QTGen4.Finite4 G] (T M L V H B D L₂ Dp : Subgroup G) (n p : ℕ),
    Hyp5_2_2p G T M L V H B D L₂ Dp n p →
    pCoreOf 2 (Dp ⊔ (L₂ ⊔ sec52S M H)) ≠ ⊥ →
    pCoreOf 2 (Dp ⊔ (L₂ ⊔ sec52S M H) ⊔ (T ⊓ Subgroup.normalizer (L₂ : Set G)) ⊔ B) ≠ ⊥ →
    ¬ H ≤ Dp ⊔ (L₂ ⊔ sec52S M H) ⊔ (T ⊓ Subgroup.normalizer (L₂ : Set G)) ⊔ B →
    T ⊓ Subgroup.normalizer (L₂ : Set G) < T → L₂ < oTwoUpper H →
    ¬ Dp ≤ Subgroup.normalizer (L₂ : Set G) → False

theorem stmt5_2_2_ne_of_F4 (hF : L2TorusFact) (h510 : Stmt5_1_10_F4) (h331 : Stmt3_3_1_F4)
    (hR : L2RankOneSylowFact) (hL2 : Stmt5_2_L2_F4) (hLie : Stmt5_2_L2Lie_F4)
    (hcore : Stmt5_2_2_ne_core_F4) : Stmt5_2_2_ne_F4 := by
  intro G _ _ T M L V H B D L₂ Dp n p hyp hO
  obtain ⟨h1, h2, h3, h4⟩ := hyp.ne_facts_F4 hF h510 h331 hR hL2 hLie hO
  exact hcore G T M L V H B D L₂ Dp n p hyp hO h1 h2 h3 h4
    (hyp.Dp_not_le_normalizer_L2_F4 hF h510 h331 hR hL2)

end CFSG.Quasithin.H13

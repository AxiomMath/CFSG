module

public import CFSG.LocalAnalysis.AGLEmbedding.ReeF4MSideOdd

public section

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.PreuniquenessRankFour.Helpers
open CFSG.RankThreeCoreUniqueness.Helpers

@[expose] def StmtReeF4Components : Prop :=
  ∀ {G : Type} [Group G] [Finite G] {P : Sylow 5 G} {M H R X : Subgroup G},
    D1ReeF4Data P M H R X → (∀ q ∈ GLBBetaFour G, q < 5 → D1At G q) →
    CFSG.pCore 5 (↥M ⧸ CFSG.pCore 2 ↥M) = ⊥ →
    ∀ Lbar : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M), IsComponentOf Lbar ⊤ →
      barM M X ≤ Subgroup.centralizer (Lbar : Set _)

theorem stmtReeF4MSide_of (h84 : Asc81bEightFour) (hD2 : D1NoXBlock)
    (hC : StmtReeF4Components) : StmtReeF4MSide := by
  intro G _ _ P M H R X h hind hO
  have h5 : Nat.Prime 5 := by norm_num
  have hXM : X ≤ M := h.surv.le_R.trans h.surv.ph3.le_M
  have hXp : IsPGroup 5 X := fun x => ⟨1, Subtype.ext (by simpa using h.elem.2 x x.2)⟩
  have hXbp : IsPGroup 5 (barM M X) := fun x =>
    ⟨1, Subtype.ext (by simpa using (isElemAbelian_barM (M := M) h.elem).2 x x.2)⟩
  have hle : barM M X ≤ CFSG.pCore 5 (↥M ⧸ CFSG.pCore 2 ↥M) := by
    refine le_pCore_of_le_centralizer_components hXbp (hC h hind hO) fun l hl => ?_
    by_cases hl2 : l = 2
    · rw [hl2, pCore_quotient_pCore_eq_bot']
      exact Subgroup.le_centralizer_iff.mp bot_le
    by_cases hl5 : l = 5
    · rw [hl5, hO]
      exact Subgroup.le_centralizer_iff.mp bot_le
    exact h.le_centralizer_pCore h84 hD2 hl hl2 hl5
  rw [hO, le_bot_iff] at hle
  have hcard := card_barM_of_isPGroup h5 (by norm_num) hXM hXp
  rw [hle, Subgroup.card_bot, h.card_X] at hcard
  norm_num at hcard

end CFSG.AGLEmbedding

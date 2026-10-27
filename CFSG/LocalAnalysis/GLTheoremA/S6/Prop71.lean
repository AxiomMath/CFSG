module

public import CFSG.LocalAnalysis.GLTheoremA.S6.Prop71Aux

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB

structure Prop71Inputs (G : Type) [Group G] [Finite G] (p : ℕ) : Prop where
  i264 : I264ChevTwoAt G p
  i61 : I61L62At
  i106 : I106L62At G
  i131 : I131L62At G
  i182 : I182At G

variable {G : Type} [Group G] [Finite G] {p : ℕ}

theorem prop71_holds (hc : S6Ctx G p) (hin : Prop71Inputs G p) (hset : AltSetupAt G p)
    (h73 : Lemma73At G p) :
    ∀ (B : Subgroup G) (x : G) (L : Subgroup G), IsSStarMax p B x L →
      ¬ catalogIs (PSimple p L) isAltIndex := by
  intro B x L hB halt
  obtain ⟨n, y, J, S⟩ := hset B x L hB halt
  obtain ⟨⟨hp3, hB81, hn11⟩, y', J', hy'B, S', a, K, T, I, Sg, D⟩ := h73 B x L n y J hB S
  subst hp3
  subst hn11
  exact l71_false hc hin.i264 hin.i61 hin.i106 hin.i131 hin.i182 hB S' hy'B hB81 D

end CFSG.LocalAnalysis.GLTheoremA

module

public import CFSG.LocalAnalysis.AGL81TheoremCD.Section12.Defs
public import CFSG.LocalAnalysis.AGL81TheoremCD.RankThree.SectionNineAt

public section

namespace CFSG.LocalAnalysis.AGL81TheoremCD.Section12

open CFSG.Open

variable {G : Type} [Group G] [Finite G] {M : Subgroup G} {p : ℕ} {Q H : Subgroup G}

theorem nineTenConclusion_of_twelveCtx
    (h10 : CFSG.LocalAnalysis.RankThreeUC.AGL81C.NineTenGen) (h : TwelveCtx G M p Q H)
    {E : Subgroup G} (hEQ : E ≤ Q) (hE : IsElemAbelian p E) (hEc : Nat.card E = p ^ 2)
    (hΓ : rankThreeGamma 1 p E ≤ M) :
    CFSG.LocalAnalysis.RankThreeUC.AGL81C.NineTenConclusion G M E H E p :=
  CFSG.LocalAnalysis.AGL81TheoremCD.RankThree.nineTenAt_of_gen h10 p E H
    (h.hypCGen hEQ hE hEc hΓ)

theorem nineSettingGen {E : Subgroup G} (h : TwelveCtx G M p Q H) (hEQ : E ≤ Q)
    (hElem : IsElemAbelian p E) (hcard : Nat.card E = p ^ 2)
    (hΓ : rankThreeGamma 1 p E ≤ M) :
    CFSG.LocalAnalysis.RankThreeUC.AGL81C.NineSettingGen G M p Q H E 2 where
  setting :=
    { cstar := h.cstar
      maxLocal := h.maxLocal
      sigma_nonempty := h.sigma_nonempty }
  mem_Q := h.mem_QSet
  mem_H := ⟨h.H_ne_top, h.H_mem_H4.1.2.1, h.H_mem_H4.1.2.2.1⟩
  stdE := ⟨Or.inl rfl, hEQ, hElem, hcard, hΓ⟩

end CFSG.LocalAnalysis.AGL81TheoremCD.Section12

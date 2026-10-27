module

public import CFSG.LocalAnalysis.GLTheoremA.S10.CaseAlphaEnd
public import CFSG.LocalAnalysis.GLTheoremA.S10.CaseBeta
public import CFSG.LocalAnalysis.GLTheoremA.S10.CaseGamma

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.LocalAnalysis.GLTheoremA.S10
open scoped commutatorElement

theorem prop101 {G : Type} [Group G] [Finite G] {p : ℕ} (hc : S10Ctx G p) (hs : SetupInputs G p)
    (h103 : Lemma103Inputs G p) (ha : AlphaInputs G p) (hb : BetaInputs G p) (hg : GammaInputs G p) :
    Concl101 G p := by
  by_cases hA1 : Alt1 G p
  · exact Or.inl hA1
  obtain ⟨B, x, L, b, h⟩ := exists_cfg hc hs
    (fun _ hp hp2 _ _ _ hL hLX hN hC hxX hxo hxc => lemma103_pow_core hp hp2 hL hLX hN hC hxX hxo hxc) hA1
  obtain ⟨hd5, hcase⟩ := lemma103 hc h103 h
  rcases hcase with hA | hU
  · exact (hA1 (caseAlpha hc ha h hd5 hA)).elim
  · by_cases hβ : ∀ a ∈ Dgrp b x, a ≠ 1 →
        catalogIs (PSimple p (Jpart p (Ipart p L b) a)) (fun i => S9.isU4two i ∨ S9.isU4eight i)
    · exact (caseBeta hc hb h hd5 ⟨hU, hβ⟩).elim
    · exact Or.inr (caseGamma hc hg h hd5 ⟨hU, hβ⟩)

end CFSG.LocalAnalysis.GLTheoremA

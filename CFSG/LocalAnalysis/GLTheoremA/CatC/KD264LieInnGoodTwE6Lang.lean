module

public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieInnGoodLangAlg
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.GoodWiringTw

public section

namespace CFSG.LocalAnalysis.GLTheoremA.KD264Lie

open CFSG.Blueprint.Chevalley CFSG.HardMathSupport.Timmesfeld.LangTorus
  CFSG.HardMathSupport.Timmesfeld.LocalTwo CFSG.HardMathSupport.Timmesfeld.CrossChar
  CFSG.HardMathSupport.Timmesfeld.DefChar CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross
  CFSG.RankThree.Lattice CFSG.LieType.SeitzGeneration

set_option linter.unusedSectionVars false


private theorem perfectCentralizerPlanes_cat_of_langTorusAtAlgW {k : LieFamily}
    (hk : IsExceptionalFam k) {R : ℕ → ℕ → Prop}
    {W : ∀ {L : Type} [Field L] [IsAlgClosed L] {p : ℕ}, LangSetup (excTag k) L p → Prop}
    (ha : LangTorusAtAlgW k R W)
    (hbig : ∀ (L : Type) [Field L] [IsAlgClosed L] (p : ℕ) (S : LangSetup (excTag k) L p)
      (q : ℕ), R p q → S.D.q = q → S.IsAlgebraic → W S →
      ∀ D₁ : Subgroup (ModGL (excTag k) L), D₁ ≤ S.E → Nat.card D₁ = p ^ 2 →
        (bigComponentSet S D₁).Nonempty)
    (q : TauCeti.PrimePower)
    (hv : (HardMathSupport.Timmesfeld.LocalTwo.excIndex k q).Valid) {p : ℕ} (hp : p.Prime)
    (hR : R p q.card) (hpq : p ≠ q.p) :
    PerfectCentralizerPlanes p (CatT ⟨HardMathSupport.Timmesfeld.LocalTwo.excIndex k q, hv⟩) := by
  obtain ⟨L, hF, hA, S, hSq, hAlg, hW, hsyl, ⟨ε⟩⟩ := ha hk q hv p hp hR hpq
  exact PerfectCentralizerPlanes.of_mulEquiv ε.symm
    (perfectCentralizerPlanes_of_sylow_le_torus S hsyl
      (fun D₁ hD₁E hD₁c => hbig L p S q.card hR hSq hAlg hW D₁ hD₁E hD₁c))

theorem perfectCentralizerPlanes_cat_twistedE6_one (q : TauCeti.PrimePower)
    (hv : (TauCeti.LieTypeIndex.twistedE6 q).Valid) {p : ℕ} (hp : p.Prime) (hp7 : 7 ≤ p)
    (hpq : p ≠ q.p) (h1 : orderOf ((q.card : ℕ) : ZMod p) = 1) :
    PerfectCentralizerPlanes p (CatT ⟨.twistedE6 q, hv⟩) :=
  perfectCentralizerPlanes_cat_of_langTorusAtAlgW (k := .twistedE6) trivial
    (langTorusAtAlgW_twistedE6_1 frobeniusOnRoots_proved)
    (fun L _ _ p S q' hR hSq _ hW D₁ hD₁E hD₁c =>
      bigComponentSet_nonempty_of_classCheck S (Or.inr (Or.inl rfl)) (toMat_cartanList _) hW.1
        (three_le_q_of_class S hR.1 (Or.inl rfl) (by rw [hSq]; exact hR.2)) hR.1
        (by rw [hSq]; exact hR.2) twE6One_classCheck hD₁E hD₁c)
    q hv hp ⟨hp7, h1⟩ hpq

theorem perfectCentralizerPlanes_cat_twistedE6_two (q : TauCeti.PrimePower)
    (hv : (TauCeti.LieTypeIndex.twistedE6 q).Valid) {p : ℕ} (hp : p.Prime) (hp7 : 7 ≤ p)
    (hpq : p ≠ q.p) (h2 : orderOf ((q.card : ℕ) : ZMod p) = 2) :
    PerfectCentralizerPlanes p (CatT ⟨.twistedE6 q, hv⟩) :=
  perfectCentralizerPlanes_cat_of_langTorusAtAlgW (k := .twistedE6) trivial
    (langTorusAtAlgW_twistedE6_2 frobeniusOnRoots_proved)
    (fun L _ _ p S q' hR hSq _ hW D₁ hD₁E hD₁c =>
      bigComponentSet_nonempty_of_classCheck S (Or.inr (Or.inl rfl)) (toMat_cartanList _) hW.1
        (three_le_q_of_class S hR.1 (Or.inr (Or.inl rfl)) (by rw [hSq]; exact hR.2)) hR.1
        (by rw [hSq]; exact hR.2) twE6Two_classCheck hD₁E hD₁c)
    q hv hp ⟨hp7, h2⟩ hpq

end CFSG.LocalAnalysis.GLTheoremA.KD264Lie

end

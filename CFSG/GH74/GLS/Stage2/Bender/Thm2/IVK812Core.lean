module

public import CFSG.GH74.GLS.Stage2.Bender.Thm2.IVK812Stmt
public import CFSG.GH74.GLS.Stage2.Bender.Thm2.IVK812Quot
public import CFSG.GH74.GLS.Stage2.Bender.Thm2.L121Cover
public import CFSG.GH74.GLS.Stage2.Bender.Thm2.Stmt12

public section

namespace CFSG.GH74.GLS.Stage2.Bender.Thm2

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.Stage2.Local CFSG.GH74.GLS.Bg CFSG.GH74.GLS.Stage2.Signalizer
  CFSG.GH74.GLS.Stage2.Bender.Thm1

theorem ivk_8_12_ly_of_core (h : IVK812Core) : IVK_8_12_ly := by
  intro G _ _ z S ctx H hH hSH V hV hVO
  obtain ⟨ha, hly⟩ := h G z S ctx H hH hSH V hV hVO
  by_cases h11 : IsDoubleCoverOfAlt (HBar H) 11
  · have hb := fun V' (hV' : MaxSInv 3 S H V') (hV'O : ¬ V' ≤ pPrimeCoreOf 2 H) =>
      IVK812.branch_two_a11 hSH (L121.card_S_eq ctx) h11 hV.1 hV.2.1 hV.2.2.1 hVO hV'.1 hV'.2.1
        hV'.2.2.1 hV'O
    exact ⟨Or.inl h11, fun V' hV' hV'O => (hb V' hV' hV'O).2, (hb V hV hVO).1⟩
  · exact ⟨ha, (hly (ha.resolve_left h11)).1, (hly (ha.resolve_left h11)).2⟩

theorem ivk812Core_of_parts (ha : IVK812CoreA) (hly : LyInvariantThree) : IVK812Core := by
  intro G _ _ z S ctx H hH hSH V hV hVO
  refine ⟨ha G z S ctx H hH hSH V hV hVO, fun hLy => ?_⟩
  have hcard : Nat.card ↥(barIn H S) = 2 ^ 8 := by
    rw [IVK812.card_barIn_two hSH (IsPGroup.of_card (L121.card_S_eq ctx)), L121.card_S_eq ctx]
  have huniq : ∀ W W' : Subgroup (HBar H), IsPGroup 3 ↥W → IsPGroup 3 ↥W' → W ≠ ⊥ → W' ≠ ⊥ →
      barIn H S ≤ normalizer (W : Set (HBar H)) → barIn H S ≤ normalizer (W' : Set (HBar H)) →
      W = W' ∧ Nat.card ↥W = 3 := fun W W' hW hW' hW1 hW1' hn hn' =>
    hly (HBar H) hLy (barIn H S) hcard W W' hW hW' hW1 hW1' hn hn'
  have hb := fun V' (hV' : MaxSInv 3 S H V') (hV'O : ¬ V' ≤ pPrimeCoreOf 2 H) =>
    IVK812.clauses_of_bar_unique huniq hV.1 hV.2.1 hV.2.2.1 hVO hV'.1 hV'.2.1 hV'.2.2.1 hV'O
  exact ⟨fun V' hV' hV'O => (hb V' hV' hV'O).2, (hb V hV hVO).1⟩

theorem ivk_8_12_ly_of_parts (ha : IVK812CoreA) (hly : LyInvariantThree) : IVK_8_12_ly :=
  ivk_8_12_ly_of_core (ivk812Core_of_parts ha hly)

end CFSG.GH74.GLS.Stage2.Bender.Thm2

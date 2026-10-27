module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.KSubTFacts
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I91T9

public section

namespace CFSG.LocalAnalysis.GLTheoremA.KSubT

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremA
  CFSG.LocalAnalysis.GLTheoremA.S10

theorem card_isL2eight (hb : CatDistinct.OrderBridge) {S : Type} [Group S] [Finite S]
    (h : catalogIs S S10.isL2eight) : Nat.card S = 504 := by
  obtain ⟨i, hi, ⟨e⟩⟩ := h
  cases i with
  | cyclic p hp => simp [S10.isL2eight, onLie] at hi
  | alternating n hn => simp [S10.isL2eight, onLie] at hi
  | sporadic s => simp [S10.isL2eight, onLie] at hi
  | lie idx =>
    obtain ⟨d, hv⟩ := idx
    cases d with
    | A r q =>
      rcases r with _ | _ | r
      · simp [S10.isL2eight, onLie] at hi
      · rw [hb ⟨.A 1 q, hv⟩ S ⟨e⟩]
        show CFSG.HardMathSupport.Solomon.Coordinator.I1420.lieOrderFormula (.A 1 q) = 504
        have hq : q.card = 8 := hi
        simp only [CFSG.HardMathSupport.Solomon.Coordinator.I1420.lieOrderFormula, hq]
        decide
      · simp [S10.isL2eight, onLie] at hi
    | _ => simp [S10.isL2eight, onLie] at hi

theorem listDistinct_holds
    : ListDistinct := by
  have hb : CatDistinct.OrderBridge := CFSG.HardMathSupport.Solomon.Coordinator.lieOrderBridge_holds
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro S _ _ h1 h2
    have c1 := CFSG.LocalAnalysis.GLTheoremA.CatB.U48.card_of_isU4two h1
    have c2 := CFSG.LocalAnalysis.GLTheoremA.I91T.card_isA6 h2
    omega
  · intro S _ _ h1 h2
    have c1 := CatDistinct.card_isU5two hb h1
    have c2 := CFSG.LocalAnalysis.GLTheoremA.I91T.card_isA6 h2
    omega
  · intro S _ _ h1 h2
    have c1 := CFSG.LocalAnalysis.GLTheoremA.I91T.card_isA6 h1
    have c2 := card_isL2eight hb h2
    omega
  · intro S _ _ h1 h2
    have c1 := CFSG.LocalAnalysis.GLTheoremA.CatB.U48.card_of_isU4two h1
    have c2 := card_isL2eight hb h2
    omega
  · intro S _ _ h1 h2
    have c1 := CatSingle.card_isSp6two hb h1
    have c2 := card_isL2eight hb h2
    omega

end CFSG.LocalAnalysis.GLTheoremA.KSubT

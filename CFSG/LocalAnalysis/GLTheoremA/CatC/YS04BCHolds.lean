module

public import CFSG.LocalAnalysis.GLTheoremA.CatC.YS04BCLie
public import CFSG.LocalAnalysis.GLTheoremA.CatC.YS04Holds

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 TauCeti
open CFSG.ComponentClassification.OuterAutomorphisms (inner Outer)


theorem kd26bcSimple_of_residuals
    (hL : KD26bcLinUni) (hD4 : KD26bcD4) (hE6 : KD26bcE6) :
    KD26bcSimple := by
  intro S _ _ hs hna hC p hp hp2 _ D hD hcard hinn
  obtain ⟨i, ⟨e⟩⟩ := hC
  have hp3 : 3 ≤ p := by have := hp.two_le; omega
  cases i with
  | cyclic q _ => exact (false_of_cyclic q e hna).elim
  | alternating n hn => exact (false_of_alt hn e hp3 D hcard hinn).elim
  | sporadic name =>
    have hout : Nat.card (Outer S) ≤ 2 :=
      CFSG.HardMathSupport.Timmesfeld.Proving.sporadicOuterLeTwo_holds S hs hna name ⟨e⟩
    exact (false_of_outer_le hp3 hout (by norm_num) D hcard hinn).elim
  | lie d => exact bc_lie_case hL hD4 hE6 hs hna hp hp2 d e D hD hcard hinn

theorem ys04_holds_of_bcRes
    (hI : ∀ (G : Type) [Group G] [Finite G] (m : ℕ), ThmACtx G m → I117D4UsedAt G)
    (hL : KD26bcLinUni) (hD4 : KD26bcD4) (hf : YS04F.KD26fE6) : YS04 :=
  ys04_holds_of_E6 hI (kd26bcSimple_of_residuals hL hD4 (kd26bcE6_of_fE6 hf)) hf

end CFSG.LocalAnalysis.GLTheoremA

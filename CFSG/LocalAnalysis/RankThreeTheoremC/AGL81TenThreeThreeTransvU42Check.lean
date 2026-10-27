module

public import CFSG.LocalAnalysis.ComponentClassification.CatFactsSmallPSp43ModelData
public import CFSG.LocalAnalysis.EvenSporadicStandard.M22Std.P21HCommCheck

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.TenThreeThree.TransvW.U42

open CFSG.KGroups.Native CFSG.GH74.KGroups.NativeChecks CFSG.Certificates CFSG.Sporadic.Schreier
  CFSG.EvenSporadicStandard.M22Std.P21H CFSG.ComponentClassification.CatFactsSmall.PSp43

@[expose] def noElemOrderCheck (n : ℕ) (L : List (Array ℕ)) (m : ℕ) : Bool :=
  L.all fun g => !orderIsA n g m

variable {n : ℕ}

theorem noElemOrder_of_check {Q : RawSchreierDatum n} (hQ : ValidSchreier Q) {m : ℕ} (hm : 0 < m)
    (h : noElemOrderCheck n (enumA Q) m = true) {y : Equiv.Perm (Fin n)}
    (hy : y ∈ Q.originalSubgroup) : orderOf y ≠ m := by
  intro hym
  have h0 := List.all_eq_true.1 h _ (toA_mem_enumA_of_mem hQ hy)
  rw [orderIsA_rep (rep_toA y) m, (orderIs_iff y hm).2 hym] at h0
  exact absurd h0 (by decide)

@[expose] def u42NoFifteenCheck : Bool := noElemOrderCheck 45 (enumA QP45) 15

end CFSG.LocalAnalysis.RankThreeTheoremC.TenThreeThree.TransvW.U42

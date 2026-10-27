module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.HypA2.LeavesR
public import CFSG.LocalAnalysis.OddStandard.AltStdSecLookupNum
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1SporNum
public import CFSG.LocalAnalysis.SeitzReduction.CrossChar
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofLieOrder

public section

namespace CFSG.OddStandard.SmallF3.HypA2Leaves

open CFSG.Blueprint CFSG.ComponentClassification.CatLeaf

section


private theorem oddLieOrder_card {S : Type} [Group S] (hO : LieOrderFormulasInput) {r : ℕ}
    (hr : r.Prime) (hr2 : r ≠ 2) {τ : Open.StatedLieTag} {n f : ℕ} (hY : LieModel S τ n r f) :
    ComponentClassification.HarrisLit.T1.SporRow.OddLieOrder (Nat.card S) := by
  obtain ⟨-, hmul, hfac⟩ := hO S τ n r f hY.admissible hY
  exact ⟨τ, n, r, f, hr, hr2, hY.admissible, hmul, hfac⟩

theorem residualNotChevOdd_holds : HypA2.ResidualNotChevOdd := by
  intro S _ _ r hr hr2 hS h
  have hO : LieOrderFormulasInput :=
    ComponentClassification.CatLeafProof.lieOrderFormulasInput
  obtain ⟨τ, n, f, hY⟩ := hS
  have hodd : OddLieType S := ⟨τ, n, r, f, hr, hr2, hY.admissible, hY⟩
  rcases h with ⟨m, hm, ⟨e⟩⟩ | hHS | hX | hX | hX | hX | hX
  · rcases Nat.lt_or_ge m 9 with hlt | hge
    · obtain rfl : m = 8 := by omega
      have hc : Nat.card S = 20160 := by
        rw [OddStandard.AltStdSec.card_eq_of_equiv_alt (by norm_num) e]
        decide
      exact ComponentClassification.HarrisLit.T1.SporRow.not_oddLieOrder_L34
        (hc ▸ oddLieOrder_card hO hr hr2 hY)
    · exact OddStandard.AltStdSec.false_of_lieModel_alt hO hge e hY.admissible hY
  · obtain ⟨e⟩ := hHS
    have hc : Nat.card S = 44352000 := by
      rw [Nat.card_congr e.toEquiv]
      exact Sporadic.HS.card_HS
    exact ComponentClassification.HarrisLit.T1.SporRow.not_oddLieOrder_HS
      (hc ▸ oddLieOrder_card hO hr hr2 hY)
  all_goals
    exact SeitzReduction.CrossChar.not_oddLieType_of_lieModel_two hO hX (by decide) (by decide)
      (by decide) hodd

end

end CFSG.OddStandard.SmallF3.HypA2Leaves

module

public import CFSG.LocalAnalysis.SectionRank.QTK.J4InspA4Levi
public import CFSG.LocalAnalysis.SectionRank.QTK.J4InspOddHolds

public section

namespace CFSG.SectionRank.QTK

theorem j4ListInspect_holds :
    J4ListInspect := by
  unfold J4ListInspect
  intro S _ _ hS L _ _ j hj hperf Q _ hQ hPSL hnt
  unfold QTKSimpleList at hS
  have h15 := two_pow_fifteen_dvd_card faithfulL34ModDim_holds j hj Q hQ hperf hPSL hnt
  rcases hS with hA | hB | hC | hD | hE
  · obtain ⟨n, h5, h9, ⟨e⟩⟩ := hA
    exact absurd h15 (not_two_pow_fifteen_dvd_alt h5 h9 e)
  · exact (odd_branch_false_of_sectional oddCharSectionalTwoRankQTK_holds faithfulL34ModDim_holds
      hB j hj Q hQ hperf hPSL hnt).elim
  · exact (char2_branch_false_of_levi hC j hj Q hQ hperf hPSL hnt).elim
  · rcases hD with ⟨n, hn, hPSLn⟩ | hPSp
    · exact absurd h15 (not_two_pow_fifteen_dvd_psl_four_five_two hn hPSLn)
    · rw [sp6TwoOrder_holds S hPSp] at h15
      norm_num at h15
  · obtain ⟨s, hs, ⟨e⟩⟩ := hE
    by_cases hJ : s = .J4
    · subst hJ
      obtain ⟨b⟩ := CFSG.Sporadic.Bridge.J4.nonempty_mulEquiv
      exact ⟨e.trans b⟩
    · exfalso
      have hs' : s = .M11 ∨ s = .M12 ∨ s = .M22 ∨ s = .M23 ∨ s = .M24 ∨ s = .J1 ∨ s = .J2 ∨
          s = .J3 ∨ s = .HS ∨ s = .He ∨ s = .Ru ∨ s = .McL := by
        tauto
      have hc : Nat.card S = Nat.card (CFSG.Blueprint.NativeSporadic.Carrier s) :=
        Nat.card_congr e.toEquiv
      rw [hc] at h15
      exact not_two_pow_fifteen_dvd_sporadic s hs' h15

end CFSG.SectionRank.QTK

end

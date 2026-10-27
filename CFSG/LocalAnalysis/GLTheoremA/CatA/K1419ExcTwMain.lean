module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.K1419ExcTwHigh
public import CFSG.LocalAnalysis.GLTheoremA.CatA.K1419ExcTwLane
public import CFSG.HardMathSupport.Dickson.Sec6.Up34Chev2Aux.InnExcRDF4

public section

namespace CFSG.LocalAnalysis.GLTheoremA.K1419E

open CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.HardMathSupport.Timmesfeld.CrossChar
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.LieType.AlgebraicGroups
  CFSG.RankThree.PartOne.KD4T CFSG.HardMathSupport.Dickson.Sec6
  CFSG.HardMathSupport.Dickson.Sec6.Up34Exc CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple

section Main


theorem char2L3U3_twoD (hF : L3U3Facts) {τ : Tag}
    (hτ : τ = .F4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8) : Char2L3U3 τ .twoD := by
  intro L _ _ _ p₀ S a hT hap h1 i hk _ hL
  exfalso
  haveI := ssTw_finite_rationalComponent S i
  obtain ⟨hnin, h4, hcard⟩ := twoD_kind_unpack hk
  have hTp : rootDiagUnit τ a ^ 3 = 1 := rootDiagUnit_pow_eq_one_of_forall hap
  by_cases h5 : 5 ≤ compRank (componentRoots (rootCharHom a) i)
  · exact not_l3u3_twoD_high hF S hT hap h1 i h5 hcard hnin hL
  · have hr : compRank (componentRoots (rootCharHom a) i) = 4 := by omega
    have hc : (componentRoots (rootCharHom a) i).ncard = 24 := by rw [hcard, hr]
    rcases hτ with rfl | -
    · rcases rdValues_F4 L a hap i with h | h | h <;> omega
    · exact not_l3u3_d4class hF S hT hTp h1 i hr hc hnin hL

theorem char2L3U3_exc (hF : L3U3Facts) {τ : Tag}
    (hτ : τ = .F4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8) : Char2L3U3 τ .exc := by
  intro L _ _ _ p₀ S a hT hap h1 i hk _ hL
  exfalso
  haveI := ssTw_finite_rationalComponent S i
  obtain ⟨hnin, h⟩ := exc_kind hk
  have hTp : rootDiagUnit τ a ^ 3 = 1 := rootDiagUnit_pow_eq_one_of_forall hap
  rcases h with ⟨h6, h72⟩ | ⟨h4, h24, -⟩
  · rcases hτ with rfl | hτ'
    · have hle := compRank_le_rank (componentRoots (rootCharHom a) i)
      rw [h6] at hle
      exact absurd hle (by decide)
    · exact not_l3u3_exc_e6class hF hτ' S hT hap h1 i h6 h72 hnin hL
  · exact not_l3u3_d4class hF S hT hTp h1 i h4 h24 hnin hL

end Main

end CFSG.LocalAnalysis.GLTheoremA.K1419E

end

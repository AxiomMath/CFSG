module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.T171ShapeExcHighFixE6
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T171ShapeExcKernelHighCube

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T171Sh

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.AlgebraicGroups
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.HardMathSupport.Timmesfeld.CrossChar

section Main


theorem excHighRankFixedPerfectAll_holds : ExcHighRankFixedPerfectAll := by
  intro τ L _ _ _ p₀ p S hp hp2 hτ a hT _ hTp h1 _ i hk hr _ _
  have hpL : (p : L) ≠ 0 := fun h =>
    hp2 ((Nat.prime_dvd_prime_iff_eq Nat.prime_two hp).1 ((CharP.cast_eq_zero_iff L 2 p).1 h)).symm
  obtain ⟨-, hA | ⟨hr4, -, -⟩⟩ := exc_kind hk
  swap
  · exact absurd hr4 hr
  have h6 : 6 ≤ τ.rank := by
    have := compRank_le_rank (τ := τ) (componentRoots (rootCharHom a) i)
    rwa [hA.1] at this
  rcases hτ with rfl | rfl | rfl | rfl | rfl | rfl
  · exact absurd h6 (by decide)
  · exact absurd h6 (by decide)
  · exact absurd h6 (by decide)
  · exact absurd (rootDiagUnit_eq_one_of_ncard i (by rw [hA.2]; rfl)) h1
  · obtain ⟨v, hv⟩ := S.e6_pinnedT_of_prime hp hpL facts_E7 kacCount_E7_six (by decide)
      (by decide) hTp i hA.1 hA.2
    exact twoDExcFixedData_of_e6Class S hT i v hv
  · obtain ⟨v, hv⟩ := S.e6_pinnedT_of_prime hp hpL facts_E8 kacCount_E8_six (by decide)
      (by decide) hTp i hA.1 hA.2
    exact twoDExcFixedData_of_e6Class S hT i v hv

end Main

end CFSG.LocalAnalysis.GLTheoremA.T171Sh

end

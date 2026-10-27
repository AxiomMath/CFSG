module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Solomon78.HNCenterFour
public import CFSG.LocalAnalysis.EvenSporadicStandard.Solomon78.HNCenterSix
public import CFSG.Sporadic.HNOddCore.Fusion
public import CFSG.Sporadic.HNSchreier.Faithful

public section

namespace CFSG.EvenSporadicStandard.Solomon78

open CFSG.Sporadic.HNSchreier CFSG.Sporadic.HNOddCore CFSG.Blueprint.NativeSporadic

theorem isConj_aJ_or_t4J
    {a : JH} (ha : orderOf a = 2) :
    IsConj aJ a ∨ IsConj t4J a := by
  have h2 : a ^ 2 = 1 := ha ▸ pow_orderOf_eq_one a
  have h1 : a ≠ 1 := fun h => by
    rw [h, orderOf_one] at ha
    exact absurd ha (by norm_num)
  have h2R : jR a ^ 2 = 1 := by rw [← map_pow, h2, map_one]
  have h1R : jR a ≠ 1 := fun h => h1 (jR_injective (by rw [h, map_one]))
  rcases involution_cover_R h2R h1R with h | h | h
  · exact absurd h (not_isConj_c_jR a)
  · exact Or.inl (isConj_t2_aJ.symm.trans (isConj_J_of_R t2J_sq t2J_ne_one h))
  · exact Or.inr (isConj_J_of_R t4J_sq' t4J_ne_one h)

theorem centerInvolutions_jh :
    CenterInvolutions JH := by
  refine CenterInvolutions.of_classes [aJ, t4J] (fun s hs => ?_) (fun r hr => ?_)
  · rcases isConj_aJ_or_t4J hs with h | h
    · exact ⟨aJ, by simp, h.symm⟩
    · exact ⟨t4J, by simp, h.symm⟩
  · rcases List.mem_pair.1 hr with rfl | rfl
    · exact centerInvAt_aJ
    · exact centerInvAt_t4J

end CFSG.EvenSporadicStandard.Solomon78

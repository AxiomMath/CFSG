module

public import CFSG.CGT.PushingUpLit.CGT6.EmbEndSmall
public import CFSG.RankThree.PartOne.Mult.Sporadic

public section

namespace CFSG.CGT.PushingUpLit.CGT6

open CFSG CFSG.Blueprint CFSG.RankThree.PartOne

theorem sporadicThreeCenterSmallPrimes_holds
    : SporadicThreeCenterSmallPrimes := by
  intro K _ _ hK hs p hp hp3 hpZ
  have : Group.IsPerfect K := hK.1
  have key : ∀ s : TauCeti.SporadicName, (s = .M12 ∨ s = .J1 ∨ s = .J2) →
      NativeSporadic.IsSporadic (K ⧸ Subgroup.center K) s → False := by
    intro s hsn he
    obtain ⟨e⟩ := he
    have hpair := (Mult.sporadic_residual_of_center e hp hp3 hpZ).1
    rcases hsn with rfl | rfl | rfl <;>
      (rcases hpair with ⟨-, h⟩ | ⟨-, h⟩ | h <;> simp at h)
  rcases hs with h | h | h
  · exact key .M12 (Or.inl rfl) h
  · exact key .J1 (Or.inr (Or.inl rfl)) h
  · exact key .J2 (Or.inr (Or.inr rfl)) h

end CFSG.CGT.PushingUpLit.CGT6

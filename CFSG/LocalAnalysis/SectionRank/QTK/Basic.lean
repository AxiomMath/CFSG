module

public import CFSG.Assembly.RankThreeEvenDefs
import CFSG.RankThree.PartTwo.Census.Criteria
import CFSG.RankThree.Classical.EvenSurvivingScalarRank

public section

namespace CFSG.SectionRank.QTK

open CFSG.Assembly.RankThreeEven (localRank)

@[expose] def qtkSporadicNames : Finset TauCeti.SporadicName :=
  {.M11, .M12, .M22, .M23, .M24, .J1, .J2, .J3, .J4, .HS, .He, .Ru, .McL}

theorem localRank_le_evenRank {G : Type*} [Group G] [Finite G] {r : ℕ} (hr : r.Prime)
    (hr2 : r ≠ 2) : localRank r G ≤ CFSG.Open.evenRank G := by
  refine csSup_le' ?_
  rintro _ ⟨H, hH, rfl⟩
  refine le_csSup ⟨Nat.card G, ?_⟩ ⟨r, H, hr, hr2, hH, rfl⟩
  rintro _ ⟨q, K, hq, -, -, rfl⟩
  exact CFSG.RankThree.Classical.pRank_le_natCard hq.one_lt K

theorem not_evenRank_le_two_of_localRank {S T : Type} [Group S] [Group T] [Finite S]
    (e : S ≃* T) {r : ℕ} (hr : r.Prime) (hr2 : r ≠ 2) (h : ∀ [Finite T], 3 ≤ localRank r T) :
    ¬ CFSG.Open.evenRank S ≤ 2 := by
  intro hS
  have : Finite T := Finite.of_equiv S e.toEquiv
  have h1 : 3 ≤ localRank r S := by
    rw [CFSG.RankThree.PartTwo.Census.localRank_eq_of_mulEquiv e hr]
    exact h
  have h2 := localRank_le_evenRank (G := S) hr hr2
  omega

end CFSG.SectionRank.QTK

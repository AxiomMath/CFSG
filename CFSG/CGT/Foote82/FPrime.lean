module

public import CFSG.CGT.Foote82.FPrimeDefs
import CFSG.RankThree.PartTwo.Sec19.SimsItem316Narrow
import CFSG.LocalAnalysis.WeakClosure81.Eleven
public import CFSG.LocalAnalysis.AGLEmbedding.WeakBlockInputs
public import CFSG.RankThree.PartTwo.Sec19.SimsTheoremCTypes

public section

namespace CFSG.CGT.Foote82

open CFSG.Open CFSG.QuasithinUnique CFSG.RankThree.PartTwo CFSG.AGLEmbedding
open CFSG.RankThree.PartTwo.Sec19.SimsTheoremC

variable {G : Type} [Group G] [Finite G]

theorem isFPrimeType_of_le (he : evenRank G = 3) {M J : Subgroup G} (hM : GLBIsMaxTwoLocal M)
    (hJM : J ≤ M) (hJ : IsFType J) : IsFPrimeType J := by
  have hM' : CFSG.IsMaximalTwoLocal M := ⟨hM.1, fun H hlt hH => hlt.ne (hM.2 H hH hlt.le).symm⟩
  rcases hJ with h | h | ⟨m, hm, h⟩ | ⟨m, hm, h⟩ | h
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · have h4 := Sec19.Narrow316.lt_four_of_isOmegaPlusType he hM' hJM h
    obtain rfl : m = 3 := by omega
    exact Or.inr (Or.inr (Or.inl h))
  · have h4 := Sec19.Narrow316.lt_four_of_isOmegaMinusType he hM' hJM h
    rcases (by omega : m = 2 ∨ m = 3) with rfl | rfl
    · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))

theorem exists_glbIsMaxTwoLocal_of_isFooteBlock {H J : Subgroup G} (hJ : IsFooteBlock H J) :
    ∃ M : Subgroup G, GLBIsMaxTwoLocal M ∧ J ≤ M := by
  have hQ : pCoreOf 2 J ≠ ⊥ := by
    intro h
    have hU : blockU J = ⊥ := by
      rw [blockU, show blockQ J = ⊥ from h, Subgroup.commutator_bot_left]
    have hlt := hJ.chief.1
    rw [hU] at hlt
    exact not_lt_bot hlt
  have h2l : IsTwoLocal (Subgroup.normalizer (pCoreOf 2 J : Set G)) :=
    ⟨pCoreOf 2 J, hQ, CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_isPGroup 2 J, rfl⟩
  obtain ⟨M, hM, hNM⟩ := CFSG.LocalAnalysis.WeakClosure81.exists_isMaxTwoLocalSubgroup_le h2l
  exact ⟨M, hM, (CFSG.RankThreeCoreUniqueness.Helpers.localGroup_le_normalizer_pCoreOf 2 J).trans
    hNM⟩

theorem isFPrimeType_of_isFooteBlock (he : evenRank G = 3) {H J : Subgroup G}
    (hJ : IsFooteBlock H J) (hJF : IsFType J) : IsFPrimeType J := by
  obtain ⟨M, hM, hJM⟩ := exists_glbIsMaxTwoLocal_of_isFooteBlock hJ
  exact isFPrimeType_of_le he hM hJM hJF

theorem fPrimeOfEvenRankThree :
    ∀ (G : Type) [Group G] [Finite G], IsSimpleGroup G → (∃ a b : G, a * b ≠ b * a) →
      CFSG.Assembly.KProper CFSG.Assembly.InCatalog G → IsCharTwoType G → evenRank G = 3 →
        ∀ J : Subgroup G, InFooteB J → IsFType J → IsFPrimeType J := by
  intro G _ _ _ _ _ _ he J hJB hJF
  obtain ⟨S, -, hSJ⟩ := hJB
  exact isFPrimeType_of_isFooteBlock he hSJ hJF

end CFSG.CGT.Foote82

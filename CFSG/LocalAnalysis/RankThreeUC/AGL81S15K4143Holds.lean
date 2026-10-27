module

public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15K4143Reduce
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.K2LieHolds
import CFSG.Adapters.LinearCatalogStated
import CFSG.LocalAnalysis.SectionRank.AmbientRank

public section

namespace CFSG.LocalAnalysis.RankThreeUC.S15

open CFSG.Open CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82
open CFSG.Blueprint (LieModel)

namespace K4143K2

theorem p_eq_two_of_card_eq_two {Q : TauCeti.PrimePower} (h : Q.card = 2) :
    Q.p = 2 ∧ Q.exponent = 1 := by
  have h2 : Q.p ^ Q.exponent = 2 := by
    rw [← TauCeti.PrimePower.card_def]
    exact h
  exact (Nat.Prime.pow_eq_iff Nat.prime_two).mp h2

theorem isLieFam811_of_isK4143Shape {L : Type} [Group L] (h : IsK4143Shape L) :
    ∃ (fam : LieFam811) (r f : ℕ), IsLieFam811 L fam r f := by
  obtain ⟨⟨d, hv⟩, hd, ⟨e⟩⟩ := h
  rcases k4143ShapeIdx_cases hd with ⟨Q, rfl, hp⟩ | ⟨Q, rfl, hp⟩ | ⟨Q, rfl, hQ⟩ | ⟨Q, rfl, hQ⟩
  · have hm := CFSG.RankThree.PartTwo.Census.statedClassicalModel_typeB_even 3 Q hv hp le_rfl e
    rw [hp] at hm
    exact ⟨.psp6, 2, Q.exponent, Nat.prime_two, by norm_num, Or.inl ⟨by decide, hm⟩⟩
  · have hm := CFSG.RankThree.PartTwo.Census.statedClassicalModel_typeTwistedD_even 4 Q hv hp e
    rw [hp] at hm
    exact ⟨.pomega8m, 2, Q.exponent, Nat.prime_two, by norm_num, Or.inl ⟨by decide, hm⟩⟩
  · obtain ⟨hp, hf⟩ := p_eq_two_of_card_eq_two hQ
    have hm := CFSG.Open.StatedAPI.statedClassicalModel_of_mulEquiv_typeA hv e
    rw [hp, hf] at hm
    exact ⟨.l6, 2, 1, Nat.prime_two, Or.inl ⟨by norm_num, Or.inl ⟨by decide, hm⟩⟩⟩
  · obtain ⟨hp, hf⟩ := p_eq_two_of_card_eq_two hQ
    have hm := CFSG.Open.StatedAPI.statedClassicalModel_of_mulEquiv_typeA hv e
    rw [hp, hf] at hm
    exact ⟨.l7, 2, 1, Nat.prime_two, Or.inl ⟨by norm_num, Or.inl ⟨by decide, hm⟩⟩⟩

end K4143K2

theorem K4143_holds : K4143 := by
  refine K4143K2.k4143_of_k2 fun L _ _ hshape hZ R hR hSyl hnle => ?_
  obtain ⟨fam, r, f, hLie⟩ := K4143K2.isLieFam811_of_isK4143Shape hshape
  have h4 := (k2Simple_of_parts fun _ _ _ _ _ _ h =>
    ⟨outPNice_three_of_isLieFam811 h, exists3_of_isLieFam811 h, outerFixed3_of_isLieFam811 h⟩)
    L fam r f hLie hZ R hR hSyl hnle
  rwa [CFSG.SectionRank.pRank_coe_eq_openPRank] at h4

end CFSG.LocalAnalysis.RankThreeUC.S15

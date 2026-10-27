module

public import CFSG.LocalAnalysis.SectionRank.QTK.Interface
public import CFSG.LocalAnalysis.SectionRank.QTK.ExcOdd
public import CFSG.LocalAnalysis.SectionRank.QTK.ExcRee
public import CFSG.LocalAnalysis.SectionRank.QTK.ExcEven

public section

namespace CFSG.SectionRank.QTK

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.Assembly.LowTwoRank
open CFSG.Assembly.RankThreeEven (localRank)


theorem qt_exceptional_restriction {S : Type} [Group S] [Finite S]
    (hQT : CFSG.Open.evenRank S ≤ 2) (h : ExceptionalRep S) : QTExceptionalList S := by
  have hfalse : ∀ r : ℕ, r.Prime → r ≠ 2 → 3 ≤ localRank r S → False := fun r hr hr2 hk => by
    have := localRank_le_evenRank (G := S) hr hr2
    omega
  rcases h with ⟨t, p, f, ht, hmod⟩ | ⟨t, p, f, ht, hmod⟩ | ⟨p, f, hmod⟩
  · have hmod' := hmod
    obtain ⟨⟨hp, hf, hadm⟩, hm⟩ := hmod
    simp only [chevalleyExceptionalTags, Finset.mem_insert, Finset.mem_singleton] at ht
    by_cases hp2 : p = 2
    · subst hp2
      rcases ht with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · refine Or.inr (Or.inl ⟨f, ?_, hmod'⟩)
        obtain ⟨-, h32⟩ := hadm
        by_contra hlt
        obtain rfl : f = 1 := by omega
        norm_num at h32
      all_goals first
        | exact (hfalse 3 Nat.prime_three (by norm_num)
            (three_le_localRank_of_untwistedModel_two (by simp) hm)).elim
        | exact (hfalse 3 Nat.prime_three (by norm_num)
            (three_le_localRank_of_twistedE6Model_two hf hm)).elim
        | exact Or.inr (Or.inr (Or.inl ⟨f, hf, hmod'⟩))
    · rcases ht with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · rcases Nat.lt_or_ge f 2 with hf2 | hf2
        · obtain rfl : f = 1 := by omega
          exact Or.inl ⟨p, hp, hp2, hmod'⟩
        · exact (hfalse p hp hp2
            (le_trans (by omega) (two_mul_le_localRank_of_G2Model_odd hp hp2 hm))).elim
      all_goals first
        | exact (hfalse p hp hp2 (le_trans (by omega)
            (four_mul_le_localRank_of_untwistedModel_odd (by simp) hp hp2 hm))).elim
        | exact (hfalse p hp hp2 (le_trans (by omega)
            (four_mul_le_localRank_of_twistedE6Model_odd hp hp2 hf hm))).elim
        | exact (hfalse p hp hp2 (le_trans (by norm_num)
            (four_le_localRank_of_trialityModel_odd hp hp2 hf hm))).elim
  · simp only [reeTitsTags, Finset.mem_insert, Finset.mem_singleton] at ht
    rcases ht with rfl | rfl | rfl
    · exact (hfalse 3 Nat.prime_three (by norm_num) (three_le_localRank_of_smallReeModel hmod)).elim
    · obtain ⟨-, -, -, hp, hodd, hf3⟩ := hmod.1
      subst hp
      exact Or.inr (Or.inr (Or.inr (Or.inl ⟨f, hodd, hf3, hmod⟩)))
    · obtain ⟨-, -, -, hp, hf1⟩ := hmod.1
      subst hp hf1
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hmod))))
  · have hmod' := hmod
    obtain ⟨hp, a, ha, K, _, _, hf, -⟩ := hmod'
    subst hp
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨f, ⟨a, hf⟩, by omega, hmod⟩))))

theorem qtExceptionalRestriction_holds : QTExceptionalRestriction :=
  fun _ _ _ hQT h => qt_exceptional_restriction hQT h

end CFSG.SectionRank.QTK

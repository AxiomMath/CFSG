module

public import CFSG.LocalAnalysis.SectionRank.QTK.CoverBOdd
import CFSG.RankThree.PartOne.S11c.ETypeRankThree
import CFSG.RankThree.GroupTheory.SteinbergBYHighTwoRankCover
public import CFSG.LocalAnalysis.SectionRank.QTK.ExcEven
public import CFSG.LocalAnalysis.SectionRank.QTK.ExcOdd
public import CFSG.LocalAnalysis.SectionRank.QTK.ExcRee
public import CFSG.LocalAnalysis.SectionRank.QTK.Interface

public section

namespace CFSG.SectionRank.QTK.CoverB

open Subgroup CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.Assembly.LowTwoRank
open CFSG.Assembly.RankThreeEven (localRank)

variable {G : Type} [Group G] [Finite G]

theorem qtExceptionalList_of_cover
    (he : CFSG.Open.evenRank G ≤ 2) {Y : Subgroup G} (h : ExceptionalRep (↥Y ⧸ center ↥Y))
    (hZ : ∀ (t : StatedLieTag) (n ℓ f : ℕ), LieModel (↥Y ⧸ center ↥Y) t n ℓ f → ∀ r : ℕ,
      r.Prime → r ≠ 2 → r ∣ Nat.card (center ↥Y) → TablePrime t n ℓ f r) :
    QTExceptionalList (↥Y ⧸ center ↥Y) := by
  have hfalse : ∀ r : ℕ, r.Prime → r ≠ 2 → ¬ r ∣ Nat.card (center ↥Y) →
      3 ≤ localRank r (↥Y ⧸ center ↥Y) → False := fun r hr hr2 hrZ hk =>
    false_of_three_le_localRank he (MulEquiv.refl _) hr hr2 hrZ hk
  have h3 : CFSG.twoLocalOddRank G ≤ 3 := by
    rw [CFSG.RankThree.GroupTheory.SteinbergBY.twoLocalOddRank_eq_evenRank]
    exact le_trans (show CFSG.Assembly.evenRank G ≤ 2 from he) (by norm_num)
  rcases h with ⟨t, p, f, ht, hmod⟩ | ⟨t, p, f, ht, hmod⟩ | ⟨p, f, hmod⟩
  · have hmod' := hmod
    have hL : LieModel (↥Y ⧸ center ↥Y) t 0 p f := Or.inr (Or.inl ⟨rfl, ht, hmod'⟩)
    obtain ⟨⟨hp, hf, hadm⟩, hm⟩ := hmod
    have hnd : ∀ r : ℕ, r.Prime → r ≠ 2 → (t = .E6 → ¬ 3 ∣ p ^ f - 1) →
        (t = .twistedE6 → ¬ 3 ∣ p ^ f + 1) → (t = .G2 → p = 3 → f ≠ 1) →
        ¬ r ∣ Nat.card (center ↥Y) := fun r hr hr2 hE6 h2E6 hG2 hrZ => by
      rcases hZ t 0 p f hL r hr hr2 hrZ with ⟨h0, -⟩ | ⟨h0, -⟩ | ⟨h0, -, h1⟩ | ⟨h0, -, h1⟩ |
          ⟨-, ⟨h0, -⟩ | ⟨h0, -⟩ | ⟨h0, -, h1, h2⟩ | ⟨h0, -⟩⟩
      all_goals subst h0
      all_goals first
        | (simp [chevalleyExceptionalTags] at ht; done)
        | exact hE6 rfl h1
        | exact h2E6 rfl h1
        | exact hG2 rfl h1 h2
    simp only [chevalleyExceptionalTags, Finset.mem_insert, Finset.mem_singleton] at ht
    have hE : t = .E6 ∨ t = .E7 ∨ t = .E8 ∨ t = .twistedE6 → t = .E6 ∧ p = 2 ∧ f = 1 :=
      fun hτ => CFSG.RankThree.PartOne.actualCoverETypeRankThreeOnlyE6FieldTwo G h3 Y p f hp hf t
        hτ hmod'
    by_cases hp2 : p = 2
    · subst hp2
      rcases ht with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · refine Or.inr (Or.inl ⟨f, ?_, hmod'⟩)
        obtain ⟨-, h32⟩ := hadm
        by_contra hlt
        obtain rfl : f = 1 := by omega
        norm_num at h32
      · exact (hfalse 3 Nat.prime_three (by norm_num)
          (hnd 3 Nat.prime_three (by norm_num) (by intro h; cases h) (by intro h; cases h)
            (by intro h; cases h)) (three_le_localRank_of_untwistedModel_two (by simp) hm)).elim
      · obtain ⟨-, -, rfl⟩ := hE (Or.inl rfl)
        exact (hfalse 3 Nat.prime_three (by norm_num)
          (hnd 3 Nat.prime_three (by norm_num) (fun _ => by norm_num) (by intro h; cases h)
            (by intro h; cases h)) (three_le_localRank_of_untwistedModel_two (by simp) hm)).elim
      · exact absurd (hE (Or.inr (Or.inl rfl))).1 (by intro h; cases h)
      · exact absurd (hE (Or.inr (Or.inr (Or.inl rfl)))).1 (by intro h; cases h)
      · exact absurd (hE (Or.inr (Or.inr (Or.inr rfl)))).1 (by intro h; cases h)
      · exact Or.inr (Or.inr (Or.inl ⟨f, hf, hmod'⟩))
    · rcases ht with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · rcases Nat.lt_or_ge f 2 with hf2 | hf2
        · obtain rfl : f = 1 := by omega
          exact Or.inl ⟨p, hp, hp2, hmod'⟩
        · exact (hfalse p hp hp2 (hnd p hp hp2 (by intro h; cases h) (by intro h; cases h)
            (fun _ _ => by omega))
            (le_trans (by omega) (two_mul_le_localRank_of_G2Model_odd hp hp2 hm))).elim
      · exact (hfalse p hp hp2 (hnd p hp hp2 (by intro h; cases h) (by intro h; cases h)
          (by intro h; cases h)) (le_trans (by omega)
            (four_mul_le_localRank_of_untwistedModel_odd (by simp) hp hp2 hm))).elim
      · exact absurd (hE (Or.inl rfl)).2.1 hp2
      · exact absurd (hE (Or.inr (Or.inl rfl))).1 (by intro h; cases h)
      · exact absurd (hE (Or.inr (Or.inr (Or.inl rfl)))).1 (by intro h; cases h)
      · exact absurd (hE (Or.inr (Or.inr (Or.inr rfl)))).1 (by intro h; cases h)
      · exact (hfalse p hp hp2 (hnd p hp hp2 (by intro h; cases h) (by intro h; cases h)
          (by intro h; cases h)) (le_trans (by norm_num)
            (four_le_localRank_of_trialityModel_odd hp hp2 hf hm))).elim
  · have hmod' := hmod
    simp only [reeTitsTags, Finset.mem_insert, Finset.mem_singleton] at ht
    rcases ht with rfl | rfl | rfl
    · have hL : LieModel (↥Y ⧸ center ↥Y) .twistedG2 0 p f :=
        Or.inr (Or.inr (Or.inl ⟨rfl, by simp [reeTitsTags], hmod'⟩))
      have hnd : ¬ 3 ∣ Nat.card (center ↥Y) := fun hrZ => by
        rcases hZ _ 0 p f hL 3 Nat.prime_three (by norm_num) hrZ with ⟨h0, -⟩ | ⟨h0, -⟩ |
            ⟨h0, -⟩ | ⟨h0, -⟩ | ⟨-, ⟨h0, -⟩ | ⟨h0, -⟩ | ⟨h0, -⟩ | ⟨h0, -⟩⟩ <;> cases h0
      exact (hfalse 3 Nat.prime_three (by norm_num) hnd
        (three_le_localRank_of_smallReeModel hmod)).elim
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

end CFSG.SectionRank.QTK.CoverB

module

public import CFSG.GH74.E2.Shapes
public import CFSG.GH74.E2.CompCerts
import CFSG.GH74.Filter.Small.Unipotent
import CFSG.GH74.Filter.Small.Exceptional
import CFSG.GH74.Filter.Orthogonal.EvenEichler
import CFSG.GH74.Filter.Orthogonal.SymplecticSix
import CFSG.GH74.Filter.Orthogonal.UnitaryEven
import CFSG.GH74.Filter.Lie.EvenSeries
import CFSG.GH74.Filter.Lie.TwistedE6Even
import CFSG.GH74.Filter.Lie.TwistedD4Even
import CFSG.GH74.Filter.Lie.Suzuki
import CFSG.GH74.Filter.Lie.TwistedF4
import CFSG.GH74.Filter.Lie.TitsElem
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.GH74.Filter.Statements

public section

namespace CFSG.GH74.E2

open CFSG.Blueprint

theorem even_lie_rank_le_four
    {S : Type} [Group S] [Finite S]
    (hs : IsSimpleGroup S)
    (hnab : ∃ a b : S, a * b ≠ b * a) (he : EvenLieType S) (h4 : SectionalTwoRankLE S 4) :
    ShapeA5 S ∨ ShapeL27 S ∨ ShapeL28 S ∨ ShapeSz8 S ∨ LieModel S .PSL 2 2 4 ∨
      LieModel S .PSL 3 2 2 ∨ LieModel S .PSL 4 2 1 ∨ LieModel S .PSU 3 2 2 ∨
      LieModel S .PSU 4 2 1 := by
  have _ := hs
  have _ := hnab
  have hgen : Gen4 S := h4
  obtain ⟨t, n, f, hadm, hmodel⟩ := he
  have hL : ∀ {n f : ℕ}, CFSG.Assembly.LowTwoRank.StatedClassicalModel S .PSL n 2 f →
      LieModel S .PSL n 2 f :=
    fun h => CFSG.GH74.Filter.lieModel_of_classical (by decide) h
  have hLU : ∀ {n f : ℕ}, CFSG.Assembly.LowTwoRank.StatedClassicalModel S .PSU n 2 f →
      LieModel S .PSU n 2 f :=
    fun h => CFSG.GH74.Filter.lieModel_of_classical (by decide) h
  rcases hmodel with ⟨ht, hcl⟩ | ⟨hn0, ht, hch⟩ | ⟨hn0, ht, hree⟩ | ⟨hn0, ht, hsz⟩
  ·
    simp only [classicalTags, Finset.mem_insert, Finset.mem_singleton] at ht
    rcases ht with rfl | rfl | rfl | rfl | rfl | rfl
    ·
      obtain ⟨hp, hf, hn2, h22, -⟩ := hadm
      obtain rfl | rfl | rfl | rfl | hn6 : n = 2 ∨ n = 3 ∨ n = 4 ∨ n = 5 ∨ 6 ≤ n := by omega
      · have hf2 : 2 ≤ f := by
          by_contra h
          obtain rfl : f = 1 := by omega
          exact h22 (by norm_num)
        obtain rfl | rfl | rfl | hf5 : f = 2 ∨ f = 3 ∨ f = 4 ∨ 5 ≤ f := by omega
        · exact Or.inl (Or.inr (Or.inl (hL hcl)))
        · exact Or.inr (Or.inr (Or.inl (hL hcl)))
        · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (hL hcl)))))
        · exact absurd hgen
            (CFSG.GH74.Filter.t_PSL_even_unipotent S 2 f hcl (by simp; omega))
      · obtain rfl | rfl | hf3 : f = 1 ∨ f = 2 ∨ 3 ≤ f := by omega
        · exact Or.inr (Or.inl (Or.inr (hL hcl)))
        · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (hL hcl))))))
        · exact absurd hgen
            (CFSG.GH74.Filter.t_PSL_even_unipotent S 3 f hcl (by simp; omega))
      · obtain rfl | hf2 : f = 1 ∨ 2 ≤ f := by omega
        · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (hL hcl)))))))
        · exact absurd hgen
            (CFSG.GH74.Filter.t_PSL_even_unipotent S 4 f hcl (by simp; omega))
      · exact absurd hgen (CFSG.GH74.Filter.t_PSL_even_unipotent S 5 f hcl (by simp; omega))
      · exact absurd hgen
          (CFSG.GH74.Filter.t_PSL_even_unipotent S n f hcl
            (CFSG.GH74.Filter.unip_PSL_bound hn6 hf))
    ·
      obtain ⟨hp, hf, hn3, h32⟩ := hadm
      obtain rfl | rfl | hn5 : n = 3 ∨ n = 4 ∨ 5 ≤ n := by omega
      · have hf2 : 2 ≤ f := by
          by_contra h
          obtain rfl : f = 1 := by omega
          exact h32 (by norm_num)
        obtain rfl | hf3 : f = 2 ∨ 3 ≤ f := by omega
        · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (hLU hcl))))))))
        · exact absurd hgen (CFSG.GH74.Filter.t_PSU_even S 3 f hcl (by simp; omega))
      · obtain rfl | hf2 : f = 1 ∨ 2 ≤ f := by omega
        · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (hLU hcl))))))))
        · exact absurd hgen (CFSG.GH74.Filter.t_PSU_even S 4 f hcl (by omega))
      · exact absurd hgen
          (CFSG.GH74.Filter.t_PSU_even S n f hcl
            (le_trans (by norm_num) (Nat.mul_le_mul hf (show 3 ≤ n - 2 by omega))))
    ·
      obtain ⟨hp, hf, hn2, h22⟩ := hadm
      obtain rfl | rfl | hn4 : n = 2 ∨ n = 3 ∨ 4 ≤ n := by omega
      · have hf2 : 2 ≤ f := by
          by_contra h
          obtain rfl : f = 1 := by omega
          exact h22 (by norm_num)
        exact absurd hgen (CFSG.GH74.Filter.t_PSp_even_unipotent S 2 f hcl (by omega))
      · obtain rfl | hf2 : f = 1 ∨ 2 ≤ f := by omega
        · exact absurd hgen (CFSG.GH74.Filter.t_PSp_three_two S hcl)
        · exact absurd hgen (CFSG.GH74.Filter.t_PSp_even_unipotent S 3 f hcl (by omega))
      · exact absurd hgen (CFSG.GH74.Filter.t_PSp_even_unipotent S n f hcl (by nlinarith))
    ·
      obtain ⟨-, -, -, hp2⟩ := hadm
      exact absurd rfl hp2
    · exact absurd hgen (CFSG.GH74.Filter.t_POmegaPlus_even S n f hcl)
    · exact absurd hgen (CFSG.GH74.Filter.t_POmegaMinus_even S n f hcl)
  ·
    simp only [chevalleyExceptionalTags, Finset.mem_insert, Finset.mem_singleton] at ht
    rcases ht with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact absurd hgen (CFSG.GH74.Filter.t_G2_even S f hch)
    · exact absurd hgen (CFSG.GH74.Filter.t_F4_even S f hch)
    · exact absurd hgen (CFSG.GH74.Filter.t_E6_even S f hch)
    · exact absurd hgen (CFSG.GH74.Filter.t_E7_even S f hch)
    · exact absurd hgen (CFSG.GH74.Filter.t_E8_even S f hch)
    · exact absurd hgen (CFSG.GH74.Filter.t_2E6_even S f hch)
    · exact absurd hgen (CFSG.GH74.Filter.t_3D4_even S f hch)
  ·
    simp only [reeTitsTags, Finset.mem_insert, Finset.mem_singleton] at ht
    rcases ht with rfl | rfl | rfl
    · obtain ⟨-, -, -, hp3, -⟩ := hadm
      exact absurd hp3 (by norm_num)
    · exact absurd hgen (CFSG.GH74.Filter.t_twistedF4 S f hree)
    · obtain ⟨-, -, -, -, hf1⟩ := hadm
      subst hf1
      exact absurd hgen (CFSG.GH74.Filter.t_Tits S hree)
  ·
    have hsz' := hsz
    obtain ⟨-, a, ha, K, -, -, hfa, -⟩ := hsz'
    by_cases ha1 : a = 1
    · subst ha1
      obtain rfl : f = 3 := by omega
      exact Or.inr (Or.inr (Or.inr (Or.inl (CFSG.GH74.Filter.lieModel_of_suzuki hsz))))
    · exact absurd hgen (CFSG.GH74.Filter.t_suzuki_large S 2 f (by omega) hsz)

theorem even_lie_rank_le_three
    {S : Type} [Group S] [Finite S]
    (hs : IsSimpleGroup S)
    (hnab : ∃ a b : S, a * b ≠ b * a) (he : EvenLieType S) (h3 : SectionalTwoRankLE S 3) :
    ShapeA5 S ∨ ShapeL27 S ∨ ShapeL28 S ∨ ShapeSz8 S := by
  have h4 : SectionalTwoRankLE S 4 := SectionalTwoRankLE.mono (by norm_num) h3
  rcases even_lie_rank_le_four hs hnab he h4 with h | h | h | h | h | h | h | h | h
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr (Or.inl h))
  · exact Or.inr (Or.inr (Or.inr h))
  · exact absurd h3 (rank3_L2_16 h).not_sectionalTwoRankLE
  · exact absurd h3 (rank3_L3_4 h).not_sectionalTwoRankLE
  · exact absurd h3 (rank3_L4_2 h).not_sectionalTwoRankLE
  · exact absurd h3 (rank3_U3_4 h).not_sectionalTwoRankLE
  · exact absurd h3 (rank3_U4_2 h).not_sectionalTwoRankLE

end CFSG.GH74.E2

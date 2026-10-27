module

public import CFSG.HardMathSupport.Dickson.I271.SporGenR3Aux.TabMThreeADefs
public import CFSG.HardMathSupport.Dickson.I271.SporGenR3Aux.TabMThreeAFi24

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.HardMathSupport.Dickson.I271.TabMThreeA

open CFSG.Monster CFSG.Monster.Generated CFSG.Monster.Griess CFSG.Monster.GMS
  CFSG.Monster.Existence CFSG.YGroups CFSG.YGroups.Y443 CFSG.Open
open CFSG.Certificates.CosetEnumeration (evalWord evalWord_nil evalWord_cons evalWord_append)

section TwoB


theorem exists_twoB_mem_range_yMc (hG : Gmat = AutO) (h : (yMc hG).ker ≤ yJ.ker) :
    ∃ t ∈ (yMc hG).range, t * tGriess = tGriess * t ∧ IsConj xGriess t := by
  have key : ∀ u : List ℕ, u ∈ yMoves → ∀ (hl : u.length % 2 = 0) (hw : ∀ c ∈ u, c < 11),
      evalWord (refT hG) u ≠ 1 := by
    intro u hu hl hw hone
    have hker : yWordC u hl hw ∈ (yMc hG).ker := by
      rw [MonoidHom.mem_ker, yMc_yWordC, yM_evalWord hG u hw]
      exact hone
    have h1 := (yJ_eq_one_iff _).1 (MonoidHom.mem_ker.1 (h hker))
    rw [coe_yWordC] at h1
    exact yKM_yMoves hu h1
  have hne : ∀ u ∈ ([[2, 6], [2, 8], [2, 10], [6, 8], [6, 10], [8, 10], [2, 6, 8, 10]] :
      List (List ℕ)), evalWord (refT hG) u ≠ 1 := by
    intro u hu
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
    rcases hu with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      exact key _ (by simp [yMoves]) (by decide) (by decide)
  obtain ⟨t, ht, hB⟩ := exists_twoB_refT hG hne
  have hgen : ∀ a b : ℕ, a < 11 → b < 11 → refT hG a * refT hG b ∈ (yMc hG).range := by
    intro a b ha hb
    refine ⟨⟨yGen 4 4 2 a * yGen 4 4 2 b, yGen_mul_yGen_mem_commutator ha hb⟩, ?_⟩
    show yM hG (yGen 4 4 2 a * yGen 4 4 2 b) = refT hG a * refT hG b
    rw [map_mul, yM_yGen hG ha, yM_yGen hG hb]
  have hcomm : ∀ a b : ℕ, a < 12 → b < 12 → a ≠ 4 → b ≠ 4 →
      refT hG a * refT hG b ∈ Subgroup.centralizer ({tGriess} : Set MGriess) := by
    intro a b ha hb ha4 hb4
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact (Commute.mul_left (tGriess_mul_refT hG ha ha4).symm
      (tGriess_mul_refT hG hb hb4).symm).eq
  have hrange : Subgroup.closure ({refT hG 2 * refT hG 6, refT hG 2 * refT hG 8,
      refT hG 2 * refT hG 10} : Set MGriess) ≤ (yMc hG).range := by
    rw [Subgroup.closure_le]
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl | rfl
    · exact hgen 2 6 (by norm_num) (by norm_num)
    · exact hgen 2 8 (by norm_num) (by norm_num)
    · exact hgen 2 10 (by norm_num) (by norm_num)
  have hcent : Subgroup.closure ({refT hG 2 * refT hG 6, refT hG 2 * refT hG 8,
      refT hG 2 * refT hG 10} : Set MGriess) ≤ Subgroup.centralizer ({tGriess} : Set MGriess) := by
    rw [Subgroup.closure_le]
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl | rfl
    · exact hcomm 2 6 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    · exact hcomm 2 8 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    · exact hcomm 2 10 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨t, hrange ht, Subgroup.mem_centralizer_singleton_iff.1 (hcent ht), hB⟩

end TwoB

end CFSG.HardMathSupport.Dickson.I271.TabMThreeA

module

public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Fi23SylowBase
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge

public section

namespace CFSG.EvenSporadicStandard.Induction.Fi

open CFSG.Sporadic.Fi23 CFSG.Sporadic.Th.Native CFSG.Perm CFSG.Perm.Native CFSG.HardMathSupport.Foote.E27
open CFSG.Sporadic.Th hiding J a b closure_ab gA gB rows_B_cube
open CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Fi23Sylow (eq_of_base)

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

section Chain

theorem mem_lvl_two_iff {g : CFSG.Sporadic.Fi23.J} :
    g ∈ lvl 2 ↔ g * CFSG.Sporadic.Fi23.d = CFSG.Sporadic.Fi23.d * g ∧
      g * CFSG.Sporadic.Fi23.d1 = CFSG.Sporadic.Fi23.d1 * g := by
  have h1 : ∀ g : CFSG.Sporadic.Fi23.J, g ∈ lvl 1 ↔ g * CFSG.Sporadic.Fi23.d =
      CFSG.Sporadic.Fi23.d * g := fun g => by
    rw [← lvl_one_iff, CFSG.Sporadic.Fi23.idx_eq_iff (by norm_num) (by norm_num), conjPt_zero,
      mul_inv_eq_iff_eq_mul]
  constructor
  · intro hg
    have hg1 : g ∈ lvl 1 := levelGroup_anti (pairG gs) (by norm_num : 1 ≤ 2) hg
    refine ⟨(h1 g).1 hg1, ?_⟩
    have h := (chain_facts'.2.1 1 (by rw [chainBase_size]; norm_num) g hg1).2 hg
    rw [chainBase_one, CFSG.Sporadic.Fi23.idx_eq_iff (by norm_num) (by norm_num), mul_inv_eq_iff_eq_mul] at h
    exact h
  · rintro ⟨hd, hd1⟩
    have hg1 : g ∈ lvl 1 := (h1 g).2 hd
    refine (chain_facts'.2.1 1 (by rw [chainBase_size]; norm_num) g hg1).1 ?_
    rw [chainBase_one, CFSG.Sporadic.Fi23.idx_eq_iff (by norm_num) (by norm_num), mul_inv_eq_iff_eq_mul]
    exact hd1

theorem card_lvl_two : Nat.card (lvl 2) = 36787322880 := by
  rw [chain_facts'.2.2 2 (by rw [chainBase_size]; norm_num), chainBase_size]
  have hs : ∀ l ∈ Finset.Ico 2 6, trees[l]!.pts.size =
      [31671, 3510, 25344, 288, 1260, 4].getD l 0 := fun l hl =>
    tree_size_of (by obtain ⟨h1, h2⟩ := Finset.mem_Ico.mp hl; interval_cases l <;> rfl)
  rw [Finset.prod_congr rfl hs]
  decide

theorem d_mem_lvl_two : CFSG.Sporadic.Fi23.d ∈ lvl 2 :=
  mem_lvl_two_iff.2 ⟨rfl, d1_commute.symm⟩

theorem d1_mem_lvl_two : CFSG.Sporadic.Fi23.d1 ∈ lvl 2 :=
  mem_lvl_two_iff.2 ⟨d1_commute, rfl⟩

end Chain

end CFSG.EvenSporadicStandard.Induction.Fi

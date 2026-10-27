module

public import CFSG.ClassicalGroups.Unitary.SUnThreeLocalRoot

public section

namespace CFSG.ClassicalGroups.SUnThreeLocal

open Matrix CFSG.Open CFSG.LieType.Universal.Unitary

variable {L : Type} [Field L] {n : ℕ} {σ : L ≃+* L}
variable [Finite L] {r : ℕ} [Fact r.Prime] [CharP L r]

theorem two_le_pRank_centralizer_c₀_weight_one (hσ : ∀ c, σ (σ c) = c)
    (htr : ∃ c : L, c ≠ 0 ∧ σ c = -c) (ζ : FixedCubeRoot σ) (hn : n = 6 ∨ n = 7) :
    2 ≤ pRank r (Subgroup.centralizer
      ({c₀ ζ hn (Multiplicative.ofAdd ![1, 0, 0])} : Set (SU σ n))) := by
  obtain ⟨c, hc0, hcσ⟩ := htr
  have hc : c + σ c = 0 := by rw [hcσ]; ring
  refine two_le_pRank_of_mulVec (r := r) (x := longPos hn 1 c hc) (y := longPos hn 2 c hc)
    (w := Pi.single (Fin.rev (pos hn 2)) 1) ?_ ?_ (orderOf_longPos hn 1 hc hc0)
    (orderOf_longPos hn 2 hc hc0) (commute_longPos_longPos hn 1 2 c c hc hc)
    (longPos_mulVec_single_rev_pos_of_ne hn (by decide) c hc)
    (longPos_mulVec_single_rev_pos_ne hn 2 hc hc0)
  · rw [Subgroup.mem_centralizer_singleton_iff]
    exact (commute_c₀_longPos ζ hn 1 c hc _ (by simp)).eq
  · rw [Subgroup.mem_centralizer_singleton_iff]
    exact (commute_c₀_longPos ζ hn 2 c hc _ (by simp)).eq

theorem two_le_pRank_centralizer_c₀_weight_two (hσ : ∀ c, σ (σ c) = c)
    (htr : ∃ c : L, c ≠ 0 ∧ σ c = -c) (ζ : FixedCubeRoot σ) (hn : n = 6 ∨ n = 7) :
    2 ≤ pRank r (Subgroup.centralizer
      ({c₀ ζ hn (Multiplicative.ofAdd ![1, 1, 0])} : Set (SU σ n))) := by
  obtain ⟨c, hc0, hcσ⟩ := htr
  have hc : c + σ c = 0 := by rw [hcσ]; ring
  have h01 : (0 : Fin 3) ≠ 1 := by decide
  refine two_le_pRank_of_mulVec (r := r) (x := longPos hn 2 c hc)
    (y := rootPos hσ hn h01 c) (w := Pi.single (pos hn 1) 1) ?_ ?_
    (orderOf_longPos hn 2 hc hc0) (orderOf_rootPos hσ hn h01 hc0)
    (commute_rootPos_longPos hσ hn h01 2 (by decide) c c hc).symm
    (longPos_mulVec_single_pos hn 2 1 c hc) (rootPos_mulVec_single_pos_ne hσ hn h01 hc0)
  · rw [Subgroup.mem_centralizer_singleton_iff]
    exact (commute_c₀_longPos ζ hn 2 c hc _ (by simp)).eq
  · rw [Subgroup.mem_centralizer_singleton_iff]
    exact (commute_c₀_rootPos hσ ζ hn h01 c _ (by simp)).eq

theorem two_le_pRank_centralizer_c₀_weight_three (hσ : ∀ c, σ (σ c) = c)
    (htr : ∃ c : L, c ≠ 0 ∧ σ c = -c) (ζ : FixedCubeRoot σ) (hn : n = 6 ∨ n = 7) :
    2 ≤ pRank r (Subgroup.centralizer
      ({c₀ ζ hn (Multiplicative.ofAdd ![1, 1, 1])} : Set (SU σ n))) := by
  obtain ⟨c, hc0, -⟩ := htr
  have h01 : (0 : Fin 3) ≠ 1 := by decide
  have h02 : (0 : Fin 3) ≠ 2 := by decide
  refine two_le_pRank_of_mulVec (r := r) (x := rootPos hσ hn h02 c) (y := rootPos hσ hn h01 c)
    (w := Pi.single (pos hn 1) 1) ?_ ?_ (orderOf_rootPos hσ hn h02 hc0)
    (orderOf_rootPos hσ hn h01 hc0)
    (commute_rootPos_rootPos hσ hn h02 h01 (by decide) (by decide) c c)
    (rootPos_mulVec_single_pos_of_ne hσ hn h02 (by decide) c)
    (rootPos_mulVec_single_pos_ne hσ hn h01 hc0)
  · rw [Subgroup.mem_centralizer_singleton_iff]
    exact (commute_c₀_rootPos hσ ζ hn h02 c _ (by simp)).eq
  · rw [Subgroup.mem_centralizer_singleton_iff]
    exact (commute_c₀_rootPos hσ ζ hn h01 c _ (by simp)).eq

theorem one_le_pRank_centralizer_c₀_plane_a (hσ : ∀ c, σ (σ c) = c)
    (htr : ∃ c : L, c ≠ 0 ∧ σ c = -c) (ζ : FixedCubeRoot σ) (hn : n = 6 ∨ n = 7) :
    1 ≤ pRank r (Subgroup.centralizer
      ({c₀ ζ hn (Multiplicative.ofAdd ![1, 0, 0]), c₀ ζ hn (Multiplicative.ofAdd ![0, 1, 0])} :
        Set (SU σ n))) := by
  obtain ⟨c, hc0, hcσ⟩ := htr
  have hc : c + σ c = 0 := by rw [hcσ]; ring
  refine one_le_pRank_of_orderOf (x := longPos hn 2 c hc) ?_ (orderOf_longPos hn 2 hc hc0)
  rw [Subgroup.mem_centralizer_iff]
  intro h hh
  rcases hh with rfl | hh
  · exact (commute_c₀_longPos ζ hn 2 c hc _ (by simp)).symm.eq
  · rw [Set.mem_singleton_iff] at hh
    subst hh
    exact (commute_c₀_longPos ζ hn 2 c hc _ (by simp)).symm.eq

theorem one_le_pRank_centralizer_c₀_plane_b (hσ : ∀ c, σ (σ c) = c)
    (htr : ∃ c : L, c ≠ 0 ∧ σ c = -c) (ζ : FixedCubeRoot σ) (hn : n = 6 ∨ n = 7) :
    1 ≤ pRank r (Subgroup.centralizer
      ({c₀ ζ hn (Multiplicative.ofAdd ![1, 1, 1]), c₀ ζ hn (Multiplicative.ofAdd ![0, 0, 1])} :
        Set (SU σ n))) := by
  obtain ⟨c, hc0, -⟩ := htr
  have h01 : (0 : Fin 3) ≠ 1 := by decide
  refine one_le_pRank_of_orderOf (x := rootPos hσ hn h01 c) ?_ (orderOf_rootPos hσ hn h01 hc0)
  rw [Subgroup.mem_centralizer_iff]
  intro h hh
  rcases hh with rfl | hh
  · exact (commute_c₀_rootPos hσ ζ hn h01 c _ (by simp)).symm.eq
  · rw [Set.mem_singleton_iff] at hh
    subst hh
    exact (commute_c₀_rootPos hσ ζ hn h01 c _ (by simp)).symm.eq

end CFSG.ClassicalGroups.SUnThreeLocal

module

public import CFSG.HardMathSupport.Solomon.Coordinator.McLTypeFactsSmall
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.LinearAlgebra.LinearGroups.ProjectiveSimple

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator

theorem mcltf_center_SL_zmod2 {n : ℕ} (hn : 1 ≤ n) :
    Subgroup.center (Matrix.SpecialLinearGroup (Fin n) (ZMod 2)) = ⊥ := by
  rw [eq_bot_iff]
  intro A hA
  obtain ⟨r, hr, hrA⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp hA
  rw [Fintype.card_fin] at hr
  have hr1 : r = 1 := by
    have h01 : ∀ a : ZMod 2, a = 0 ∨ a = 1 := by decide
    rcases h01 r with rfl | rfl
    · rw [zero_pow (by omega)] at hr
      exact absurd hr zero_ne_one
    · rfl
  rw [Subgroup.mem_bot]
  ext i j
  rw [← hrA, hr1, map_one]
  rfl

theorem mcltf_isSimpleGroup_SL {n : ℕ} (hn : 3 ≤ n) :
    IsSimpleGroup (Matrix.SpecialLinearGroup (Fin n) (ZMod 2)) := by
  obtain ⟨-, hsimple, -⟩ := CFSG.LinearGroups.linear_projective_simple (K := ZMod 2) (n := n)
    (by omega) (Or.inl hn)
  exact ((QuotientGroup.quotientMulEquivOfEq (mcltf_center_SL_zmod2 (by omega))).trans
    QuotientGroup.quotientBot).symm.isSimpleGroup

theorem mcltf_facts_SL {n : ℕ} (hn : 3 ≤ n) :
    mcltf_Facts (Matrix.SpecialLinearGroup (Fin n) (ZMod 2)) := by
  have := mcltf_isSimpleGroup_SL hn
  exact mcltf_facts_of_simple (mcltf_exists_ne_of_perfect
    (CFSG.LinearGroups.special_linear_dimension_at_least_three_perfect hn).commutator_eq_top)

@[expose] noncomputable def mcltf_SLEquiv (n : ℕ) :
    Matrix.SpecialLinearGroup (Fin n) (ZMod 2) ≃* ↥(CFSG.Open.StatedSL n (ZMod 2)) :=
  (CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL n (ZMod 2)).trans
    (MulEquiv.subgroupCongr rfl)

theorem mcltf_facts_statedSL {n : ℕ} (hn : 2 ≤ n) :
    mcltf_Facts ↥(CFSG.Open.StatedSL n (ZMod 2)) := by
  rcases Nat.lt_or_ge n 3 with h | h
  · obtain rfl : n = 2 := by omega
    exact mcltf_facts_of_mulEquiv (mcltf_SLEquiv 2).symm mcltf_facts_SL22
  · exact mcltf_facts_of_mulEquiv (mcltf_SLEquiv n).symm (mcltf_facts_SL h)

end CFSG.HardMathSupport.Solomon.Coordinator

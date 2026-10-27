module

public import CFSG.GF2Type.Aschbacher1976HigherCenter.Setup

public section

namespace CFSG.GF2Type.Aschbacher1976HigherCenter

open Subgroup CFSG CFSG.Open

theorem exists_layer
    {G : Type} [Group G] [Finite G] {M B Q : Subgroup G} {z : G} {D : Subgroup Q} {k u : ℕ}
    (h : Setup M B Q z D k u) :
    ∃ P : Subgroup G, P ≤ Q ∧ (∀ x ∈ P, x ^ 4 = 1) ∧ M ≤ normalizer (P : Set G) ∧
      M ⊓ centralizer (P : Set G) ≤ critCenter D := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hk3 := h.three_le
  have hcc := (CFSG.LocalAnalysis.GorensteinLyons.gf2_critical_center_and_exponent_four_reduction
    h.charTwoType (by have := h.oddRank; omega) h.maxLocal h.symplectic h.bmax h.bmax_le
    h.core_eq h.central h.involution (r := GLATwoLocalRank 3 G) rfl).2 D h.critical _ rfl _ rfl
  obtain ⟨-, -, hYcyc, -⟩ := hcc
  obtain ⟨y₀, hy₀⟩ := hYcyc.exists_generator
  have hy₀o : orderOf (y₀ : Q) = 2 ^ k := by
    rw [Subgroup.orderOf_coe, orderOf_eq_card_of_forall_mem_zpowers hy₀, h.center_card]
  have hdvd : 2 ^ (k - 2) ∣ orderOf (y₀ : Q) := hy₀o ▸ pow_dvd_pow 2 (by omega)
  have hTY : zpowers ((y₀ : Q) ^ 2 ^ (k - 2)) ≤ (center D).map D.subtype :=
    zpowers_le.2 (pow_mem y₀.2 _)
  have hT4 : Nat.card (zpowers ((y₀ : Q) ^ 2 ^ (k - 2))) = 4 := by
    rw [Nat.card_zpowers, orderOf_pow_of_dvd (by positivity) hdvd, hy₀o,
      Nat.pow_div (by omega) (by norm_num), show k - (k - 2) = 2 by omega]
  obtain ⟨-, -, ⟨L, hLset, -, hMNL, -, hMcL⟩, -⟩ :=
    CFSG.LocalAnalysis.GorensteinLyons.gf2_higher_center_residual_presentations_and_fusion
      h.charTwoType h.oddRank h.maxLocal h.symplectic h.bmax h.bmax_le h.core_eq h.central
      h.involution (r := GLATwoLocalRank 3 G) rfl h.critical rfl h.three_le h.center_card hTY hT4
  refine ⟨L.map Q.subtype, map_subtype_le _, ?_, hMNL, hMcL.le⟩
  rintro _ ⟨l, hl, rfl⟩
  have hl' : l ∈ ({d | d ∈ D ∧ d ^ 4 = 1} : Set Q) := hLset ▸ hl
  have hl4 : l ^ 4 = 1 := hl'.2
  simpa using congrArg Subtype.val hl4

end CFSG.GF2Type.Aschbacher1976HigherCenter

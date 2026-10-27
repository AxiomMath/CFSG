module

public import CFSG.GH74.Uniqueness.SU.SU0Even
public import CFSG.GH74.GLS.UniquenessBridge
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

namespace CFSG.GH74.GLS

open Subgroup Blueprint Assembly.LowTwoRank

@[expose] def S_SUS_KGH : Prop :=
  ∀ (G : Type) [Group G] [Finite G], IsSimpleGroup G → (∃ a b : G, a * b ≠ b * a) → KGH G →
    IsLB2Type G → HasTwoUniquenessSubgroup G →
      LieModel G .PSL 2 2 2 ∨ LieModel G .PSU 3 2 2 ∨ NativeSporadic.IsSporadic G .J1

theorem lieModel_psl_two_two_two_of_mulEquiv {G : Type} [Group G]
    (e : G ≃* Theory.Comparator.PSL2Model 2) : LieModel G .PSL 2 2 2 := by
  refine Or.inl ⟨by decide, ⟨Nat.prime_two, by norm_num, le_rfl, ?_, ?_⟩,
    GaloisField 2 2, inferInstance, inferInstance, GaloisField.card 2 2 (by norm_num),
    ⟨e.trans (projectiveSpecialLinearGroupEquivStatedProj 2 (GaloisField 2 2))⟩⟩
  · decide
  · decide

theorem lieModel_psu_three_two_two_of_mulEquiv {G : Type} [Group G]
    (e : G ≃* Theory.Comparator.PSU3Model 2) : LieModel G .PSU 3 2 2 :=
  Or.inl ⟨by decide, (RankTwoShapes.statedClassicalModel_PSU_three_two_iff G 2 le_rfl).mpr ⟨e⟩⟩

theorem S_SUS_KGH_of_S_SU (hSU : Uniqueness.S_SU) : S_SUS_KGH := by
  intro G _ _ hs hnonab hK hLB hU
  obtain ⟨M, hM⟩ := hU
  rcases hSU G hs hnonab hK ⟨M, (isTwoUniquenessSubgroup_iff M).mp hM⟩ with hJ | hB
  · exact Or.inr (Or.inr hJ)
  · obtain ⟨n, i, e, hBT⟩ := Uniqueness.Bender.isBenderGroup_iff_exists_benderType.mp hB
    by_cases hn : 3 ≤ n
    · exact absurd hLB (Uniqueness.SU.SU0.not_isLB2Type_of_benderType hBT hn)
    · cases hBT with
      | linear _ hn' e' =>
        obtain rfl : n = 2 := by omega
        exact Or.inl (lieModel_psl_two_two_two_of_mulEquiv e')
      | suzuki a ha e' => omega
      | unitary _ hn' e' =>
        obtain rfl : n = 2 := by omega
        exact Or.inr (Or.inl (lieModel_psu_three_two_two_of_mulEquiv e'))

end CFSG.GH74.GLS

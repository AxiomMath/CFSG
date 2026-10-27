module

public import CFSG.GF2Type.AschbacherFSmith1977Holds

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.GF2Type.Smith1979W3

open CFSG CFSG.Blueprint CFSG.Open CFSG.LargeExtraspecial CFSG.LargeExtraspecial.Bridge

@[expose] def NotWeaklyClosed {G : Type} [Group G] (S : Setting G) : Prop :=
  ∃ g : G, g * S.z * g⁻¹ ∈ S.QG ∧ g * S.z * g⁻¹ ≠ S.z

@[expose] def IrreducibleNoA2WidthThree : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (S : Setting G),
    S.width = 3 → NotWeaklyClosed S → ¬ S.IsReducible → S11.NoA2All S → False

theorem widthThree_of_leaves_at (h77 : AschbacherFSmith1977Statement) {G : Type} [Group G]
    [Finite G] [IsSimpleGroup G] (hnonab : ∃ a b : G, a * b ≠ b * a) {z : G}
    (hz : orderOf z = 2)
    (hext : IsExtraspecialPGroup 2
      (inSubgroup generalizedFitting (Subgroup.centralizer ({z} : Set G))))
    (hcard : Nat.card (inSubgroup generalizedFitting (Subgroup.centralizer ({z} : Set G))) =
      2 ^ (1 + 2 * 3))
    (hB : ∀ S : Setting G, S.width = 3 → NotWeaklyClosed S → S.IsReducible →
      LieModel G .PSL 5 2 1 ∨ NativeSporadic.IsSporadic G .M24 ∨
        NativeSporadic.IsSporadic G .He)
    (hC : ∀ S : Setting G, S.width = 3 → ¬ S.IsReducible →
      (∃ g : G, g * S.z * g⁻¹ ∈ S.QG ∧ g * S.z * g⁻¹ ≠ S.z ∧ S.HasTypeAInL g) →
        NativeSporadic.IsSporadic G .Suz)
    (hD : ∀ S : Setting G, S.width = 3 → NotWeaklyClosed S → ¬ S.IsReducible →
      S11.NoA2All S → False) :
    LieModel G .PSL 5 2 1 ∨ LieModel G .PSU 5 2 1 ∨ NativeSporadic.IsSporadic G .M24 ∨
      NativeSporadic.IsSporadic G .He ∨ NativeSporadic.IsSporadic G .Suz := by
  by_cases hwc : ∀ g : G, g⁻¹ * z * g ∈
      inSubgroup generalizedFitting (Subgroup.centralizer ({z} : Set G)) → g⁻¹ * z * g = z
  · rcases h77 G hnonab z hz hext 3 hcard le_rfl hwc with hU | ⟨h4, -⟩
    · exact Or.inr (Or.inl hU)
    · exact absurd h4 (by norm_num)
  · obtain ⟨hext', hcard'⟩ := timmesfeld_hypotheses hext hcard
    obtain ⟨S, hSz, hSQ, hSw⟩ : ∃ S : Setting G, S.z = z ∧
        S.QG = inSubgroup generalizedFitting (Subgroup.centralizer ({z} : Set G)) ∧
          S.width = 3 :=
      ⟨Setting.ofFStar z hz hext', Setting.ofFStar_z z hz hext', ofFStar_QG hz hext',
        width_ofFStar hz hext' hcard'⟩
    have hnwc : NotWeaklyClosed S := by
      push_neg at hwc
      obtain ⟨g, hg, hne⟩ := hwc
      refine ⟨g⁻¹, ?_, ?_⟩
      · rw [hSz, hSQ, inv_inv]
        exact hg
      · rw [hSz, inv_inv]
        exact hne
    by_cases hred : S.IsReducible
    · rcases hB S hSw hnwc hred with h | h | h
      · exact Or.inl h
      · exact Or.inr (Or.inr (Or.inl h))
      · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
    · by_cases ha : ∃ g : G, g * S.z * g⁻¹ ∈ S.QG ∧ g * S.z * g⁻¹ ≠ S.z ∧ S.HasTypeAInL g
      · exact Or.inr (Or.inr (Or.inr (Or.inr (hC S hSw hred ha))))
      · exact (hD S hSw hnwc hred fun g h1 h2 h3 => ha ⟨g, h1, h2, h3⟩).elim

end CFSG.GF2Type.Smith1979W3

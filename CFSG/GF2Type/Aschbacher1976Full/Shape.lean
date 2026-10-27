module

public import CFSG.GF2Type.Aschbacher1976Full.ShapeCyclicCore
public import CFSG.GF2Type.Aschbacher1976Full.ShapeBigCenter2

public section

namespace CFSG.GF2Type.Aschbacher1976Full

open CFSG CFSG.Blueprint CFSG.SectionRank.Ccomm Subgroup Shape

theorem shapeBigZ :
    ∀ (G : Type) [Group G] [Finite G] (z : G), Asc76Setting G z →
      ∀ D : Subgroup ↥(Fz z), ThompsonCritical D →
        (∀ D' : Subgroup ↥(Fz z), ThompsonCritical D' → Nat.card D' ≤ Nat.card D) →
        8 ≤ Nat.card (Zof D) → Asc76Shape z := by
  intro G _ _ z hS D hD hmax hk8
  obtain ⟨-, -, hz, hsymp⟩ := hS
  haveI := nontrivial_Fz hz
  obtain ⟨E, R, zz, cd⟩ := exists_critData hsymp.1 hsymp.2 hD
  have hzz : zF z = zz := cd.center_uniq _ (zF_mem_center z) ((orderOf_zF z).trans hz)
  rcases cd.cases with ⟨hE, -⟩ | ⟨w, hw, -, hEcard, hER, -⟩
  · exact shape_cyclic_core hsymp cd hmax hk8 hE
  · exact shape_big_center hsymp cd hzz.symm hmax hk8 hw hEcard hER

theorem asc76ShapeHolds_of_bigZ : Asc76ShapeHolds := by
  have h := shapeBigZ
  intro G _ _ z hS
  have hS' := hS
  obtain ⟨-, -, hz, hsymp⟩ := hS'
  haveI := nontrivial_Fz hz
  obtain ⟨D, hD, hmax⟩ := exists_max_critical hsymp.1
  by_cases hk : Nat.card (Zof D) ≤ 4
  · exact shape_small hz hsymp hD hk
  · obtain ⟨k, hk2⟩ := IsPGroup.iff_card.mp (hsymp.1.to_subgroup (Zof D))
    have hk8 : 8 ≤ Nat.card (Zof D) := by
      rw [hk2] at hk ⊢
      have hk3 : 3 ≤ k := by
        by_contra hlt
        exact hk (by calc 2 ^ k ≤ 2 ^ 2 := Nat.pow_le_pow_right (by norm_num) (by omega)
          _ = 4 := by norm_num)
      calc 8 = 2 ^ 3 := by norm_num
        _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk3
    exact h G z hS D hD hmax hk8

theorem asc76ShapeHolds : Asc76ShapeHolds := asc76ShapeHolds_of_bigZ

end CFSG.GF2Type.Aschbacher1976Full

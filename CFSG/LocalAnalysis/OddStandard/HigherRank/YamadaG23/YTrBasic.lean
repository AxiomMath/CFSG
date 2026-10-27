module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.YSetBasic

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

open Subgroup CFSG.Open CFSG.OddStandard.HigherRank.G2Three
  CFSG.OddStandard.HigherRank.G2Three.Sec1

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} (s : Setting3 G L)

theorem s3_isPGroup_S : IsPGroup 2 ↥s.fr.S := s.sylow_S.2.1

theorem s3_isPGroup_of_le {X : Subgroup G} (hX : X ≤ s.fr.S) : IsPGroup 2 ↥X :=
  (s3_isPGroup_S s).of_injective (Subgroup.inclusion hX) (Subgroup.inclusion_injective hX)

theorem s3_isPGroup_zpowers {x : G} (hx : x ∈ s.fr.S) : IsPGroup 2 ↥(zpowers x) :=
  s3_isPGroup_of_le s (by rwa [zpowers_le])

theorem s3_a₁_mem_S : s.fr.a₁ ∈ s.fr.S := subset_closure (by simp)

theorem s3_b₁_mem_S : s.fr.b₁ ∈ s.fr.S := subset_closure (by simp)

theorem s3_a₂_mem_S : s.fr.a₂ ∈ s.fr.S := subset_closure (by simp)

theorem s3_b₂_mem_S : s.fr.b₂ ∈ s.fr.S := subset_closure (by simp)

theorem s3_h₀_mem_S : s.fr.h₀ ∈ s.fr.S := subset_closure (by simp)

theorem s3_z_mem_S : s.fr.z ∈ s.fr.S := pow_mem (s3_b₁_mem_S s) 2

theorem s3_a₁_mem_A : s.fr.a₁ ∈ s.fr.A := subset_closure (by simp)

theorem s3_b₁_mem_A : s.fr.b₁ ∈ s.fr.A := subset_closure (by simp)

theorem s3_a₂_mem_A : s.fr.a₂ ∈ s.fr.A := subset_closure (by simp)

theorem s3_b₂_mem_A : s.fr.b₂ ∈ s.fr.A := subset_closure (by simp)

theorem s3_Z_le_A : s.fr.Z ≤ s.fr.A := by
  rw [SFrame.Z, zpowers_le]
  exact s3_z_mem_A s

theorem s3_B_le_S : s.fr.B ≤ s.fr.S := inf_le_left

theorem s3_cenB_le_B : cen s.fr.B ≤ s.fr.B := inf_le_left

theorem s3_J0B_le_B : thompsonSubgroup s.fr.B ≤ s.fr.B :=
  CFSG.ambientMaxCardThompson_le _

theorem s3_E_le_A : s.fr.E ≤ s.fr.A := by
  rw [SFrame.E, closure_le]
  intro x hx
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
  rcases hx with rfl | rfl | rfl
  · exact mul_mem (s3_b₁_mem_A s) (s3_b₂_mem_A s)
  · exact mul_mem (mul_mem (s3_a₁_mem_A s) (s3_b₁_mem_A s)) (s3_a₂_mem_A s)
  · exact s3_z_mem_A s

theorem s3_F_le_A : s.fr.F ≤ s.fr.A := by
  rw [SFrame.F, closure_le]
  intro x hx
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
  rcases hx with rfl | rfl | rfl
  · exact mul_mem (s3_a₁_mem_A s) (s3_a₂_mem_A s)
  · exact mul_mem (s3_b₁_mem_A s) (s3_b₂_mem_A s)
  · exact s3_z_mem_A s

theorem s3_K1_le_A : closure {s.fr.a₁, s.fr.b₁} ≤ s.fr.A := by
  rw [closure_le]
  intro x hx
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
  rcases hx with rfl | rfl
  · exact s3_a₁_mem_A s
  · exact s3_b₁_mem_A s

theorem s3_K2_le_A : closure {s.fr.a₂, s.fr.b₂} ≤ s.fr.A := by
  rw [closure_le]
  intro x hx
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
  rcases hx with rfl | rfl
  · exact s3_a₂_mem_A s
  · exact s3_b₂_mem_A s

theorem s3_Z_le_E : s.fr.Z ≤ s.fr.E := by
  rw [SFrame.Z, zpowers_le]
  exact subset_closure (by simp)

theorem s3_Z_le_F : s.fr.Z ≤ s.fr.F := by
  rw [SFrame.Z, zpowers_le]
  exact subset_closure (by simp)

theorem s3_a₁b₁b₂_mem_S : s.fr.a₁ * s.fr.b₁ * s.fr.b₂ ∈ s.fr.S :=
  mul_mem (mul_mem (s3_a₁_mem_S s) (s3_b₁_mem_S s)) (s3_b₂_mem_S s)

end CFSG.OddStandard.HigherRank.YamadaG23

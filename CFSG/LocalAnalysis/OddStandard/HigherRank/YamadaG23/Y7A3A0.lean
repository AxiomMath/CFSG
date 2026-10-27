module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y6Set5
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y4GCentA

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

open Subgroup CFSG.Open CFSG.OddStandard.HigherRank.G2Three
  CFSG.OddStandard.HigherRank.G2Three.Sec1
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

private lemma y7a_mem_zpowers_eq_one_or_self {z v : G} (hz2 : z ^ 2 = 1)
    (hv : v ∈ zpowers z) : v = 1 ∨ v = z := by
  obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp hv
  have h2 : z ^ (2 : ℤ) = 1 := by simpa using hz2
  rw [zpow_eq_zpow_emod m h2]
  rcases Int.emod_two_eq_zero_or_one m with h | h
  · left; rw [h]; simp
  · right; rw [h]; simp

theorem y7a_exists_a0 (c : Ctx7 G L) (hH : F33Hyp c.s c.e) {x : G}
    (hc : ∀ a ∈ c.s.fr.A, ⁅a, x⁆ ∈ zpowers c.s.fr.z) :
    ∃ a₀ ∈ c.s.fr.A, a₀⁻¹ * x ∈ centralizer (c.s.fr.A : Set G) := by
  classical
  have cfg := c.toCtx5.y6cfg5 hH
  have hcomm_gen : ∀ g ∈ c.s.fr.A, ⁅x, g⁆ = 1 ∨ ⁅x, g⁆ = c.s.fr.z := by
    intro g hgA
    have hxgz : ⁅x, g⁆ ∈ zpowers c.s.fr.z := by
      have hmem := Subgroup.inv_mem _ (hc g hgA)
      rwa [commutatorElement_inv] at hmem
    exact y7a_mem_zpowers_eq_one_or_self cfg.rel.z_sq hxgz
  have hz_cent : ∀ a ∈ (closure {c.s.fr.a₁, c.s.fr.b₁, c.s.fr.a₂, c.s.fr.b₂} : Subgroup G),
      a * c.s.fr.z = c.s.fr.z * a := y6q8_z_central cfg.rel
  have hza₁ : ⁅c.s.fr.z, c.s.fr.a₁⁆ = 1 :=
    commutatorElement_eq_one_iff_mul_comm.mpr
      (hz_cent c.s.fr.a₁ (Subgroup.subset_closure (by simp))).symm
  have hzb₁ : ⁅c.s.fr.z, c.s.fr.b₁⁆ = 1 :=
    commutatorElement_eq_one_iff_mul_comm.mpr
      (hz_cent c.s.fr.b₁ (Subgroup.subset_closure (by simp))).symm
  have hza₂ : ⁅c.s.fr.z, c.s.fr.a₂⁆ = 1 :=
    commutatorElement_eq_one_iff_mul_comm.mpr
      (hz_cent c.s.fr.a₂ (Subgroup.subset_closure (by simp))).symm
  have hzb₂ : ⁅c.s.fr.z, c.s.fr.b₂⁆ = 1 :=
    commutatorElement_eq_one_iff_mul_comm.mpr
      (hz_cent c.s.fr.b₂ (Subgroup.subset_closure (by simp))).symm
  have hy : ∀ a ∈ ({c.s.fr.a₁, c.s.fr.b₁, c.s.fr.a₂, c.s.fr.b₂} : Set G),
      ⁅x, a⁆ = 1 ∨ ⁅x, a⁆ = c.s.fr.z := by
    intro a ha
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha
    rcases ha with rfl | rfl | rfl | rfl
    · exact hcomm_gen c.s.fr.a₁ (by rw [cfg.hA]; exact Subgroup.subset_closure (by simp))
    · exact hcomm_gen c.s.fr.b₁ (by rw [cfg.hA]; exact Subgroup.subset_closure (by simp))
    · exact hcomm_gen c.s.fr.a₂ (by rw [cfg.hA]; exact Subgroup.subset_closure (by simp))
    · exact hcomm_gen c.s.fr.b₂ (by rw [cfg.hA]; exact Subgroup.subset_closure (by simp))
  obtain ⟨a₀, ha₀A, ha₀C⟩ :=
    y4_central_aut cfg.rel.z_sq hza₁ hzb₁ hza₂ hzb₂ cfg.rel.comm1 cfg.rel.comm2
      cfg.rel.a1a2 cfg.rel.a1b2 cfg.rel.b1a2 cfg.rel.b1b2 hy
  refine ⟨a₀, by rw [cfg.hA]; exact ha₀A, ?_⟩
  rw [cfg.hA]
  exact ha₀C

end CFSG.OddStandard.HigherRank.YamadaG23

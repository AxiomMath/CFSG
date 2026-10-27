module

public import CFSG.ClassicalInvolution.Q3.Q3TPSChart

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3TPS

open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.RouteD
  CFSG.Assembly.LowTwoRank
open CFSG.ClassicalInvolution.Q3.Q3TP (TCtxS3 not_locImg_eq_map_fund3S)
open scoped MatrixGroups

variable {G : Type} [Group G]


namespace TCtxS3

variable {Ω : Set (Subgroup G)} {z : G} {tY : StatedLieTag} {nY : ℕ} {K : Subgroup G}
  [Finite G] (c : TCtxS3 tY nY Ω K z)

include c

theorem eq_of_involution_ne (hsingle : ∀ L ∈ Ω, ∃ g : G, L = conjSub g K) {N : Subgroup G}
    (hN : N ∈ Ω) {z₁ : G} (hz₁ : IsClassicalMember3 N z₁) {M M' : Subgroup G} (hM : M ∈ Ω)
    (hM' : M' ∈ Ω) (hzM : IsClassicalMember3 M z₁) (hzM' : IsClassicalMember3 M' z₁)
    (hMN : M ≠ N) (hM'N : M' ≠ N) : M = M' := by
  obtain ⟨c₁⟩ := exists_ctx_member c hsingle hN hz₁
  have key : ∀ M : Subgroup G, ∀ (hM : M ∈ Ω), IsClassicalMember3 M z₁ → M ≠ N →
      M ∈ centralizingMembers Ω {z₁} ∧ locImg Ω z₁ M ≤ c₁.d.Q₁ := by
    intro M hM hzM hMN
    have hMz : M ∈ centralizingMembers Ω {z₁} := ⟨hM, isSubnormal_le hzM.subnormal⟩
    have hfam : locImg Ω z₁ M ∈ locFamily Ω z₁ := mem_locFamily_iff.mpr ⟨M, hMz, rfl⟩
    refine ⟨hMz, ?_⟩
    rcases c₁.d.fam_cases _ hfam with h | h | ⟨R, hR, hMR⟩
    · exact absurd (c₁.eq_of_locImg_le_Q₀ hMz h) hMN
    · exact h
    · exact (not_locImg_eq_map_fund3S c₁.hY hMz hzM c₁.d.ψ c₁.d.ker_le hR hMR).elim
  obtain ⟨hMz, hMQ⟩ := key M hM hzM hMN
  obtain ⟨hMz', hMQ'⟩ := key M' hM' hzM' hM'N
  exact c₁.eq_of_locImg_le_Q₁ hMz hMz' hMQ hMQ'

theorem normalizes_of_cube_one (hsingle : ∀ L ∈ Ω, ∃ g : G, L = conjSub g K) {N : Subgroup G}
    (hN : N ∈ Ω) {z₁ : G} (hz₁ : IsClassicalMember3 N z₁) {s : G} (hs3 : s ^ 3 = 1)
    (hs : s * z₁ * s⁻¹ = z₁) : ∀ n ∈ N, s * n * s⁻¹ ∈ N := by
  have hmem : ∀ g : G, g * z₁ * g⁻¹ = z₁ →
      conjSub g N ∈ Ω ∧ IsClassicalMember3 (conjSub g N) z₁ := fun g hg =>
    ⟨c.hΩ.conjInvariant g N hN, hg ▸ hz₁.conj g⟩
  have hss : (s * s) * z₁ * (s * s)⁻¹ = z₁ := by
    calc (s * s) * z₁ * (s * s)⁻¹ = s * (s * z₁ * s⁻¹) * s⁻¹ := by group
      _ = z₁ := by rw [hs, hs]
  have hs3' : s * (s * s) = 1 := by
    rw [← mul_assoc]
    simpa [pow_succ, mul_assoc] using hs3
  have hNs : conjSub s N = N := by
    by_contra h1
    have h2 : conjSub (s * s) N ≠ N := by
      intro h
      apply h1
      calc conjSub s N = conjSub s (conjSub (s * s) N) := by rw [h]
        _ = conjSub (s * (s * s)) N := (conjSub_mul s (s * s) N).symm
        _ = N := by rw [hs3', conjSub_one]
    obtain ⟨hΩ1, hz1⟩ := hmem s hs
    obtain ⟨hΩ2, hz2⟩ := hmem (s * s) hss
    have h3 : conjSub s N = conjSub (s * s) N :=
      eq_of_involution_ne c hsingle hN hz₁ hΩ1 hΩ2 hz1 hz2 h1 h2
    apply h1
    calc conjSub s N = conjSub s⁻¹ (conjSub (s * s) N) := by
          rw [← conjSub_mul]
          congr 1
          group
      _ = conjSub s⁻¹ (conjSub s N) := by rw [h3]
      _ = N := conjSub_inv_conjSub s N
  intro n hn
  have : s * n * s⁻¹ ∈ conjSub s N := ⟨n, hn, rfl⟩
  rwa [hNs] at this

end TCtxS3

end CFSG.ClassicalInvolution.Q3.Q3TPS

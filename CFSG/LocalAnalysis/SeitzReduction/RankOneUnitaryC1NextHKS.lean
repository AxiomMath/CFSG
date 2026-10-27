module

public import CFSG.LocalAnalysis.SeitzReduction.RankOneUnitaryC1NextDvd
public import CFSG.LocalAnalysis.SeitzReduction.RankOneUnitaryC1NextEight
public import CFSG.LocalAnalysis.SeitzReduction.RankOneUnitaryC1StageNextOdd

public section

set_option linter.unusedSectionVars false

namespace CFSG.SeitzReduction.RankOne

open Subgroup

namespace U3C1Next

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {f : ℕ} {t : G} {T : Subgroup G}
  {d : G} {V U U₁ : Subgroup G} {k : ℕ} {K : Type} [Field K] [Fintype K] [CharP K 2]
  {v : G → K} {μ : K}

section HKS


theorem exists_regData (H : U3C1Next G L f t T d V U U₁ k K v μ)
    (hU : ¬ ∃ S : Sylow 2 G, (S : Subgroup G) = U) : ∃ E, H.RegData E := by
  have : IsSimpleGroup G := H.stage.start.setting.1
  have hf2 : 2 ≤ f := H.stage.start.two_le
  have hY : normalizer (U : Set G) ≠ ⊤ := by
    intro htop
    have hnorm : U.Normal := normalizer_eq_top_iff.mp htop
    rcases hnorm.eq_bot_or_eq_top with hbot | htop'
    · have hcard := H.stage.card_U
      rw [hbot, Subgroup.card_bot] at hcard
      have : 0 < (2 ^ f) ^ (k + 4) := by positivity
      omega
    · exact hU ⟨H.stage.isPGroup_U.toSylow (by rw [htop', Subgroup.index_top]; norm_num), rfl⟩
  have hcardK : Nat.card K = 2 ^ f := by rw [Nat.card_eq_fintype_card, H.card_K]
  rcases odd_stabilizer_two_transitive_kProper_of_dvd H.stage.start.setting.2.2.1 hY
    H.perm H.perm.range le_rfl (H.perm_two_transitive hU) (by omega) hcardK 0
    H.odd_card_range_inf_stabilizer H.card_range_inf_stabilizer_dvd with
    ⟨E, hEN, hEnorm, hEab, hE2, hEcard, hreg⟩ | ⟨hf3, -, h168, hsimple, -⟩
  · refine ⟨E, hEN, hEnorm, hEab, hE2, hEcard, hreg, ?_⟩
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have hA2 : IsPGroup 2 E := IsPGroup.of_card hEcard
    have haff : ∀ x ∈ E, ∃ ℓ : K →+ K, ∀ c, x c = x 0 + ℓ c := by
      intro x hx
      obtain ⟨n, rfl⟩ := hEN hx
      exact H.perm_affine n
    set δn : normalizer (U : Set G) := ⟨d⁻¹, inv_mem H.d_mem_normalizer_U⟩ with hδn
    have hδA : ∀ x ∈ E, (H.perm δn)⁻¹ * x * H.perm δn ∈ E := by
      intro x hx
      have hδN : (H.perm δn)⁻¹ ∈ H.perm.range := inv_mem ⟨δn, rfl⟩
      have := hEnorm.conj_mem ⟨x, hEN hx⟩ (mem_subgroupOf.mpr hx) ⟨_, hδN⟩
      rw [mem_subgroupOf] at this
      simpa using this
    exact SzC1.translation_of_affine H.card_K hf2 H.gen hA2 haff H.perm_d_inv hδA
  · exact (H.false_of_card_range_eq_168 hf3 h168 hsimple).elim

end HKS

end U3C1Next

end CFSG.SeitzReduction.RankOne

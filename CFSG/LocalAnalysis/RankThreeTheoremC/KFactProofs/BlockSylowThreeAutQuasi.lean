module

public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.BlockSylowThreeAutDich
public import CFSG.LocalAnalysis.AGLEmbedding.BlockParabThreeLeviSmall

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs

open CFSG.Open CFSG.AGLEmbedding CFSG.AGLEmbedding.ParabHub CFSG.Assembly.LowTwoRank
  CFSG.QuasithinUnique CFSG.RankThreeCoreUniqueness.Helpers

theorem threeSubgroups_of_quasisimple (hGA : CFSG.Open.GriessAllModelsStatement)
    (hExc : SuOddThreeDvdStatement hGA) {W : Type} [Group W] [Finite W]
    (hW : CFSG.Open.IsQuasisimple W) {t : StatedLieTag} {n : ℕ}
    (hc : StatedClassicalModel (W ⧸ Subgroup.center W) t n 2 1)
    (ht : t = .PSL ∨ t = .PSp ∨ t = .POmegaPlus ∨ t = .POmegaMinus ∨ t = .PSU)
    (hcard : t = .PSU → Nat.card (W ⧸ Subgroup.center W) =
      CFSG.Open.ordTwistedA (n - 1) (2 ^ 1))
    (S : Sylow 2 W) (J : Subgroup W)
    (hNJ : Subgroup.normalizer ((S : Subgroup W) : Set W) ≤ J)
    (hJ : J ≠ Subgroup.normalizer ((S : Subgroup W) : Set W))
    (hperf : ∀ U : Subgroup W, U ≤ J → ⁅U, U⁆ = U → Nat.Coprime 3 (Nat.card U)) :
    (∀ U : Subgroup W, U ≤ J → IsPGroup 3 U → IsElemAbelian 3 U) ∨ 3 ∣ J.index := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Group.IsPerfect W := ⟨hW.1⟩
  set O : Subgroup W := primeComplementCore (G := W) 3 with hOdef
  rcases le_center_or_eq_top_of_normal_quasisimple hW O with hO | hO
  · have hρ₀ : Function.Surjective (QuotientGroup.mk' O) := QuotientGroup.mk'_surjective O
    have hker₀ : (QuotientGroup.mk' O).ker = O := QuotientGroup.ker_mk' O
    obtain ⟨hT₁, hN₁, hJ₁, hperf₁⟩ :=
      map_overgroup_of_central hρ₀ (hker₀.le.trans hO) S hNJ hJ hperf
    obtain ⟨S₁, hS₁⟩ := exists_sylow_of_isSylowTwoOf_top hT₁
    rw [← hS₁] at hN₁ hJ₁
    have hY₁ : Group.IsPerfect (W ⧸ O) := Group.IsPerfect.ofSurjective hρ₀
    have hX := center_centerQuotient_eq_bot hW
    rcases threeSubgroups_of_model_two hGA hExc hY₁ _ (quotCenterOfLeCenter_surjective hO)
      (ker_quotCenterOfLeCenter_le_center hO) (isPGroup_ker_quotCenterOfLeCenter hO) hX hc ht
      hcard S₁ _ hN₁ hJ₁ hperf₁ with hE | h3
    · refine Or.inl (isElemAbelian_of_map (ρ := QuotientGroup.mk' O) ?_ hE)
      rw [hker₀]
      exact primeComplementCore_coprime 3
    · refine Or.inr ?_
      rwa [Subgroup.index_map_eq J hρ₀
        (hker₀.le.trans (hO.trans ((Subgroup.center_le_normalizer _).trans hNJ)))] at h3
  · left
    intro U _ hU
    refine isElemAbelian_of_card_dvd_three ?_
    have hcop : Nat.Coprime 3 (Nat.card (⊤ : Subgroup W)) := hO ▸ primeComplementCore_coprime 3
    obtain ⟨k, hk⟩ := hU.exists_card_eq
    have hdvd : Nat.card U ∣ Nat.card (⊤ : Subgroup W) := Subgroup.card_dvd_of_le le_top
    rw [hk] at hdvd ⊢
    rcases k with _ | k
    · norm_num
    · exact absurd ((dvd_pow_self 3 (Nat.succ_ne_zero k)).trans hdvd)
        ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).1 hcop)

end CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs

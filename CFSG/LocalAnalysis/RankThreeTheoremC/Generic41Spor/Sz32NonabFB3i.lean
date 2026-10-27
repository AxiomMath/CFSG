module

public import CFSG.LocalAnalysis.AGLEmbedding.CaseTwoRank
public import CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.Sz32NonabFB0
public import CFSG.RankThree.PartOne.Census3.Interface

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers
open CFSG.RankThree.PartOne.Census3 (IsoLie)

section Part

variable {Y : Type} [Group Y] [Finite Y] {F Γ B R₀ : Subgroup Y} {x : Y} {L : Subgroup Y} {z : Y}

theorem nf5_I714 (h714 : KFactI714Four') (hc : NF5Cfg F Γ B R₀ x L z) (hFL : ¬ F ≤ L) :
    (∃ (t : CFSG.Assembly.LowTwoRank.StatedLieTag) (n ℓ f : ℕ), ℓ ≠ 5 ∧
      CFSG.Blueprint.LieModel ↥L t n ℓ f) ∧
      (Nat.card ((F ⊓ L : Subgroup Y)) = 25 ∧ IsCyclic ((F ⊓ L : Subgroup Y))) := by
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  obtain ⟨hsimple, hnonab, hcat⟩ :=
    hc.data.catalog.isSimpleGroup_of_center_eq_bot hc.comp hc.cen
  obtain ⟨hFp, hFidx⟩ : IsPGroup 5 F ∧ ¬ 5 ∣ F.index := by
    obtain ⟨_, hFp, hFdvd⟩ := CFSG.ABGLocalTools.isSylowOf_iff.mp hc.data.sylow
    exact ⟨hFp, by rwa [Subgroup.relIndex_top_right] at hFdvd⟩
  obtain ⟨Q, hQ⟩ : ∃ Q : Sylow 5 Y, (Q : Subgroup Y) = F :=
    ⟨IsPGroup.toSylow hFp hFidx, rfl⟩
  have hcardQ : Nat.card (Q : Subgroup Y) = 125 := by
    rw [hQ]
    exact hc.data.card
  have hnonabQ : ¬ IsMulCommutative (Q : Subgroup Y) := by
    rw [hQ]
    exact hc.data.nonab
  have hexpQ : ∀ q ∈ (Q : Subgroup Y), q ^ 25 = 1 := by
    rw [hQ]
    exact hc.data.exp
  have hFLQ : ¬ (Q : Subgroup Y) ≤ L := by
    rw [hQ]
    exact hFL
  have hex5 : ∃ q ∈ (Q : Subgroup Y), q ^ 5 ≠ 1 := by
    by_contra hne
    push_neg at hne
    have hBF : B = F := by
      ext b
      rw [hc.data.hB b]
      refine ⟨fun h => h.1, fun h => ⟨h, hne b ?_⟩⟩
      rw [hQ]
      exact h
    have h125 := hc.data.Bcard
    rw [hBF, hc.data.card] at h125
    norm_num at h125
  obtain ⟨h1, h2⟩ :=
    h714 Y L hc.normal hsimple hnonab hcat hc.cent Q hFLQ hcardQ hnonabQ hexpQ hex5
  rw [hQ] at h2
  exact ⟨h1, h2⟩

end Part

end CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor

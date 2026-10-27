module

public import CFSG.LocalAnalysis.RankThreeTheoremC.TransitivityKFacts
public import CFSG.RankThree.PartOne.K159.CenterRank
import CFSG.Foundations.SteinbergCADefinitionNodes
import CFSG.RankThree.PartOne.N143.CaseB1Theta
import CFSG.RankThree.PartTwo.Setup
import CFSG.LocalAnalysis.AGLEmbedding.CoverRankLift

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.RankThree.PartOne.K159 Subgroup

theorem isKGroup_of_ne_top_of_isKProper {G : Type} [Group G] [Finite G]
    (hK : CFSG.Open.IsKProper G) {H : Subgroup G} (hH : H ≠ ⊤) : CFSG.IsKGroup H :=
  (CFSG.ComponentClassification.CatalogueKProper.isKProper_iff_kProper.2
    (CFSG.ComponentClassification.CatalogueKProper.open_isKProper_iff.1 hK)) H hH

theorem exists_elemAbelian_of_centerRankFour (hCR : CenterRankFour) {G : Type} [Group G]
    [Finite G] (he : CFSG.Open.evenRank G ≤ 3) {H : Subgroup G} (hH : CFSG.IsKGroup H)
    (O : Subgroup H) [O.Normal] (K : Subgroup (H ⧸ O)) (hK : CFSG.IsQuasisimple K) {p : ℕ}
    (hp : p.Prime) (hp3 : 3 < p) (hZ : p ∣ Nat.card (center K))
    (hodd : Odd (Nat.card (center K))) :
    ∃ B : Subgroup K, (∀ b ∈ B, b ^ p = 1) ∧ (∀ a ∈ B, ∀ b ∈ B, a * b = b * a) ∧
      p ^ 4 ≤ Nat.card B := by
  classical
  set K' : Subgroup H := K.comap (QuotientGroup.mk' O) with hK'
  let π : K' →* K := ((QuotientGroup.mk' O).comp K'.subtype).codRestrict K (fun w => w.2)
  have hπ : Function.Surjective π := by
    intro k
    obtain ⟨h, hh⟩ := QuotientGroup.mk'_surjective O (k : H ⧸ O)
    exact ⟨⟨h, by simp [hK', hh]⟩, Subtype.ext hh⟩
  let e : (K' ⧸ π.ker) ≃* K := QuotientGroup.quotientKerEquivOfSurjective π hπ
  have hQ : CFSG.IsQuasisimple (K' ⧸ π.ker) := CFSG.LocalCores.isQuasisimple_of_mulEquiv e.symm hK
  have hKK : CFSG.IsKGroup K' := CFSG.RankThree.PartOne.N143.isKGroup_subgroup hH K'
  have hrank : CFSG.twoLocalOddRank K' ≤ 3 := by
    have h1 := CFSG.RankThree.PartTwo.evenRank_subgroup_le K'
    have h2 := CFSG.RankThree.PartTwo.evenRank_subgroup_le H
    have he' : CFSG.Assembly.evenRank G ≤ 3 := he
    rw [← CFSG.RankThree.OddKernel.evenRank_eq_twoLocalOddRank]
    omega
  have hcard : Nat.card (center (K' ⧸ π.ker)) = Nat.card (center K) :=
    Nat.card_congr (Subgroup.centerCongr e).toEquiv
  obtain ⟨B, hBp, hBc, hBcard⟩ := hCR K' hrank hKK π.ker hQ p hp hp3 (by rw [hcard]; exact hZ)
    (by rw [hcard]; exact hodd)
  refine ⟨B.map e.toMonoidHom, ?_, ?_, ?_⟩
  · rintro _ ⟨b, hb, rfl⟩
    rw [← map_pow]
    simp [hBp b hb]
  · rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    rw [← map_mul, ← map_mul, hBc a ha b hb]
  · rw [Subgroup.card_map_of_injective (f := e.toMonoidHom) (by exact e.injective)]
    exact hBcard

theorem kF1At_of_centerRankFour {G : Type} [Group G] [Finite G] (hCR : CenterRankFour)
    (hS : Setting G) : KF1At G := by
  intro p hp hp5 H hH O _ K hK _ hpg hdvd
  have : Fact p.Prime := ⟨hp⟩
  have hodd : Odd (Nat.card (center K)) := by
    obtain ⟨n, hn⟩ := hpg.exists_card_eq
    rw [hn]
    exact (hp.eq_two_or_odd'.resolve_left (by omega)).pow
  have hK' : CFSG.IsQuasisimple K :=
    ((CFSG.Foundations.SteinbergCA.quasisimple_iff K).2.2.1).2 hK
  obtain ⟨B, hBp, hBc, hBcard⟩ := exists_elemAbelian_of_centerRankFour hCR hS.rank.le
    (isKGroup_of_ne_top_of_isKProper hS.kProper hH) O K hK' hp (by omega) hdvd hodd
  exact CFSG.AGLEmbedding.le_pRank_of_pow_le_card hp le_top
    ⟨isMulCommutative_iff.2 fun a b => Subtype.ext (hBc a a.2 b b.2), hBp⟩ hBcard

end CFSG.LocalAnalysis.RankThreeTheoremC

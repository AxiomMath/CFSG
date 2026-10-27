module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Co2Std.Exclusion.KDM22
public import CFSG.LocalAnalysis.EvenSporadicStandard.Co2Std.Exclusion.KDM22Proof.Alt
public import CFSG.LocalAnalysis.EvenSporadicStandard.Co2Std.Exclusion.KDM22Proof.Basic
public import CFSG.LocalAnalysis.EvenSporadicStandard.Co2Std.Exclusion.KDM22Proof.EvenLie
public import CFSG.LocalAnalysis.EvenSporadicStandard.Co2Std.Exclusion.KDM22Proof.OddLie
public import CFSG.LocalAnalysis.EvenSporadicStandard.Co2Std.Exclusion.KDM22Proof.Sporadic
import CFSG.RankThree.PartOne.S11d.PlaneCases

public section

namespace CFSG.EvenSporadicStandard.Co2Std.Exclusion

open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open KDM22Proof


theorem kdm22_holds : KDM22 := by
  intro F _ _ hs hcat α hα1 hα2 K hKα hKs hK hnorm hle
  have hN := m22Normal_subgroupOf hKα hKs hK hnorm
  have hσ : orderOf α = 2 := orderOf_eq_prime (by rw [sq, hα2]) hα1
  have hle' : Nat.card (fixedSubgroup α) ≤ 4 * 443520 := (card_fixedSubgroup_eq α).trans_le hle
  obtain ⟨a, b, hab⟩ := hN.exists_mul_ne_mul
  have hna : ∃ a b : F, a * b ≠ b * a :=
    ⟨a.1.1, b.1.1, fun h => hab (Subtype.ext (Subtype.ext h))⟩
  rcases RankThree.PartOne.PlaneCases.catalog_cases hcat with
    ⟨q, -, ⟨e⟩⟩ | ⟨n, hn, ⟨θ⟩⟩ | ⟨t, n, ℓ, f, hadm, hmod⟩ | ⟨s, ⟨e⟩⟩
  · obtain ⟨x, y, hxy⟩ := hna
    exact hxy (e.injective (by rw [map_mul, map_mul, mul_comm]))
  · exact false_of_alt hn θ hσ hN.dvd_card hle'
  · rcases eq_or_ne ℓ 2 with rfl | hℓ
    · by_cases hin : α ∈ (MulAut.conj : F →* MulAut F).range
      · exact false_of_evenLie_inner hs hna ⟨t, n, f, hadm, hmod⟩ hσ hin hN.isComponent
      · exact false_of_evenLie_outer hadm hmod hσ hin hN.isPComponent_two
          hN.card_quotient_fusionZStar
    · exact false_of_oddLie hℓ hadm hmod hσ hN.isComponent hN.card_quotient_center
  · exact false_of_sporadic hs hna e hσ hN.isComponent hN.card_quotient_center hN.dvd_card

end CFSG.EvenSporadicStandard.Co2Std.Exclusion

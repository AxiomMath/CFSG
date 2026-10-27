module

public import CFSG.LocalAnalysis.RankThreeEvenClassification.ThompsonAmbient
import CFSG.Foundations.MaxOrderThompsonImage

public section

namespace CFSG.RankThreeEvenClassification.Helpers

universe u v

theorem thompsonCenterOf_map_of_injective_restriction {G : Type u} {H : Type v}
    [Group G] [Group H] [Finite G] [Finite H]
    (homomorphism : G →* H) (subgroup : Subgroup G)
    (hinjective : Function.Injective (homomorphism.comp subgroup.subtype)) :
    thompsonCenterOf (subgroup.map homomorphism) =
      (thompsonCenterOf subgroup).map homomorphism := by
  exact (CFSG.map_ambientOrderZJ_of_injective homomorphism subgroup hinjective).symm

theorem prime_complement_quotient_injective_on_pSubgroup {G : Type u} [Group G] [Finite G]
    (prime : ℕ) (hprime : prime.Prime) (normal subgroup : Subgroup G) [normal.Normal]
    (hcomplement : ¬prime ∣ Nat.card normal) (hpgroup : IsPGroup prime subgroup) :
    Function.Injective ((QuotientGroup.mk' normal).comp subgroup.subtype) := by
  have : Fact prime.Prime := ⟨hprime⟩
  refine CFSG.injective_comp_subtype_of_coprime_card_ker (QuotientGroup.mk' normal) ?_ hpgroup
  rw [QuotientGroup.ker_mk']
  exact hprime.coprime_iff_not_dvd.mpr hcomplement

end CFSG.RankThreeEvenClassification.Helpers

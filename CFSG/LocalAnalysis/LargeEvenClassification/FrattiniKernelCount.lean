module

public import CFSG.LocalAnalysis.LargeEvenClassification.FrattiniExact

public section

namespace CFSG.LargeEvenClassification.Helpers

universe groupUniverse

theorem normal_frattini_image_generator_loss {Ambient : Type groupUniverse} [Group Ambient]
    [Finite Ambient] {prime : ℕ} (hprime : prime.Prime) (hpgroup : IsPGroup prime Ambient)
    (Normal : Subgroup Ambient) (hcommutative : IsMulCommutative Normal) (element : Normal)
    (hfrattini : (element : Ambient) ∈ frattini Ambient)
    (hnotPower : ¬∃ source : Normal, source ^ prime = element) :
    Nat.log prime (Nat.card (Normal.map (QuotientGroup.mk' (frattini Ambient)))) + 1 ≤
      pGeneratorRank prime Normal := by
  let : CommGroup Normal := { (inferInstance : Group Normal) with
    mul_comm := @mul_comm' Normal _ hcommutative }
  let : CommGroup (Ambient ⧸ frattini Ambient) := pGroupFrattiniCommGroup hprime hpgroup
  let projection := QuotientGroup.mk' (frattini Ambient)
  let restriction := projection.subgroupMap Normal
  have hrestriction : Function.Surjective restriction := projection.subgroupMap_surjective Normal
  have hkilled : restriction element = 1 := by
    apply Subtype.ext
    exact (QuotientGroup.eq_one_iff _).mpr hfrattini
  have hexponent : ∀ entry : Normal.map projection, entry ^ prime = 1 := by
    intro entry
    apply Subtype.ext
    exact pGroup_frattini_quotient_exponent hprime hpgroup entry
  have hnotRange : element ∉ (powMonoidHom prime : Normal →* Normal).range := by
    rintro ⟨source, hsource⟩
    exact hnotPower ⟨source, hsource⟩
  exact elementary_image_generator_loss hprime (hpgroup.to_subgroup Normal) restriction hrestriction
    hexponent element hkilled hnotRange

theorem pGeneratorRank_normal_square_saving {Ambient : Type groupUniverse} [Group Ambient]
    [Finite Ambient] {prime : ℕ} (hprime : prime.Prime) (hpgroup : IsPGroup prime Ambient)
    (Normal : Subgroup Ambient) [Normal.Normal] (hcommutative : IsMulCommutative Normal)
    (element : Normal) (hfrattini : (element : Ambient) ∈ frattini Ambient)
    (hnotPower : ¬∃ source : Normal, source ^ prime = element) :
    pGeneratorRank prime Ambient + 1 ≤
      pGeneratorRank prime (Ambient ⧸ Normal) + pGeneratorRank prime Normal := by
  have hsaving := normal_frattini_image_generator_loss hprime hpgroup Normal hcommutative
    element hfrattini hnotPower
  have hformula := pGeneratorRank_extension hprime hpgroup (QuotientGroup.mk' Normal)
    (QuotientGroup.mk'_surjective Normal)
  rw [QuotientGroup.ker_mk'] at hformula
  rw [hformula]
  omega

end CFSG.LargeEvenClassification.Helpers

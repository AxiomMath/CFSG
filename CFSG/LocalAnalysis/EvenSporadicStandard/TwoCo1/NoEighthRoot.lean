module

public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoCo1.ECoreCover
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoCo1.EighthRoot

public section

namespace CFSG.EvenSporadicStandard.TwoCo1

open CFSG.Blueprint CFSG.Blueprint.NativeSporadic CFSG.Monster.GMS

@[expose] def FourthPowerTwoB : Prop := ∀ y : NativeSporadic.Co1, ¬ IsCo1TwoB (y ^ 4)

theorem no_eighth_root_of_cover
    (hS1 : FourthPowerTwoB) {C : Type} [Group C] (π : C →* NativeSporadic.Co1) (ζ : C)
    (hπ : Function.Surjective π) (hker : π.ker = Subgroup.zpowers ζ)
    (hζc : ζ ∈ Subgroup.center C) (hζo : orderOf ζ = 2) : ∀ y : C, y ^ 8 ≠ ζ := by
  have hζ2 : ζ ^ 2 = 1 := by rw [← hζo]; exact pow_orderOf_eq_one ζ
  have hζ1 : ζ ≠ 1 := fun h1 => by rw [h1, orderOf_one] at hζo; exact absurd hζo (by decide)
  refine no_eighth_root_of_lift π hker hζ1 IsCo1TwoB (fun w hw hB => ?_) hS1
  by_cases h1 : π w = 1
  · rcases (mem_ker_iff_eq_one_or_eq π ζ hker hζo).1 (MonoidHom.mem_ker.2 h1) with h | h
    · rw [h]; exact one_pow 2
    · rw [h]; exact hζ2
  · have hc : orderOf (π w) = 2 := orderOf_eq_prime hw h1
    exact sq_eq_one_of_not_isCo1TwoB π ζ hπ hker hζc hζo hc hB

theorem no_eighth_root_of_isSporadic
    (hS1 : FourthPowerTwoB) {G : Type} [Group G] {L : Subgroup G}
    (hQ : IsSporadic (L ⧸ Subgroup.center L) .Co1) {z : G} (hz2 : orderOf z = 2)
    (hZ : (Subgroup.center L).map L.subtype = Subgroup.zpowers z) : ∀ v ∈ L, v ^ 8 ≠ z := by
  obtain ⟨e⟩ := hQ
  obtain ⟨ζ, hζc, hζz⟩ : z ∈ (Subgroup.center L).map L.subtype := hZ ▸ Subgroup.mem_zpowers z
  have hζo : orderOf ζ = 2 := by
    rw [← hz2, ← hζz]
    exact (orderOf_injective L.subtype L.subtype_injective ζ).symm
  have hcenter : Subgroup.center L = Subgroup.zpowers ζ := by
    refine Subgroup.map_injective L.subtype_injective ?_
    rw [hZ, MonoidHom.map_zpowers, ← hζz]
  let π : L →* Carrier .Co1 := e.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center L))
  have hπ : Function.Surjective π := e.surjective.comp (QuotientGroup.mk'_surjective _)
  have hker : π.ker = Subgroup.zpowers ζ := by
    rw [← hcenter]
    ext x
    simp only [MonoidHom.mem_ker, π, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
      QuotientGroup.mk'_apply]
    rw [map_eq_one_iff _ e.injective, QuotientGroup.eq_one_iff]
  intro v hv hv8
  refine no_eighth_root_of_cover hS1 π ζ hπ hker hζc hζo ⟨v, hv⟩ (Subtype.ext ?_)
  rw [SubgroupClass.coe_pow]
  exact hv8.trans hζz.symm

end CFSG.EvenSporadicStandard.TwoCo1

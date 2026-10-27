module

public import CFSG.LocalAnalysis.StandardType.GGSixLayerCXNonsplitE6Gen
public import CFSG.Quasithin.Background.A3ComponentsQuotient

public section

namespace CFSG.LocalAnalysis.GLTheoremA.Y10F

open CFSG.Open

namespace ExcEngine

theorem normal_map_comap_of_layer {K M : Type*} [Group K] [Group M] {C : Subgroup K}
    (ψ : ↥C →* M) {P : Subgroup M}
    (hnorm : ∀ d : ↥C, ∀ u ∈ P, ψ d * u * (ψ d)⁻¹ ∈ P) :
    (((P.comap ψ).map C.subtype).subgroupOf C).Normal := by
  have hN : (P.comap ψ).Normal := ⟨fun u hu d => by
    change ψ (d * u * d⁻¹) ∈ P
    rw [map_mul, map_mul, map_inv]
    exact hnorm d _ hu⟩
  have hcoe : (((P.comap ψ).map C.subtype).subgroupOf C) = P.comap ψ := by
    apply Subgroup.map_injective C.subtype_injective
    rw [Subgroup.map_subgroupOf_eq_of_le (Subgroup.map_subtype_le _)]
  rwa [hcoe]

theorem isQuasisimple_map_comap_of_layer {K M : Type*} [Group K] [Group M] {C : Subgroup K}
    (ψ : ↥C →* M) (hψ : Function.Injective ψ) {P : Subgroup M} (hP : P ≤ ψ.range)
    (hq : CFSG.Open.IsQuasisimple ↥P) :
    CFSG.Open.IsQuasisimple ↥((P.comap ψ).map C.subtype) := by
  have hq' : CFSG.IsQuasisimple (P.comap ψ) :=
    CFSG.StandardType.E6Nonsplit.isQuasisimple_comap_of_layer ψ hψ hP
      (CFSG.Quasithin.A3.isQuasisimple_iff_open.mpr hq)
  exact CFSG.Quasithin.A3.isQuasisimple_iff_open.mp
    (CFSG.LocalCores.isQuasisimple_of_mulEquiv
      (Subgroup.equivMapOfInjective (P.comap ψ) C.subtype C.subtype_injective) hq')

theorem card_map_comap_of_layer {K M : Type*} [Group K] [Group M] {C : Subgroup K}
    (ψ : ↥C →* M) (hψ : Function.Injective ψ) {P : Subgroup M} (hP : P ≤ ψ.range) :
    Nat.card ((P.comap ψ).map C.subtype) = Nat.card P := by
  rw [Subgroup.card_map_of_injective C.subtype_injective]
  have hmap : (P.comap ψ).map ψ = P := by
    rw [Subgroup.map_comap_eq, inf_of_le_right hP]
  calc Nat.card ↥(P.comap ψ) = Nat.card ↥((P.comap ψ).map ψ) :=
        (Subgroup.card_map_of_injective hψ).symm
    _ = Nat.card ↥P := by rw [hmap]

end ExcEngine

theorem quasisimple_normal_map_comap_of_layer {K M : Type*} [Group K] [Group M] {C : Subgroup K}
    (ψ : ↥C →* M) (hψ : Function.Injective ψ) {P : Subgroup M} (hP : P ≤ ψ.range)
    (hq : CFSG.Open.IsQuasisimple ↥P)
    (hnorm : ∀ d : ↥C, ∀ u ∈ P, ψ d * u * (ψ d)⁻¹ ∈ P) :
    ((P.comap ψ).map C.subtype ≤ C) ∧
      ((((P.comap ψ).map C.subtype).subgroupOf C).Normal) ∧
      CFSG.Open.IsQuasisimple ↥((P.comap ψ).map C.subtype) ∧
      Nat.card ((P.comap ψ).map C.subtype) = Nat.card P :=
  ⟨Subgroup.map_subtype_le _, ExcEngine.normal_map_comap_of_layer ψ hnorm,
    ExcEngine.isQuasisimple_map_comap_of_layer ψ hψ hP hq,
    ExcEngine.card_map_comap_of_layer ψ hψ hP⟩

end CFSG.LocalAnalysis.GLTheoremA.Y10F

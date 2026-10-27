module

public import CFSG.LocalAnalysis.ComponentClassification.GMS78Sec5RuB1CentA

public section

namespace CFSG.ComponentClassification.GMS78

open Subgroup CFSG.Open CFSG.ABGLocalTools

variable {G : Type} [Group G] [Finite G]

namespace Sec3.SzR

variable {L T R : Subgroup G} {y d : G}

theorem le_centralizer_gmsA (hS : SzR G L T R 1 y d) : R ≤ centralizer (gmsA L T : Set G) :=
  fun _ hr => mem_centralizer_iff.mpr fun _ hb => (hS.commute_gmsA hr hb).symm

end Sec3.SzR

namespace SzMinCounter

variable {L T R R₂ : Subgroup G} {y d : G}

theorem mem_normalizer_of_map_gmsA_le_centralizer
    (hM : SzMinCounter G L 1)
    (hS : Sec3.SzR G L T R 1 y d) (h34 : NoStronglyClosedAbelian G)
    (hR₂ : Sec3.IsR₂ L T R R₂ d)
    (h4 : Nat.card (T ⊓ centralizer (L : Set G) : Subgroup G) = 4) {g : G}
    (hg : (gmsA L T).map (MulAut.conj g).toMonoidHom ≤
      centralizer (AS76b.oddCoreIn (centralizer (L : Set G)) : Set G)) :
    g ∈ normalizer (AS76b.oddCoreIn (centralizer (L : Set G)) : Set G) := by
  set W := AS76b.oddCoreIn (centralizer (L : Set G)) with hW
  have hle : W.map (MulAut.conj g⁻¹).toMonoidHom ≤ centralizer (gmsA L T : Set G) := by
    rintro _ ⟨w, hw, rfl⟩
    rw [mem_centralizer_iff]
    intro a ha
    have h1 := mem_centralizer_iff.mp (hg ⟨a, ha, rfl⟩) w hw
    simp only [MulEquiv.toMonoidHom_eq_coe, MonoidHom.coe_ofClass, MulAut.conj_apply,
      inv_inv] at h1 ⊢
    calc a * (g⁻¹ * w * g) = g⁻¹ * ((g * a * g⁻¹) * w) * g := by group
      _ = g⁻¹ * (w * (g * a * g⁻¹)) * g := by rw [h1]
      _ = g⁻¹ * w * g * a := by group
  have h2 := hM.le_oddCoreIn_of_le_centralizer_gmsA hS h34 hR₂ h4
    (by rw [card_map_of_injective (MulAut.conj g⁻¹).injective]
        exact AS76b.odd_card_oddCoreIn _) hle
  simpa using inv_mem (AS76b.mem_normalizer_of_map_conj_le h2)

end SzMinCounter

end CFSG.ComponentClassification.GMS78

module

public import CFSG.Assembly.Defs
public import CFSG.LocalAnalysis.RankThreeEvenClassification.LocalCore

public section

namespace CFSG.RankThreeEvenClassification.Helpers

universe u v

theorem pair_internal_generators_top {actor : Type u} [Group actor] (first second : actor) :
    Subgroup.zpowers (⟨first, Subgroup.mem_sup_left (Subgroup.mem_zpowers first)⟩ :
      (Subgroup.zpowers first ⊔ Subgroup.zpowers second : Subgroup actor)) ⊔
    Subgroup.zpowers (⟨second, Subgroup.mem_sup_right (Subgroup.mem_zpowers second)⟩ :
      (Subgroup.zpowers first ⊔ Subgroup.zpowers second : Subgroup actor)) = ⊤ := by
  let pair := Subgroup.zpowers first ⊔ Subgroup.zpowers second
  apply Subgroup.map_injective pair.subtype_injective
  rw [Subgroup.map_sup, MonoidHom.map_zpowers, MonoidHom.map_zpowers]
  change pair = (⊤ : Subgroup pair).map pair.subtype
  ext member
  exact ⟨fun hmember => ⟨⟨member, hmember⟩, Subgroup.mem_top _, rfl⟩,
    fun ⟨preimage, _, heq⟩ => heq ▸ preimage.property⟩

theorem pair_homomorphism_range {actor : Type u} {target : Type v} [Group actor] [Group target]
    (first second : actor)
    (homomorphism : (Subgroup.zpowers first ⊔ Subgroup.zpowers second : Subgroup actor) →* target) :
    homomorphism.range =
      Subgroup.zpowers (homomorphism ⟨first, Subgroup.mem_sup_left (Subgroup.mem_zpowers first)⟩) ⊔
        Subgroup.zpowers (homomorphism ⟨second, Subgroup.mem_sup_right (Subgroup.mem_zpowers second)⟩) := by
  have hmap : (⊤ : Subgroup (Subgroup.zpowers first ⊔ Subgroup.zpowers second : Subgroup actor)).map
      homomorphism = homomorphism.range := by
    ext member
    exact ⟨fun ⟨preimage, _, heq⟩ => ⟨preimage, heq⟩,
      fun ⟨preimage, heq⟩ => ⟨preimage, Subgroup.mem_top _, heq⟩⟩
  rw [← hmap, ← pair_internal_generators_top first second,
    Subgroup.map_sup, MonoidHom.map_zpowers, MonoidHom.map_zpowers]

end CFSG.RankThreeEvenClassification.Helpers

module

public import CFSG.LocalAnalysis.ComponentClassification.SylowTwoImageLifting
public import CFSG.LocalAnalysis.ComponentClassification.BlockThreeFactorImages

public section

open CFSG.Open

namespace CFSG.ComponentClassification.BlockPermutationSylowLifting

theorem lift {G : Type*} [Group G] [Finite G]
    (component : Subgroup G) (heven : Even (Nat.card component))
    (huniversal : UniversalComponentBlock.Universal component) (hquasisimple : IsQuasisimple component)
    (label : Fin 3 ≃ ↥(UniversalOrbitBlock.block component))
    (factor : Subgroup G) (swap : Equiv.Perm (Fin 3))
    (hswap : swap = Equiv.swap 0 1 ∨ swap = Equiv.swap 0 2 ∨ swap = Equiv.swap 1 2)
    (himage : ∀ member : Equiv.Perm (Fin 3),
      member ∈ BlockThreeFactorImages.image (UniversalOrbitBlock.normalizer component) factor
        (BlockPermutationAction.permutation component heven huniversal hquasisimple label) ↔ member = 1 ∨ member = swap)
    (sylow : Sylow 2 ↥(factor ⊓ UniversalOrbitBlock.normalizer component)) :
    ∃ member : UniversalOrbitBlock.normalizer component,
      member.val ∈ (sylow : Subgroup ↥(factor ⊓ UniversalOrbitBlock.normalizer component)).map
          (factor ⊓ UniversalOrbitBlock.normalizer component).subtype ∧
        BlockPermutationAction.permutation component heven huniversal hquasisimple label member = swap := by
  let overlap := factor ⊓ UniversalOrbitBlock.normalizer component
  let inclusion := Subgroup.inclusion (inf_le_right : overlap ≤ UniversalOrbitBlock.normalizer component)
  let permutation := BlockPermutationAction.permutation component heven huniversal hquasisimple label
  let homomorphism := permutation.comp inclusion
  have hrange : homomorphism.range = BlockThreeFactorImages.image (UniversalOrbitBlock.normalizer component) factor permutation :=
    BlockThreeFactorImages.range_eq _ _ _
  have htwo : IsPGroup 2 homomorphism.range := by
    rw [hrange]
    exact SylowTwoImageLifting.swap_two _ swap hswap (fun member hmember => (himage member).mp hmember)
  have hmember : swap ∈ homomorphism.range := by
    rw [hrange]
    exact (himage swap).mpr (Or.inr rfl)
  obtain ⟨member, hmember, heq⟩ := SylowTwoImageLifting.range homomorphism htwo sylow swap hmember
  exact ⟨inclusion member, Subgroup.mem_map.mpr ⟨member, hmember, rfl⟩, heq⟩

end CFSG.ComponentClassification.BlockPermutationSylowLifting

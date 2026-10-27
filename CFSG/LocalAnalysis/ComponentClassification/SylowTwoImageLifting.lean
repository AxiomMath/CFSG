module

public import CFSG.Assembly.Defs

public section

namespace CFSG.ComponentClassification.SylowTwoImageLifting

theorem surjective {G Image : Type*} [Group G] [Finite G] [Group Image]
    (homomorphism : G →* Image) (hsurjective : Function.Surjective homomorphism)
    (htwo : IsPGroup 2 Image) (sylow : Sylow 2 G) :
    ∀ member : Image, ∃ lift : G, lift ∈ (sylow : Subgroup G) ∧ homomorphism lift = member := by
  let imageSylow := sylow.mapSurjective (f := homomorphism) hsurjective
  have htop : (imageSylow : Subgroup Image) = ⊤ := by
    have hmaximal := imageSylow.is_maximal' (htwo.of_injective (⊤ : Subgroup Image).subtype
      (⊤ : Subgroup Image).subtype_injective)
      (le_top : (imageSylow : Subgroup Image) ≤ ⊤)
    exact hmaximal.symm
  intro member
  have hmember : member ∈ (imageSylow : Subgroup Image) := htop ▸ Subgroup.mem_top member
  rw [Sylow.coe_mapSurjective] at hmember
  exact Subgroup.mem_map.mp hmember

theorem range {G Image : Type*} [Group G] [Finite G] [Group Image]
    (homomorphism : G →* Image) (htwo : IsPGroup 2 homomorphism.range) (sylow : Sylow 2 G)
    (member : Image) (hmember : member ∈ homomorphism.range) :
    ∃ lift : G, lift ∈ (sylow : Subgroup G) ∧ homomorphism lift = member := by
  obtain ⟨lift, hlift, heq⟩ := surjective homomorphism.rangeRestrict homomorphism.rangeRestrict_surjective htwo sylow
    ⟨member, hmember⟩
  exact ⟨lift, hlift, congrArg Subtype.val heq⟩

theorem swap_two (subgroup : Subgroup (Equiv.Perm (Fin 3))) (swap : Equiv.Perm (Fin 3))
    (hswap : swap = Equiv.swap 0 1 ∨ swap = Equiv.swap 0 2 ∨ swap = Equiv.swap 1 2)
    (himage : ∀ member ∈ subgroup, member = 1 ∨ member = swap) : IsPGroup 2 subgroup := by
  have hsquare : swap ^ 2 = 1 := by
    rcases hswap with rfl | rfl | rfl <;> decide
  intro member
  refine ⟨1, ?_⟩
  change member ^ 2 = 1
  apply Subtype.ext
  change member.val ^ 2 = 1
  rcases himage member.val member.property with heq | heq
  · rw [heq, one_pow]
  · rw [heq]
    exact hsquare

end CFSG.ComponentClassification.SylowTwoImageLifting

module

public import CFSG.CharacterTheory.BrauerThirdMainTheorem.ClassDefects
public import Mathlib.GroupTheory.Nilpotent

public section

open CFSG
namespace CFSG.BrauerThirdMainTheorem.Helpers

theorem classDefect_of_maximal_centralizing {G : Type*} [Group G]
    (prime : ℕ) (element : G) (subgroup : Subgroup G)
    (hpGroup : IsPGroup prime subgroup)
    (hcentralizes : subgroup ≤ Subgroup.centralizer {element})
    (hmaximal : ∀ other : Subgroup G, IsPGroup prime other → subgroup ≤ other →
      other ≤ Subgroup.centralizer {element} → other = subgroup) :
    classDefect prime (ConjClasses.mk element) subgroup := by
  let centralizer := Subgroup.centralizer {element}
  let localSubgroup := subgroup.subgroupOf centralizer
  have hpLocal : IsPGroup prime localSubgroup :=
    hpGroup.of_equiv (Subgroup.subgroupOfEquivOfLe hcentralizes).symm
  let sylow : Sylow prime centralizer := Sylow.mk localSubgroup hpLocal (by
    intro other hpOther hinclusion
    have hequal := hmaximal (other.map centralizer.subtype) (hpOther.map centralizer.subtype)
      (by
        rw [← Subgroup.map_subgroupOf_eq_of_le hcentralizes]
        exact Subgroup.map_mono hinclusion) (Subgroup.map_subtype_le _)
    apply Subgroup.map_injective centralizer.subtype_injective
    rw [Subgroup.map_subgroupOf_eq_of_le hcentralizes]
    exact hequal)
  exact ⟨element, rfl, sylow, Subgroup.map_subgroupOf_eq_of_le hcentralizes⟩

theorem classDefect_maximal_centralizing {G : Type*} [Group G] [Finite G]
    (prime : ℕ) (hprime : prime.Prime) (element : G) {subgroup : Subgroup G}
    (hdefect : classDefect prime (ConjClasses.mk element) subgroup)
    (_hcentralizes : subgroup ≤ Subgroup.centralizer {element})
    {other : Subgroup G} (hpOther : IsPGroup prime other)
    (hinclusion : subgroup ≤ other) (hotherCentralizes : other ≤ Subgroup.centralizer {element}) :
    other = subgroup := by
  have hpLocal : IsPGroup prime (other.subgroupOf (Subgroup.centralizer {element})) :=
    hpOther.of_equiv (Subgroup.subgroupOfEquivOfLe hotherCentralizes).symm
  obtain ⟨sylow, hsylow⟩ := hpLocal.exists_le_sylow
  let extension := (sylow : Subgroup (Subgroup.centralizer {element})).map
    (Subgroup.centralizer {element}).subtype
  have hotherLe : other ≤ extension := by
    rw [← Subgroup.map_subgroupOf_eq_of_le hotherCentralizes]
    exact Subgroup.map_mono hsylow
  have hextensionDefect : classDefect prime (ConjClasses.mk element) extension :=
    ⟨element, rfl, sylow, rfl⟩
  have hcard := classDefect_card_eq prime hprime hdefect hextensionDefect
  exact (Subgroup.eq_of_le_of_card_ge hinclusion
    (hcard.symm ▸ Subgroup.card_le_of_le hotherLe)).symm

theorem pGroup_eq_of_self_normalizing {G : Type*} [Group G] [Finite G]
    (prime : ℕ) (hprime : prime.Prime) (large small : Subgroup G)
    (hpLarge : IsPGroup prime large) (hinclusion : small ≤ large)
    (hself : Subgroup.normalizer (small.subgroupOf large : Set large) =
      small.subgroupOf large) : large = small := by
  let : Fact prime.Prime := ⟨hprime⟩
  let : Group.IsNilpotent large := hpLarge.isNilpotent
  have htop := normalizerCondition_iff_only_full_group_self_normalizing.mp
    Group.normalizerCondition_of_isNilpotent (small.subgroupOf large) hself
  exact le_antisymm (Subgroup.subgroupOf_eq_top.mp htop) hinclusion

end CFSG.BrauerThirdMainTheorem.Helpers

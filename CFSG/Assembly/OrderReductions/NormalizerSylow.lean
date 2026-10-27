module

public import CFSG.Assembly.OrderReductions.DoubleTransitiveSylow
public import CFSG.Assembly.OrderReductions.InternalComponents
public import CFSG.Assembly.OrderReductions.InternalSylow

public section

namespace CFSG.OrderReductions.NormalizerSylow

open CFSG.OrderReductions.InvolutionGraph
open CFSG.OrderReductions.TwoPointInvolutions

theorem internal_pair_sylow_image {group : Type*} [Group group] [Finite group]
    (prime : ℕ) [Fact (Nat.Prime prime)] (subgroup pair : Subgroup group) (pair_le : pair ≤ subgroup)
    (first second : Component subgroup) (pair_eq : pair.subgroupOf subgroup = pairSubgroup first second)
    (sylow : Sylow prime pair) :
    ∃ internal : Sylow prime (pairSubgroup first second),
      ((internal : Subgroup (pairSubgroup first second)).map (pairSubgroup first second).subtype).map subgroup.subtype =
        (sylow : Subgroup pair).map pair.subtype := by
  let image := (sylow : Subgroup pair).map pair.subtype
  have image_pair : image ≤ pair := Subgroup.map_subtype_le _
  have image_le := image_pair.trans pair_le
  let internal_image := image.subgroupOf subgroup
  have internal_prime : IsPGroup prime internal_image :=
    (sylow.isPGroup'.map pair.subtype).of_equiv (Subgroup.subgroupOfEquivOfLe image_le).symm
  have internal_le : internal_image ≤ pairSubgroup first second := by
    rw [← pair_eq]
    exact Subgroup.subgroupOf_mono subgroup image_pair
  have internal_card : Nat.card internal_image = CFSG.OrderReductions.PrimePart.primePart prime
      (Nat.card (pairSubgroup first second)) := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe image_le).toEquiv,
      CFSG.OrderReductions.PrimePart.sylow_map_card_eq_primePart, ← pair_eq,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe pair_le).toEquiv]
  obtain ⟨internal, internal_eq⟩ := CFSG.OrderReductions.PrimePart.exists_sylow_image_of_card prime
    internal_image (pairSubgroup first second) internal_le internal_card
  refine ⟨internal, ?_⟩
  rw [internal_eq, Subgroup.map_subgroupOf_eq_of_le image_le]

theorem odd_sylow_point_normalizer_of_nonregular {group : Type*} [Group group] [Finite group]
    (prime : ℕ) [Fact (Nat.Prime prime)] (first second : Component group) (distinct : first ≠ second)
    (not_regular : ¬ CFSG.OrderReductions.PrimeRegular.PRegular prime (pairSubgroup first second) (componentStabilizer first))
    (sylow : Sylow prime (pairSubgroup first second)) :
    Odd (Nat.card ↥(Subgroup.normalizer
      ((sylow : Subgroup (pairSubgroup first second)).map (pairSubgroup first second).subtype : Set group) ⊓
        componentStabilizer first)) := by
  apply Nat.not_even_iff_odd.mp
  intro even_normalizer
  apply not_regular
  exact (CFSG.OrderReductions.PrimeRegular.pRegular_iff_some_even_normalizer prime _ _
    (distinct_componentStabilizers_odd_intersection first second distinct)).mpr ⟨sylow, even_normalizer⟩

theorem ambient_sylow_in_normalizer
    {group : Type*} [Group group] [Finite group] (prime : ℕ) [Fact (Nat.Prime prime)] (odd_prime : Odd prime)
    (point : Component group) (normalizer : Subgroup group) (inside : Involution normalizer)
    (stabilizer_eq : (componentStabilizer point).subgroupOf normalizer =
      componentStabilizer ((commutingGraph normalizer).connectedComponentMk inside))
    (acting : normalizer) (moves : acting.val • point ≠ point)
    (pair_le : pairSubgroup point (acting.val • point) ≤ normalizer)
    (two_transitive : MulAction.IsMultiplyPretransitive normalizer (Component normalizer) 2)
    (even_point_rule : CFSG.OrderReductions.EmptyRegularity.EvenPointRule (group := normalizer) prime)
    (not_regular : ¬ CFSG.OrderReductions.PrimeRegular.PRegular prime (pairSubgroup point (acting.val • point))
      (componentStabilizer point))
    (sylow : Sylow prime (pairSubgroup point (acting.val • point))) :
    ∃ ambient : Sylow prime normalizer,
      (ambient : Subgroup normalizer).map normalizer.subtype =
        (sylow : Subgroup (pairSubgroup point (acting.val • point))).map
          (pairSubgroup point (acting.val • point)).subtype := by
  let first := (commutingGraph normalizer).connectedComponentMk inside
  let second := acting • first
  have distinct := CFSG.OrderReductions.InternalComponents.internal_pair_distinct point normalizer inside stabilizer_eq acting moves
  have pair_eq := CFSG.OrderReductions.InternalComponents.internal_pair_eq point normalizer inside stabilizer_eq acting
  obtain ⟨internal, image_eq⟩ := internal_pair_sylow_image prime normalizer _ pair_le first second pair_eq sylow
  have odd_ambient := odd_sylow_point_normalizer_of_nonregular prime point (acting.val • point) moves.symm
    not_regular sylow
  have odd_internal := CFSG.OrderReductions.InternalSylow.odd_internal_point_normalizer normalizer
    (componentStabilizer point) first stabilizer_eq
    ((internal : Subgroup (pairSubgroup first second)).map (pairSubgroup first second).subtype)
    _ image_eq odd_ambient
  obtain ⟨ambient, ambient_eq⟩ := CFSG.OrderReductions.DoubleTransitiveSylow.ambient_sylow_of_odd_sylow_normalizer
    prime odd_prime even_point_rule two_transitive first second distinct internal odd_internal
  refine ⟨ambient, ?_⟩
  rw [ambient_eq]
  exact image_eq

end CFSG.OrderReductions.NormalizerSylow

module

public import CFSG.Assembly.OrderReductions.NormalizerInduction
public import CFSG.Assembly.OrderReductions.ThompsonCoreProduct

public section

namespace CFSG.OrderReductions.ThompsonNormalizer

universe group_universe

open CFSG.OrderReductions.InvolutionGraph
open CFSG.OrderReductions.TwoPointInvolutions
open CFSG.OrderReductions.ThompsonCenter
open CFSG.OrderReductions.ThompsonCoreProduct

theorem normalizes_thompsonCenter_image {group : Type*} [Group group]
    (subgroup : Subgroup group) (element : group)
    (normalizes : element ∈ Subgroup.normalizer (subgroup : Set group)) :
    element ∈ Subgroup.normalizer ((thompsonCenter subgroup).map subgroup.subtype : Set group) :=
  CFSG.OrderReductions.RegularCore.characteristic_pair_image_normalizes subgroup (thompsonCenter subgroup) element normalizes

theorem coreProduct_image_normalizes {group : Type*} [Group group] [Finite group]
    (prime : ℕ) [Fact (Nat.Prime prime)] (pair : Subgroup group) (sylow : Sylow prime pair)
    (element : group)
    (core_normalizes : element ∈ Subgroup.normalizer
      (CFSG.OrderReductions.PrimeComplementCore.ambientCore prime pair : Set group))
    (sylow_normalizes : element ∈ Subgroup.normalizer
      ((sylow : Subgroup pair).map pair.subtype : Set group)) :
    element ∈ Subgroup.normalizer ((coreProduct prime sylow).map pair.subtype : Set group) := by
  let image := (sylow : Subgroup pair).map pair.subtype
  let image_equivalence : (sylow : Subgroup pair) ≃* image :=
    MulEquiv.ofBijective (pair.subtype.subgroupMap (sylow : Subgroup pair))
      ⟨fun first second equal => by
          have equal_values : first.val.val = second.val.val :=
            congrArg (fun candidate : image => candidate.val) equal
          exact Subtype.ext (Subtype.ext equal_values),
        pair.subtype.subgroupMap_surjective _⟩
  have intertwines : image.subtype.comp image_equivalence.toMonoidHom =
      pair.subtype.comp (sylow : Subgroup pair).subtype := by
    ext element
    rfl
  have center_image := congrArg (fun candidate : Subgroup image => candidate.map image.subtype)
    (thompsonCenter_map_eq image_equivalence)
  rw [Subgroup.map_map, intertwines, ← Subgroup.map_map] at center_image
  have center_normalizes := normalizes_thompsonCenter_image image element sylow_normalizes
  rw [← center_image] at center_normalizes
  change element ∈ Subgroup.normalizer
    ((CFSG.OrderReductions.PrimeComplementCore.primeComplementCore prime pair).map pair.subtype : Set group) at core_normalizes
  apply Subgroup.mem_normalizer_iff_map_conj_eq.mpr
  unfold coreProduct
  rw [Subgroup.map_sup, Subgroup.map_sup,
    Subgroup.mem_normalizer_iff_map_conj_eq.mp core_normalizes,
    Subgroup.mem_normalizer_iff_map_conj_eq.mp center_normalizes]

theorem double_transitive_of_equal_core_and_independent_product
    {group : Type group_universe} [Group group] [Finite group]
    (induction_hypothesis : ∀ (smaller : Type group_universe) [Group smaller] [Finite smaller],
      Nat.card smaller < Nat.card group →
      ∀ first second : Involution smaller, first ≠ second → Commute first.val second.val →
        ∀ subgroup : Subgroup smaller, StronglyEmbedded subgroup →
          MulAction.IsMultiplyPretransitive smaller (CFSG.OrderReductions.StrongEmbedding.Conjugates subgroup) 2)
    (prime : ℕ) [Fact (Nat.Prime prime)]
    (point other : Component group) (distinct_points : point ≠ other)
    (strong : StronglyEmbedded (componentStabilizer point)) (degree : 3 ≤ Nat.card (Component group))
    (pair_nontrivial : pairSubgroup point other ≠ ⊥)
    (regular : CFSG.OrderReductions.PrimeRegular.PRegular prime (pairSubgroup point other) (componentStabilizer point))
    (flip inside : Involution group) (first_moves : flip.val • point = other)
    (second_moves : flip.val • other = point) (inside_mem : inside.val ∈ componentStabilizer point)
    (core_eq : CFSG.OrderReductions.PrimeComplementCore.ambientCore prime
      (CFSG.OrderReductions.InvolutiveIntersection.intersection (MulAut.conj inside.val) (pairSubgroup point other)) =
        CFSG.OrderReductions.PrimeComplementCore.ambientCore prime (pairSubgroup point other))
    (first second : Involution group) (distinct_involutions : first ≠ second)
    (commutes : Commute first.val second.val)
    (first_mem : first.val ∈ componentStabilizer point)
    (second_mem : second.val ∈ componentStabilizer point)
    (independent : ∀ sylow other_sylow : Sylow prime (pairSubgroup point other),
      coreProduct prime sylow = coreProduct prime other_sylow)
    (ambient_rule : ∀ other_prime : ℕ, Nat.Prime other_prime →
      CFSG.OrderReductions.EmptyRegularity.EvenPointRule (group := group) other_prime)
    (normalizer_rule : ∀ normal : Subgroup group, normal ≤ pairSubgroup point other →
      (normal.subgroupOf (pairSubgroup point other)).Normal →
      ∀ other_prime : ℕ, Nat.Prime other_prime →
        CFSG.OrderReductions.EmptyRegularity.EvenPointRule (group := Subgroup.normalizer (normal : Set group)) other_prime) :
    MulAction.IsMultiplyPretransitive group (Component group) 2 := by
  classical
  let pair := pairSubgroup point other
  obtain ⟨sylow, inside_sylow_normalizes⟩ :=
    CFSG.OrderReductions.PrimeRegular.pRegular_pair_every_involution_invariant_sylow
      prime point other distinct_points regular inside inside_mem
  have : Nontrivial pair := (Subgroup.nontrivial_iff_ne_bot pair).mpr pair_nontrivial
  have characteristic : (coreProduct prime sylow).Characteristic :=
    coreProduct_characteristic_of_independent_sylow prime sylow (fun candidate => independent candidate sylow)
  have : (coreProduct prime sylow).Characteristic := characteristic
  let normal := (coreProduct prime sylow).map pair.subtype
  have normal_nontrivial : normal ≠ ⊥ := by
    intro trivial
    apply coreProduct_nontrivial prime sylow
    apply Subgroup.map_injective (f := pair.subtype) Subtype.val_injective
    rw [Subgroup.map_bot]
    exact trivial
  have contains : normal ≤ pairSubgroup point (flip.val • point) := by
    rw [first_moves]
    exact Subgroup.map_subtype_le _
  have internal_eq : normal.subgroupOf pair = coreProduct prime sylow :=
    Subgroup.comap_map_eq_self_of_injective Subtype.val_injective _
  have : (normal.subgroupOf (pairSubgroup point (flip.val • point))).Normal := by
    rw [first_moves, internal_eq]
    infer_instance
  have flip_normalizes : flip.val ∈ Subgroup.normalizer (normal : Set group) :=
    CFSG.OrderReductions.RegularCore.characteristic_pair_image_normalizes pair (coreProduct prime sylow) flip.val
      (flip_normalizes_pair point other flip first_moves second_moves)
  have inside_core_normalizes : inside.val ∈ Subgroup.normalizer
      (CFSG.OrderReductions.PrimeComplementCore.ambientCore prime pair : Set group) :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mpr
      (CFSG.OrderReductions.RegularCore.core_invariant_of_equal_intersection prime (MulAut.conj inside.val)
        (CFSG.OrderReductions.PrimeRegular.involution_conjugation_involutive inside) pair core_eq)
  have inside_normalizes := coreProduct_image_normalizes prime pair sylow inside.val
    inside_core_normalizes inside_sylow_normalizes
  have flip_outside : flip.val ∉ componentStabilizer point := by
    intro fixes
    exact distinct_points (fixes.symm.trans first_moves)
  have internal_normal : (normal.subgroupOf pair).Normal := by
    rw [internal_eq]
    infer_instance
  exact CFSG.OrderReductions.NormalizerInduction.double_transitive_of_nontrivial_normal_pair
    induction_hypothesis point strong degree inside flip inside_mem flip_outside normal normal_nontrivial contains
    inside_normalizes flip_normalizes first second distinct_involutions commutes first_mem second_mem ambient_rule
    (normalizer_rule normal (Subgroup.map_subtype_le _) internal_normal)

end CFSG.OrderReductions.ThompsonNormalizer

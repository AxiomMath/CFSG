module

public import Mathlib
public import Mathlib.Algebra.CharP.Lemmas
public import Mathlib.Algebra.Module.ZMod
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Mathlib.GroupTheory.Frattini
public import Mathlib.GroupTheory.Subgroup.Center
public import Mathlib.LinearAlgebra.Determinant
public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.LinearAlgebra.Dual.Lemmas
public import Mathlib.LinearAlgebra.Eigenspace.Triangularizable
public import Mathlib.LinearAlgebra.TensorProduct.Tower
public import Mathlib.RepresentationTheory.Basic
public import Mathlib.RepresentationTheory.Irreducible
public import Mathlib.RingTheory.TensorProduct.Finite
public import CFSG.Assembly.OrderReductions.FixedPairSylow
public import CFSG.Assembly.OrderReductions.InvariantSylow
public import CFSG.Assembly.OrderReductions.FixedConjugator
public import CFSG.Assembly.OrderReductions.CoprimeFixedSubgroup
public import CFSG.Assembly.OrderReductions.PrimePart
public import CFSG.Assembly.OrderReductions.FourGroupGeneration
public import CFSG.Assembly.OrderReductions.PrimeInvolutionGeneration

public section

namespace CFSG.OrderReductions.PrimeInvolutionSylow

open scoped Pointwise

abbrev InvariantSylows {actor group : Type*} [Group actor] [Group group]
    (prime : ℕ) (action : actor →* MulAut group) :=
  {sylow : Sylow prime group // ∀ acting : actor,
    (sylow : Subgroup group).map (action acting).toMonoidHom = sylow}

theorem fixed_conjugate_invariant {actor group : Type*} [Group actor] [Group group]
    (prime : ℕ) (action : actor →* MulAut group)
    (sylow : InvariantSylows prime action)
    (conjugator : CFSG.OrderReductions.CoprimeFixedSubgroup.fixedSubgroup action) :
    ∀ acting : actor, ((conjugator.val • sylow.val : Sylow prime group) : Subgroup group).map
      (action acting).toMonoidHom = (conjugator.val • sylow.val : Sylow prime group) := by
  intro acting
  rw [CFSG.OrderReductions.FixedPairSylow.sylow_smul_subgroup_eq,
    CFSG.OrderReductions.FixedConjugator.automorphism_conjugate_map, sylow.property]
  rw [(CFSG.OrderReductions.CoprimeFixedSubgroup.mem_fixedSubgroup action conjugator.val).mp
    conjugator.property acting]

@[expose, instance_reducible] def fixedConjugationAction {actor group : Type*}
    [Group actor] [Group group] (prime : ℕ) (action : actor →* MulAut group) :
    MulAction (CFSG.OrderReductions.CoprimeFixedSubgroup.fixedSubgroup action) (InvariantSylows prime action) where
  smul conjugator sylow := ⟨conjugator.val • sylow.val,
    fixed_conjugate_invariant prime action sylow conjugator⟩
  one_smul sylow := by
    apply Subtype.ext
    exact one_smul group sylow.val
  mul_smul first second sylow := by
    apply Subtype.ext
    exact mul_smul first.val second.val sylow.val

theorem invariant_sylow_card_odd {actor group : Type*}
    [Group actor] [Group group] [Finite group]
    (acting_prime sylow_prime : ℕ) [Fact (Nat.Prime acting_prime)] [Fact (Nat.Prime sylow_prime)]
    (prime_actor : IsPGroup acting_prime actor) (coprime : ¬ acting_prime ∣ Nat.card group)
    (odd_group : Odd (Nat.card group)) (action : actor →* MulAut group) :
    Odd (Nat.card (InvariantSylows sylow_prime action)) := by
  let := fixedConjugationAction sylow_prime action
  have transitive : MulAction.IsPretransitive (CFSG.OrderReductions.CoprimeFixedSubgroup.fixedSubgroup action)
      (InvariantSylows sylow_prime action) := by
    constructor
    intro first second
    obtain ⟨conjugator, conjugates, fixed⟩ :=
      CFSG.OrderReductions.FixedConjugator.invariant_sylows_conjugate_of_coprime
        acting_prime sylow_prime prime_actor coprime action first.val second.val
        first.property second.property
    let acting : CFSG.OrderReductions.CoprimeFixedSubgroup.fixedSubgroup action :=
      ⟨conjugator, (CFSG.OrderReductions.CoprimeFixedSubgroup.mem_fixedSubgroup action conjugator).mpr fixed⟩
    refine ⟨acting, ?_⟩
    apply Subtype.ext
    change (conjugator • first.val : Sylow sylow_prime group) = second.val
    apply Sylow.ext
    rw [CFSG.OrderReductions.FixedPairSylow.sylow_smul_subgroup_eq]
    exact conjugates
  have := transitive
  obtain ⟨sample, invariant⟩ := CFSG.OrderReductions.InvariantSylow.exists_invariant_sylow_of_coprime
    acting_prime sylow_prime prime_actor coprime action
  let point : InvariantSylows sylow_prime action := ⟨sample, invariant⟩
  rw [← MulAction.index_stabilizer_of_transitive
    (CFSG.OrderReductions.CoprimeFixedSubgroup.fixedSubgroup action) point]
  exact odd_group.of_dvd_nat ((MulAction.stabilizer
    (CFSG.OrderReductions.CoprimeFixedSubgroup.fixedSubgroup action) point).index_dvd_card.trans
      (CFSG.OrderReductions.CoprimeFixedSubgroup.fixedSubgroup action).card_subgroup_dvd_card)

theorem automorphism_preserves_invariant_sylow {actor group : Type*}
    [Group actor] [Group group] (prime : ℕ)
    (action : actor →* MulAut group) (actor_automorphism : MulAut actor)
    (actor_involutive : Function.Involutive actor_automorphism) (automorphism : MulAut group)
    (compatible : ∀ acting : actor, ∀ element : group,
      automorphism (action acting element) = action (actor_automorphism acting) (automorphism element))
    (sylow : InvariantSylows prime action) :
    ∀ acting : actor, ((automorphism • sylow.val : Sylow prime group) : Subgroup group).map
      (action acting).toMonoidHom = (automorphism • sylow.val : Sylow prime group) := by
  intro acting
  have intertwines : (action acting).toMonoidHom.comp automorphism.toMonoidHom =
      automorphism.toMonoidHom.comp (action (actor_automorphism acting)).toMonoidHom := by
    ext element
    exact (actor_involutive acting ▸ compatible (actor_automorphism acting) element).symm
  rw [Sylow.pointwise_smul_def]
  change ((sylow.val : Subgroup group).map automorphism.toMonoidHom).map
    (action acting).toMonoidHom = (sylow.val : Subgroup group).map automorphism.toMonoidHom
  rw [Subgroup.map_map, intertwines, ← Subgroup.map_map, sylow.property]

@[expose] def invariantSylowInvolution {actor group : Type*}
    [Group actor] [Group group] (prime : ℕ)
    (action : actor →* MulAut group) (actor_automorphism : MulAut actor)
    (actor_involutive : Function.Involutive actor_automorphism) (automorphism : MulAut group)
    (involutive : Function.Involutive automorphism)
    (compatible : ∀ acting : actor, ∀ element : group,
      automorphism (action acting element) = action (actor_automorphism acting) (automorphism element)) :
    Equiv.Perm (InvariantSylows prime action) :=
  { toFun := fun sylow => ⟨automorphism • sylow.val,
      automorphism_preserves_invariant_sylow prime action actor_automorphism actor_involutive
        automorphism compatible sylow⟩
    invFun := fun sylow => ⟨automorphism • sylow.val,
      automorphism_preserves_invariant_sylow prime action actor_automorphism actor_involutive
        automorphism compatible sylow⟩
    left_inv := fun sylow => by
      apply Subtype.ext
      have square : automorphism * automorphism = 1 := by
        ext element
        exact involutive element
      change automorphism • (automorphism • sylow.val) = sylow.val
      rw [← mul_smul, square, one_smul]
    right_inv := fun sylow => by
      apply Subtype.ext
      have square : automorphism * automorphism = 1 := by
        ext element
        exact involutive element
      change automorphism • (automorphism • sylow.val) = sylow.val
      rw [← mul_smul, square, one_smul] }

theorem exists_common_invariant_sylow {actor group : Type*}
    [Group actor] [Group group] [Finite group]
    (acting_prime sylow_prime : ℕ) [Fact (Nat.Prime acting_prime)] [Fact (Nat.Prime sylow_prime)]
    (prime_actor : IsPGroup acting_prime actor) (coprime : ¬ acting_prime ∣ Nat.card group)
    (odd_group : Odd (Nat.card group)) (action : actor →* MulAut group)
    (actor_automorphism : MulAut actor) (actor_involutive : Function.Involutive actor_automorphism)
    (automorphism : MulAut group) (involutive : Function.Involutive automorphism)
    (compatible : ∀ acting : actor, ∀ element : group,
      automorphism (action acting element) = action (actor_automorphism acting) (automorphism element)) :
    ∃ sylow : Sylow sylow_prime group,
      (∀ acting : actor, (sylow : Subgroup group).map (action acting).toMonoidHom = sylow) ∧
      (sylow : Subgroup group).map automorphism.toMonoidHom = sylow := by
  classical
  let points := InvariantSylows sylow_prime action
  let permutation := invariantSylowInvolution sylow_prime action actor_automorphism actor_involutive
    automorphism involutive compatible
  let := Fintype.ofFinite points
  have : Fact (Nat.Prime 2) := ⟨by decide⟩
  have permutation_square : permutation ^ (2 ^ 1) = 1 := by
    apply Equiv.ext
    intro sylow
    change permutation (permutation sylow) = sylow
    exact permutation.left_inv sylow
  have odd_points := invariant_sylow_card_odd acting_prime sylow_prime prime_actor coprime odd_group action
  have not_divides : ¬ 2 ∣ Fintype.card points := by
    rw [← Nat.card_eq_fintype_card]
    exact odd_points.not_two_dvd_nat
  obtain ⟨fixed, fixed_eq⟩ := Equiv.Perm.exists_fixed_point_of_prime not_divides permutation_square
  refine ⟨fixed.val, fixed.property, ?_⟩
  have sylow_eq : (automorphism • fixed.val : Sylow sylow_prime group) = fixed.val :=
    congrArg Subtype.val fixed_eq
  have subgroup_eq := congrArg (fun sylow : Sylow sylow_prime group => (sylow : Subgroup group)) sylow_eq
  rwa [Sylow.pointwise_smul_def] at subgroup_eq

theorem odd_fixed_generation {actor group : Type*}
    [Group actor] [Group group] [Finite group]
    (prime : ℕ) [Fact (Nat.Prime prime)] (prime_actor : IsPGroup prime actor)
    (coprime : ¬ prime ∣ Nat.card group) (odd_group : Odd (Nat.card group))
    (action : actor →* MulAut group) (actor_automorphism : MulAut actor)
    (actor_involutive : Function.Involutive actor_automorphism)
    (actor_generated : Subgroup.closure {acting : actor | actor_automorphism acting = acting⁻¹} = ⊤)
    (automorphism : MulAut group) (involutive : Function.Involutive automorphism)
    (compatible : ∀ acting : actor, ∀ element : group,
      automorphism (action acting element) = action (actor_automorphism acting) (automorphism element)) :
    CFSG.OrderReductions.PrimeInvolutionGeneration.FixedGeneration action actor_automorphism automorphism := by
  intro subgroup actor_fixed twisted_fixed
  apply CFSG.OrderReductions.PrimePart.eq_top_of_contains_sylow_for_every_prime
  intro sylow_prime sylow_prime_is_prime
  have : Fact (Nat.Prime sylow_prime) := ⟨sylow_prime_is_prime⟩
  obtain ⟨sylow, action_invariant, automorphism_invariant⟩ := exists_common_invariant_sylow
    prime sylow_prime prime_actor coprime odd_group action actor_automorphism actor_involutive
      automorphism involutive compatible
  refine ⟨sylow, ?_⟩
  apply Subgroup.subgroupOf_eq_top.mp
  apply CFSG.OrderReductions.PrimeInvolutionGeneration.pGroup_fixed_generation prime sylow_prime prime_actor
    sylow.isPGroup' (fun divides => coprime
      (divides.trans (sylow : Subgroup group).card_subgroup_dvd_card))
    (odd_group.of_dvd_nat (sylow : Subgroup group).card_subgroup_dvd_card)
    (CFSG.OrderReductions.InvariantSylow.restrictedHomomorphism action sylow action_invariant)
    actor_automorphism actor_involutive actor_generated
    (CFSG.OrderReductions.InvariantSylow.restrictedAutomorphism automorphism sylow automorphism_invariant)
    (CFSG.OrderReductions.InvariantSylow.restrictedAutomorphism_involutive
      automorphism involutive sylow automorphism_invariant)
    (CFSG.OrderReductions.PrimeInvolutionGeneration.restricted_compatible action actor_automorphism
      automorphism compatible sylow action_invariant automorphism_invariant)
  · intro element fixed
    exact actor_fixed element.val (fun acting => congrArg Subtype.val (fixed acting))
  · intro acting inverted element fixed
    exact twisted_fixed acting inverted element.val (congrArg Subtype.val fixed)

end CFSG.OrderReductions.PrimeInvolutionSylow

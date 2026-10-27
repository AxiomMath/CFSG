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
public import CFSG.Assembly.OrderReductions.InvariantSylow
public import CFSG.Assembly.OrderReductions.FixedPointLifting
public import CFSG.Assembly.OrderReductions.InvariantQuotient
public import CFSG.Assembly.OrderReductions.FourGroupGeneration
public import CFSG.Assembly.OrderReductions.Reduction

public section

namespace CFSG.OrderReductions.PrimeInvolutionGeneration

@[expose] def FixedGeneration {actor group : Type*} [Group actor] [Group group]
    (action : actor →* MulAut group) (actor_automorphism : MulAut actor)
    (automorphism : MulAut group) : Prop :=
  ∀ subgroup : Subgroup group,
    (∀ element : group, (∀ acting : actor, action acting element = element) → element ∈ subgroup) →
    (∀ acting : actor, actor_automorphism acting = acting⁻¹ → ∀ element : group,
      (action acting * automorphism : MulAut group) element = element → element ∈ subgroup) →
    subgroup = ⊤

@[expose] def generators {actor group : Type*} [Group actor] [Group group]
    (action : actor →* MulAut group) (actor_automorphism : MulAut actor)
    (automorphism : MulAut group) : Set group :=
  {element | (∀ acting : actor, action acting element = element) ∨
    ∃ acting : actor, actor_automorphism acting = acting⁻¹ ∧
      (action acting * automorphism : MulAut group) element = element}

@[expose] def generationSubgroup {actor group : Type*} [Group actor] [Group group]
    (action : actor →* MulAut group) (actor_automorphism : MulAut actor)
    (automorphism : MulAut group) : Subgroup group :=
  Subgroup.closure (generators action actor_automorphism automorphism)

theorem action_mul_apply {actor group : Type*} [Group actor] [Group group]
    (action : actor →* MulAut group) (first second : actor) (element : group) :
    action (first * second) element = action first (action second element) := by
  rw [map_mul]
  rfl

theorem twisted_involutive {actor group : Type*} [Group actor] [Group group]
    (action : actor →* MulAut group) (actor_automorphism : MulAut actor)
    (automorphism : MulAut group) (involutive : Function.Involutive automorphism)
    (compatible : ∀ acting : actor, ∀ element : group,
      automorphism (action acting element) = action (actor_automorphism acting) (automorphism element))
    (acting : actor) (inverted : actor_automorphism acting = acting⁻¹) :
    Function.Involutive (action acting * automorphism : MulAut group) := by
  intro element
  change action acting (automorphism (action acting (automorphism element))) = element
  rw [compatible, involutive, inverted, ← action_mul_apply, mul_inv_cancel, map_one]
  rfl

theorem twisted_actor_inverted {actor : Type*} [Group actor]
    (actor_automorphism : MulAut actor) (involutive : Function.Involutive actor_automorphism)
    (conjugator acting : actor) (inverted : actor_automorphism acting = acting⁻¹) :
    actor_automorphism (conjugator * acting * (actor_automorphism conjugator)⁻¹) =
      (conjugator * acting * (actor_automorphism conjugator)⁻¹)⁻¹ := by
  rw [map_mul, map_mul, map_inv, involutive, inverted, mul_inv_rev, mul_inv_rev, inv_inv]
  group

theorem twisted_action_conjugate {actor group : Type*} [Group actor] [Group group]
    (action : actor →* MulAut group) (actor_automorphism : MulAut actor)
    (automorphism : MulAut group)
    (compatible : ∀ acting : actor, ∀ element : group,
      automorphism (action acting element) = action (actor_automorphism acting) (automorphism element))
    (conjugator acting : actor) (element : group) :
    (action (conjugator * acting * (actor_automorphism conjugator)⁻¹) * automorphism :
      MulAut group) (action conjugator element) =
        action conjugator ((action acting * automorphism : MulAut group) element) := by
  change action (conjugator * acting * (actor_automorphism conjugator)⁻¹)
    (automorphism (action conjugator element)) = action conjugator (action acting (automorphism element))
  rw [compatible, ← action_mul_apply,
    show (conjugator * acting * (actor_automorphism conjugator)⁻¹) * actor_automorphism conjugator =
      conjugator * acting from by group, action_mul_apply]

theorem generation_le {actor group : Type*} [Group actor] [Group group]
    (action : actor →* MulAut group) (actor_automorphism : MulAut actor)
    (automorphism : MulAut group) (subgroup : Subgroup group)
    (actor_fixed : ∀ element : group, (∀ acting : actor, action acting element = element) →
      element ∈ subgroup)
    (twisted_fixed : ∀ acting : actor, actor_automorphism acting = acting⁻¹ →
      ∀ element : group, (action acting * automorphism : MulAut group) element = element →
        element ∈ subgroup) : generationSubgroup action actor_automorphism automorphism ≤ subgroup := by
  apply (Subgroup.closure_le subgroup).mpr
  intro element element_mem
  rcases element_mem with fixed | ⟨acting, inverted, fixed⟩
  · exact actor_fixed element fixed
  · exact twisted_fixed acting inverted element fixed

theorem map_generation_eq_of_maps_generators {actor group : Type*}
    [Group actor] [Group group] [Finite group]
    (action : actor →* MulAut group) (actor_automorphism : MulAut actor)
    (automorphism mapping : MulAut group)
    (maps : ∀ element ∈ generators action actor_automorphism automorphism,
      mapping element ∈ generationSubgroup action actor_automorphism automorphism) :
    (generationSubgroup action actor_automorphism automorphism).map mapping.toMonoidHom =
      generationSubgroup action actor_automorphism automorphism := by
  apply Subgroup.eq_of_le_of_card_ge
  · apply Subgroup.map_le_iff_le_comap.mpr
    exact (Subgroup.closure_le _).mpr maps
  · rw [Subgroup.card_map_of_injective mapping.injective]

theorem generation_actor_invariant {actor group : Type*}
    [Group actor] [Group group] [Finite group]
    (action : actor →* MulAut group) (actor_automorphism : MulAut actor)
    (actor_involutive : Function.Involutive actor_automorphism) (automorphism : MulAut group)
    (compatible : ∀ acting : actor, ∀ element : group,
      automorphism (action acting element) = action (actor_automorphism acting) (automorphism element))
    (conjugator : actor) :
    (generationSubgroup action actor_automorphism automorphism).map
      (action conjugator).toMonoidHom = generationSubgroup action actor_automorphism automorphism := by
  apply map_generation_eq_of_maps_generators
  intro element element_mem
  apply Subgroup.subset_closure
  rcases element_mem with fixed | ⟨acting, inverted, fixed⟩
  · left
    rw [fixed conjugator]
    exact fixed
  · right
    refine ⟨conjugator * acting * (actor_automorphism conjugator)⁻¹,
      twisted_actor_inverted actor_automorphism actor_involutive conjugator acting inverted, ?_⟩
    rw [twisted_action_conjugate action actor_automorphism automorphism compatible, fixed]

theorem generation_automorphism_invariant {actor group : Type*}
    [Group actor] [Group group] [Finite group]
    (action : actor →* MulAut group) (actor_automorphism : MulAut actor)
    (actor_involutive : Function.Involutive actor_automorphism) (automorphism : MulAut group)
    (involutive : Function.Involutive automorphism)
    (compatible : ∀ acting : actor, ∀ element : group,
      automorphism (action acting element) = action (actor_automorphism acting) (automorphism element)) :
    (generationSubgroup action actor_automorphism automorphism).map automorphism.toMonoidHom =
      generationSubgroup action actor_automorphism automorphism := by
  apply map_generation_eq_of_maps_generators
  intro element element_mem
  apply Subgroup.subset_closure
  rcases element_mem with fixed | ⟨acting, inverted, fixed⟩
  · left
    intro acting
    have relation := compatible (actor_automorphism acting) element
    rw [actor_involutive, fixed] at relation
    exact relation.symm
  · right
    refine ⟨actor_automorphism acting, ?_, ?_⟩
    · rw [actor_involutive, inverted, inv_inv]
    · change action (actor_automorphism acting) (automorphism (automorphism element)) =
        automorphism element
      rw [involutive]
      have relation := compatible acting (automorphism element)
      rw [involutive] at relation
      change action acting (automorphism element) = element at fixed
      rw [← relation, fixed]

theorem quotient_compatible {actor group : Type*} [Group actor] [Group group]
    (action : actor →* MulAut group) (actor_automorphism : MulAut actor)
    (automorphism : MulAut group)
    (compatible : ∀ acting : actor, ∀ element : group,
      automorphism (action acting element) = action (actor_automorphism acting) (automorphism element))
    (normal : Subgroup group) [normal.Normal]
    (action_invariant : ∀ acting : actor, normal.map (action acting).toMonoidHom = normal)
    (automorphism_invariant : normal.map automorphism.toMonoidHom = normal) :
    ∀ acting : actor, ∀ point : group ⧸ normal,
      CFSG.OrderReductions.InvariantQuotient.quotientAutomorphism automorphism normal automorphism_invariant
        (CFSG.OrderReductions.InvariantQuotient.quotientHomomorphism action normal action_invariant acting point) =
      CFSG.OrderReductions.InvariantQuotient.quotientHomomorphism action normal action_invariant
        (actor_automorphism acting)
          (CFSG.OrderReductions.InvariantQuotient.quotientAutomorphism automorphism normal
            automorphism_invariant point) := by
  intro acting point
  induction point using QuotientGroup.induction_on with
  | H element =>
      change CFSG.OrderReductions.InvariantQuotient.quotientAutomorphism automorphism normal automorphism_invariant
        (CFSG.OrderReductions.InvariantQuotient.quotientAutomorphism (action acting) normal (action_invariant acting)
          (QuotientGroup.mk' normal element)) =
        CFSG.OrderReductions.InvariantQuotient.quotientAutomorphism (action (actor_automorphism acting)) normal
          (action_invariant (actor_automorphism acting))
          (CFSG.OrderReductions.InvariantQuotient.quotientAutomorphism automorphism normal automorphism_invariant
            (QuotientGroup.mk' normal element))
      rw [CFSG.OrderReductions.InvariantQuotient.quotientAutomorphism_apply,
        CFSG.OrderReductions.InvariantQuotient.quotientAutomorphism_apply,
        CFSG.OrderReductions.InvariantQuotient.quotientAutomorphism_apply,
        CFSG.OrderReductions.InvariantQuotient.quotientAutomorphism_apply, compatible]

theorem restricted_compatible {actor group : Type*} [Group actor] [Group group]
    (action : actor →* MulAut group) (actor_automorphism : MulAut actor)
    (automorphism : MulAut group)
    (compatible : ∀ acting : actor, ∀ element : group,
      automorphism (action acting element) = action (actor_automorphism acting) (automorphism element))
    (subgroup : Subgroup group)
    (action_invariant : ∀ acting : actor, subgroup.map (action acting).toMonoidHom = subgroup)
    (automorphism_invariant : subgroup.map automorphism.toMonoidHom = subgroup) :
    ∀ acting : actor, ∀ element : subgroup,
      CFSG.OrderReductions.InvariantSylow.restrictedAutomorphism automorphism subgroup automorphism_invariant
        (CFSG.OrderReductions.InvariantSylow.restrictedHomomorphism action subgroup action_invariant acting element) =
      CFSG.OrderReductions.InvariantSylow.restrictedHomomorphism action subgroup action_invariant
        (actor_automorphism acting)
          (CFSG.OrderReductions.InvariantSylow.restrictedAutomorphism automorphism subgroup
            automorphism_invariant element) := by
  intro acting element
  exact Subtype.ext (compatible acting element.val)

theorem normal_fixed_generation {actor group : Type*}
    [Group actor] [Group group] [Finite group]
    (prime : ℕ) [Fact (Nat.Prime prime)] (prime_actor : IsPGroup prime actor)
    (coprime : ¬ prime ∣ Nat.card group) (odd_group : Odd (Nat.card group))
    (action : actor →* MulAut group) (actor_automorphism : MulAut actor)
    (actor_generated : Subgroup.closure {acting : actor | actor_automorphism acting = acting⁻¹} = ⊤)
    (automorphism : MulAut group) (involutive : Function.Involutive automorphism)
    (compatible : ∀ acting : actor, ∀ element : group,
      automorphism (action acting element) = action (actor_automorphism acting) (automorphism element))
    (subgroup : Subgroup group) [subgroup.Normal]
    (action_invariant : ∀ acting : actor, subgroup.map (action acting).toMonoidHom = subgroup)
    (automorphism_invariant : subgroup.map automorphism.toMonoidHom = subgroup)
    (actor_fixed : ∀ element : group, (∀ acting : actor, action acting element = element) →
      element ∈ subgroup)
    (twisted_fixed : ∀ acting : actor, actor_automorphism acting = acting⁻¹ →
      ∀ element : group, (action acting * automorphism : MulAut group) element = element →
        element ∈ subgroup) : subgroup = ⊤ := by
  let projection := QuotientGroup.mk' subgroup
  let quotient_action := CFSG.OrderReductions.InvariantQuotient.quotientHomomorphism action subgroup action_invariant
  let quotient_automorphism := CFSG.OrderReductions.InvariantQuotient.quotientAutomorphism
    automorphism subgroup automorphism_invariant
  have equivariant : ∀ acting : actor, ∀ element : group,
      projection (action acting element) = quotient_action acting (projection element) := by
    intro acting element
    exact (CFSG.OrderReductions.InvariantQuotient.quotientAutomorphism_apply
      (action acting) subgroup (action_invariant acting) element).symm
  have automorphism_equivariant : ∀ element : group,
      projection (automorphism element) = quotient_automorphism (projection element) := by
    intro element
    exact (CFSG.OrderReductions.InvariantQuotient.quotientAutomorphism_apply
      automorphism subgroup automorphism_invariant element).symm
  have odd_kernel : Odd (Nat.card projection.ker) := by
    rw [QuotientGroup.ker_mk']
    exact odd_group.of_dvd_nat subgroup.card_subgroup_dvd_card
  have quotient_involutive := CFSG.OrderReductions.InvariantQuotient.quotientAutomorphism_involutive
    automorphism involutive subgroup automorphism_invariant
  have quotient_compatibility := quotient_compatible action actor_automorphism automorphism
    compatible subgroup action_invariant automorphism_invariant
  have twisted_inverse : ∀ acting : actor, actor_automorphism acting = acting⁻¹ →
      ∀ point : group ⧸ subgroup,
        (quotient_action acting * quotient_automorphism : MulAut (group ⧸ subgroup)) point = point⁻¹ := by
    intro acting inverted
    have fixed_free : MonoidHom.FixedPointFree
        (quotient_action acting * quotient_automorphism : MulAut (group ⧸ subgroup)) := by
      intro point point_fixed
      obtain ⟨element, image_eq, element_fixed⟩ :=
        CFSG.OrderReductions.FixedPointLifting.exists_fixed_lift_of_odd_kernel
          (action acting * automorphism) (quotient_action acting * quotient_automorphism)
          (twisted_involutive action actor_automorphism automorphism involutive compatible acting inverted)
          projection (QuotientGroup.mk'_surjective subgroup) odd_kernel
          (fun element => by
            change projection (action acting (automorphism element)) =
              quotient_action acting (quotient_automorphism (projection element))
            rw [equivariant, automorphism_equivariant]) point point_fixed
      rw [← image_eq]
      exact (QuotientGroup.eq_one_iff element).mpr (twisted_fixed acting inverted element element_fixed)
    exact fun point => congrFun
      (fixed_free.coe_eq_inv_of_involutive
        (twisted_involutive quotient_action actor_automorphism quotient_automorphism
          quotient_involutive quotient_compatibility acting inverted)) point
  have automorphism_inverse : ∀ point : group ⧸ subgroup, quotient_automorphism point = point⁻¹ := by
    intro point
    simpa only [map_one, one_mul] using twisted_inverse 1 (by simp) point
  have inverted_trivial : ∀ acting : actor, actor_automorphism acting = acting⁻¹ →
      quotient_action acting = 1 := by
    intro acting inverted
    ext point
    change quotient_action acting point = point
    have relation := twisted_inverse acting inverted point⁻¹
    change quotient_action acting (quotient_automorphism point⁻¹) = point⁻¹⁻¹ at relation
    simpa only [automorphism_inverse, inv_inv] using relation
  have action_trivial : ∀ acting : actor, quotient_action acting = 1 := by
    have generated_le : Subgroup.closure {acting : actor | actor_automorphism acting = acting⁻¹} ≤
        quotient_action.ker :=
      (Subgroup.closure_le _).mpr inverted_trivial
    rw [actor_generated] at generated_le
    intro acting
    exact generated_le (Subgroup.mem_top acting)
  have quotient_one : ∀ point : group ⧸ subgroup, point = 1 := by
    intro point
    obtain ⟨element, image_eq, element_fixed⟩ :=
      CFSG.OrderReductions.FixedPointLifting.exists_fixed_lift_of_coprime prime prime_actor action quotient_action
        projection (QuotientGroup.mk'_surjective subgroup) coprime equivariant point
          (fun acting => by rw [action_trivial]; rfl)
    rw [← image_eq]
    exact (QuotientGroup.eq_one_iff element).mpr (actor_fixed element element_fixed)
  apply top_unique
  intro element _
  exact (QuotientGroup.eq_one_iff element).mp (quotient_one (projection element))

theorem abelian_fixed_generation {actor group : Type*}
    [Group actor] [CommGroup group] [Finite group]
    (prime : ℕ) [Fact (Nat.Prime prime)] (prime_actor : IsPGroup prime actor)
    (coprime : ¬ prime ∣ Nat.card group) (odd_group : Odd (Nat.card group))
    (action : actor →* MulAut group) (actor_automorphism : MulAut actor)
    (actor_involutive : Function.Involutive actor_automorphism)
    (actor_generated : Subgroup.closure {acting : actor | actor_automorphism acting = acting⁻¹} = ⊤)
    (automorphism : MulAut group) (involutive : Function.Involutive automorphism)
    (compatible : ∀ acting : actor, ∀ element : group,
      automorphism (action acting element) = action (actor_automorphism acting) (automorphism element)) :
    FixedGeneration action actor_automorphism automorphism := by
  intro subgroup actor_fixed twisted_fixed
  let generated := generationSubgroup action actor_automorphism automorphism
  have generated_top : generated = ⊤ := by
    apply normal_fixed_generation prime prime_actor coprime odd_group action actor_automorphism
      actor_generated automorphism involutive compatible generated
      (generation_actor_invariant action actor_automorphism actor_involutive automorphism compatible)
      (generation_automorphism_invariant action actor_automorphism actor_involutive automorphism
        involutive compatible)
    · intro element fixed
      exact Subgroup.subset_closure (Or.inl fixed)
    · intro acting inverted element fixed
      exact Subgroup.subset_closure (Or.inr ⟨acting, inverted, fixed⟩)
  exact top_unique (generated_top ▸ generation_le action actor_automorphism automorphism subgroup
    actor_fixed twisted_fixed)

theorem solvable_fixed_generation {actor group : Type*}
    [Group actor] [Group group] [Finite group] [Group.IsSolvable group]
    (prime : ℕ) [Fact (Nat.Prime prime)] (prime_actor : IsPGroup prime actor)
    (coprime : ¬ prime ∣ Nat.card group) (odd_group : Odd (Nat.card group))
    (action : actor →* MulAut group) (actor_automorphism : MulAut actor)
    (actor_involutive : Function.Involutive actor_automorphism)
    (actor_generated : Subgroup.closure {acting : actor | actor_automorphism acting = acting⁻¹} = ⊤)
    (automorphism : MulAut group) (involutive : Function.Involutive automorphism)
    (compatible : ∀ acting : actor, ∀ element : group,
      automorphism (action acting element) = action (actor_automorphism acting) (automorphism element)) :
    FixedGeneration action actor_automorphism automorphism := by
  classical
  generalize order_eq : Nat.card group = order
  induction order using Nat.strong_induction_on generalizing group with
  | h order induction_hypothesis =>
      by_cases trivial : Subsingleton group
      · let := trivial
        intro subgroup _ _
        apply top_unique
        intro element _
        simpa only [Subsingleton.elim element 1] using subgroup.one_mem
      · have : Nontrivial group := not_subsingleton_iff_nontrivial.mp trivial
        let normal := commutator group
        have action_invariant : ∀ acting : actor, normal.map (action acting).toMonoidHom = normal :=
          fun acting => Subgroup.characteristic_iff_map_eq.mp
            (inferInstance : normal.Characteristic) (action acting)
        have automorphism_invariant : normal.map automorphism.toMonoidHom = normal :=
          Subgroup.characteristic_iff_map_eq.mp (inferInstance : normal.Characteristic) automorphism
        have smaller : Nat.card normal < order := by
          rw [← order_eq]
          exact CFSG.OrderReductions.Reduction.proper_subgroup_card_lt group normal
            (Group.IsSolvable.commutator_lt_top_of_nontrivial group).ne
        let restricted_action := CFSG.OrderReductions.InvariantSylow.restrictedHomomorphism
          action normal action_invariant
        let restricted_automorphism := CFSG.OrderReductions.InvariantSylow.restrictedAutomorphism
          automorphism normal automorphism_invariant
        have normal_generation : FixedGeneration restricted_action actor_automorphism
            restricted_automorphism :=
          induction_hypothesis (Nat.card normal) smaller
            (fun divides => coprime (divides.trans normal.card_subgroup_dvd_card))
            (odd_group.of_dvd_nat normal.card_subgroup_dvd_card) restricted_action restricted_automorphism
            (CFSG.OrderReductions.InvariantSylow.restrictedAutomorphism_involutive
              automorphism involutive normal automorphism_invariant)
            (restricted_compatible action actor_automorphism automorphism compatible normal
              action_invariant automorphism_invariant) rfl
        intro subgroup actor_fixed twisted_fixed
        let generated := generationSubgroup action actor_automorphism automorphism
        have normal_le : normal ≤ generated := by
          apply Subgroup.subgroupOf_eq_top.mp
          apply normal_generation
          · intro element fixed
            exact Subgroup.subset_closure (Or.inl
              (fun acting => congrArg Subtype.val (fixed acting)))
          · intro acting inverted element fixed
            exact Subgroup.subset_closure (Or.inr
              ⟨acting, inverted, congrArg Subtype.val fixed⟩)
        have : generated.Normal := Subgroup.Normal.of_commutator_le group normal_le
        have generated_top : generated = ⊤ := by
          apply normal_fixed_generation prime prime_actor coprime odd_group action actor_automorphism
            actor_generated automorphism involutive compatible generated
            (generation_actor_invariant action actor_automorphism actor_involutive automorphism compatible)
            (generation_automorphism_invariant action actor_automorphism actor_involutive automorphism
              involutive compatible)
          · intro element fixed
            exact Subgroup.subset_closure (Or.inl fixed)
          · intro acting inverted element fixed
            exact Subgroup.subset_closure (Or.inr ⟨acting, inverted, fixed⟩)
        exact top_unique (generated_top ▸ generation_le action actor_automorphism automorphism subgroup
          actor_fixed twisted_fixed)

theorem pGroup_fixed_generation {actor group : Type*}
    [Group actor] [Group group] [Finite group]
    (acting_prime group_prime : ℕ) [Fact (Nat.Prime acting_prime)] [Fact (Nat.Prime group_prime)]
    (prime_actor : IsPGroup acting_prime actor) (prime_group : IsPGroup group_prime group)
    (coprime : ¬ acting_prime ∣ Nat.card group) (odd_group : Odd (Nat.card group))
    (action : actor →* MulAut group) (actor_automorphism : MulAut actor)
    (actor_involutive : Function.Involutive actor_automorphism)
    (actor_generated : Subgroup.closure {acting : actor | actor_automorphism acting = acting⁻¹} = ⊤)
    (automorphism : MulAut group) (involutive : Function.Involutive automorphism)
    (compatible : ∀ acting : actor, ∀ element : group,
      automorphism (action acting element) = action (actor_automorphism acting) (automorphism element)) :
    FixedGeneration action actor_automorphism automorphism := by
  have : Group.IsNilpotent group := prime_group.isNilpotent
  exact solvable_fixed_generation acting_prime prime_actor coprime odd_group action actor_automorphism
    actor_involutive actor_generated automorphism involutive compatible

end CFSG.OrderReductions.PrimeInvolutionGeneration

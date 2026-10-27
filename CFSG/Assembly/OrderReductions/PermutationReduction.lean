module

public import Mathlib
public import CFSG.Mathlib.GroupTheory.Basic
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
public import CFSG.Open.OrderForm
public import CFSG.Assembly.OrderReductions.Helpers

public section

open CFSG.Open

namespace CFSG.OrderReductions.PermutationReduction

theorem simple_coset_action_injective (group : Type*) [Group group]
    [IsSimpleGroup group] (subgroup : Subgroup group) (proper : subgroup ≠ ⊤) :
    Function.Injective (MulAction.toPermHom group (group ⧸ subgroup)) := by
  apply (MonoidHom.ker_eq_bot_iff _).mp
  rw [← subgroup.normalCore_eq_ker]
  rcases CFSG.eq_bot_or_eq_top_of_normal subgroup.normalCore inferInstance with
    core_bot | core_top
  · exact core_bot
  · exact False.elim (proper (top_le_iff.mp (core_top ▸ subgroup.normalCore_le)))

theorem simple_card_dvd_index_factorial (group : Type*) [Group group] [Finite group]
    [IsSimpleGroup group] (subgroup : Subgroup group) (proper : subgroup ≠ ⊤) :
    Nat.card group ∣ Nat.factorial subgroup.index := by
  have card_dvd := Subgroup.card_dvd_of_injective
    (MulAction.toPermHom group (group ⧸ subgroup))
    (simple_coset_action_injective group subgroup proper)
  simpa only [Nat.card_perm, ← subgroup.index_eq_card] using card_dvd

theorem perfect_perm_hom_mem_alternating (group : Type*) [Group group]
    [Group.IsPerfect group] (points : Type*) [Fintype points] [DecidableEq points]
    (homomorphism : group →* Equiv.Perm points) (element : group) :
    homomorphism element ∈ alternatingGroup points := by
  rw [Equiv.Perm.mem_alternatingGroup]
  have trivial_sign : Equiv.Perm.sign.comp homomorphism = 1 :=
    CFSG.OrderReductions.Helpers.perfect_hom_to_commutative_eq_one group ℤˣ
      (Equiv.Perm.sign.comp homomorphism)
  exact congrArg (fun homomorphism : group →* ℤˣ => homomorphism element) trivial_sign

theorem alternating_four_solvable : Group.IsSolvable (alternatingGroup (Fin 4)) := by
  classical
  let klein_four := commutator (alternatingGroup (Fin 4))
  have card_four : Nat.card klein_four = 4 := by
    dsimp [klein_four]
    rw [← alternatingGroup.kleinFour_eq_commutator (by simp)]
    exact alternatingGroup.kleinFour_card_of_card_eq_four (by simp)
  have : Fact (Nat.Prime 2) := ⟨by decide⟩
  have : Group.IsNilpotent klein_four :=
    (IsPGroup.of_card (p := 2) (n := 2) (by simpa using card_four)).isNilpotent
  let _ : IsMulCommutative (alternatingGroup (Fin 4) ⧸ klein_four) :=
    Subgroup.Normal.quotient_commutative_iff_commutator_le.mpr le_rfl
  let _ : Group.IsSolvable (alternatingGroup (Fin 4) ⧸ klein_four) :=
    Group.isSolvable_of_comm (isMulCommutative_iff.mp inferInstance)
  apply (Group.isSolvable_iff_subgroup_quotient klein_four).mpr
  exact ⟨inferInstance, inferInstance⟩

theorem permutation_four_solvable : Group.IsSolvable (Equiv.Perm (Fin 4)) := by
  classical
  let := alternating_four_solvable
  have commutator_solvable : Group.IsSolvable (commutator (Equiv.Perm (Fin 4))) :=
    Group.isSolvable_of_isSolvable_injective
      (Subgroup.inclusion_injective alternatingGroup.commutator_perm_le)
  let := commutator_solvable
  let _ : IsMulCommutative
      (Equiv.Perm (Fin 4) ⧸ commutator (Equiv.Perm (Fin 4))) :=
    Subgroup.Normal.quotient_commutative_iff_commutator_le.mpr le_rfl
  let _ : Group.IsSolvable
      (Equiv.Perm (Fin 4) ⧸ commutator (Equiv.Perm (Fin 4))) :=
    Group.isSolvable_of_comm (isMulCommutative_iff.mp inferInstance)
  exact (Group.isSolvable_iff_subgroup_quotient (commutator (Equiv.Perm (Fin 4)))).mpr
    ⟨inferInstance, inferInstance⟩

theorem permutation_solvable_of_card_le_four (points : Type*) [Finite points]
    (small : Nat.card points ≤ 4) : Group.IsSolvable (Equiv.Perm points) := by
  classical
  let _ : Fintype points := Fintype.ofFinite points
  have card_bound : Fintype.card points ≤ Fintype.card (Fin 4) := by
    simpa only [Fintype.card_fin, Nat.card_eq_fintype_card] using small
  obtain ⟨embedding⟩ := Function.Embedding.nonempty_of_card_le card_bound
  let := permutation_four_solvable
  exact Group.isSolvable_of_isSolvable_injective
    (Equiv.Perm.viaEmbeddingHom_injective embedding)

theorem simple_prime_card_of_index_le_four (group : Type*) [Group group] [Finite group]
    [IsSimpleGroup group] (subgroup : Subgroup group) (proper : subgroup ≠ ⊤)
    (small_index : subgroup.index ≤ 4) : (Nat.card group).Prime := by
  have small_cosets : Nat.card (group ⧸ subgroup) ≤ 4 := by
    rwa [← subgroup.index_eq_card]
  let := permutation_solvable_of_card_le_four (group ⧸ subgroup) small_cosets
  let := Group.isSolvable_of_isSolvable_injective
    (simple_coset_action_injective group subgroup proper)
  exact CFSG.OrderReductions.Helpers.prime_card_of_simple_solvable group

theorem simple_card_mem_orders_of_index_le_four (group : Type*) [Group group]
    [Finite group] [IsSimpleGroup group] (subgroup : Subgroup group)
    (proper : subgroup ≠ ⊤) (small_index : subgroup.index ≤ 4) :
    Nat.card group ∈ cfsgOrders :=
  CFSG.OrderReductions.Helpers.mem_cfsgOrders_of_prime
    (simple_prime_card_of_index_le_four group subgroup proper small_index)

theorem simple_noncommutative_proper_subgroup_index_ge_five (group : Type*) [Group group]
    [Finite group] [IsSimpleGroup group] (noncommutative : ¬ IsMulCommutative group)
    (subgroup : Subgroup group) (proper : subgroup ≠ ⊤) : 5 ≤ subgroup.index := by
  by_contra small_index
  have prime_order := simple_prime_card_of_index_le_four group subgroup proper (by omega)
  have : Fact (Nat.card group).Prime := ⟨prime_order⟩
  have : IsCyclic group := isCyclic_of_prime_card (p := Nat.card group) rfl
  exact noncommutative inferInstance

theorem simple_noncommutative_sylow_not_normal (group : Type*) [Group group]
    [Finite group] [IsSimpleGroup group] (noncommutative : ¬ IsMulCommutative group)
    (prime : ℕ) [Fact prime.Prime] (divides : prime ∣ Nat.card group)
    (sylow : Sylow prime group) : ¬ (sylow : Subgroup group).Normal := by
  intro normal
  rcases CFSG.eq_bot_or_eq_top_of_normal (sylow : Subgroup group) normal with
    sylow_bot | sylow_top
  · exact sylow.ne_bot_of_dvd_card divides sylow_bot
  · have surjective : Function.Surjective (sylow : Subgroup group).subtype := by
      intro element
      exact ⟨⟨element, by rw [sylow_top]; trivial⟩, rfl⟩
    have p_group : IsPGroup prime group :=
      sylow.isPGroup'.of_surjective (sylow : Subgroup group).subtype surjective
    let := p_group.isNilpotent
    exact noncommutative (CFSG.OrderReductions.Helpers.simple_solvable_isMulCommutative group)

theorem simple_noncommutative_sylow_normalizer_ne_top (group : Type*) [Group group]
    [Finite group] [IsSimpleGroup group] (noncommutative : ¬ IsMulCommutative group)
    (prime : ℕ) [Fact prime.Prime] (divides : prime ∣ Nat.card group)
    (sylow : Sylow prime group) : Subgroup.normalizer (sylow : Set group) ≠ ⊤ := by
  intro normalizer_top
  exact simple_noncommutative_sylow_not_normal group noncommutative prime divides sylow
    (Subgroup.normalizer_eq_top_iff.mp normalizer_top)

theorem simple_noncommutative_sylow_card_ge_five (group : Type*) [Group group]
    [Finite group] [IsSimpleGroup group] (noncommutative : ¬ IsMulCommutative group)
    (prime : ℕ) [Fact prime.Prime] (divides : prime ∣ Nat.card group) :
    5 ≤ Nat.card (Sylow prime group) := by
  obtain ⟨sylow⟩ : Nonempty (Sylow prime group) := inferInstance
  rw [sylow.card_eq_index_normalizer]
  exact simple_noncommutative_proper_subgroup_index_ge_five group noncommutative _
    (simple_noncommutative_sylow_normalizer_ne_top group noncommutative prime divides sylow)

theorem simple_noncommutative_sylow_card_mul_five_le_card (group : Type*) [Group group]
    [Finite group] [IsSimpleGroup group] (noncommutative : ¬ IsMulCommutative group)
    (prime : ℕ) [Fact prime.Prime] (divides : prime ∣ Nat.card group)
    (sylow : Sylow prime group) : 5 * Nat.card sylow ≤ Nat.card group := by
  have proper : (sylow : Subgroup group) ≠ ⊤ := by
    intro sylow_top
    apply simple_noncommutative_sylow_not_normal group noncommutative prime divides sylow
    rw [sylow_top]
    infer_instance
  have index_bound :=
    simple_noncommutative_proper_subgroup_index_ge_five group noncommutative sylow proper
  have card_eq := (sylow : Subgroup group).card_mul_index
  nlinarith

theorem simple_noncommutative_card_dvd_alternating_order_of_index_bound
    (group : Type*) [Group group] [Finite group] [IsSimpleGroup group]
    (noncommutative : ¬ IsMulCommutative group) (subgroup : Subgroup group)
    (proper : subgroup ≠ ⊤) (degree : ℕ) (degree_bound : 5 ≤ degree)
    (index_bound : subgroup.index ≤ degree) :
    Nat.card group ∣ Nat.factorial degree / 2 := by
  classical
  let _ : Fintype (group ⧸ subgroup) := Fintype.ofFinite _
  let := CFSG.OrderReductions.Helpers.simple_noncommutative_isPerfect group noncommutative
  have coset_bound : Fintype.card (group ⧸ subgroup) ≤ Fintype.card (Fin degree) := by
    simpa only [subgroup.index_eq_card, Nat.card_eq_fintype_card, Fintype.card_fin] using
      index_bound
  obtain ⟨embedding⟩ := Function.Embedding.nonempty_of_card_le coset_bound
  let permutation_hom := (Equiv.Perm.viaEmbeddingHom embedding).comp
    (MulAction.toPermHom group (group ⧸ subgroup))
  have permutation_injective : Function.Injective permutation_hom :=
    (Equiv.Perm.viaEmbeddingHom_injective embedding).comp
      (simple_coset_action_injective group subgroup proper)
  let alternating_hom := permutation_hom.codRestrict (alternatingGroup (Fin degree))
    (perfect_perm_hom_mem_alternating group (Fin degree) permutation_hom)
  have alternating_injective : Function.Injective alternating_hom := by
    intro first second equal_images
    exact permutation_injective (congrArg Subtype.val equal_images)
  have card_dvd := Subgroup.card_dvd_of_injective alternating_hom alternating_injective
  have : Nontrivial (Fin degree) := Fin.nontrivial_iff_two_le.mpr (by omega)
  rwa [nat_card_alternatingGroup, Nat.card_fin] at card_dvd

theorem simple_noncommutative_card_eq_sixty_of_dvd_sixty (group : Type*) [Group group]
    [Finite group] [IsSimpleGroup group] (noncommutative : ¬ IsMulCommutative group)
    (card_dvd : Nat.card group ∣ 60) : Nat.card group = 60 := by
  have not_squarefree : ¬ Squarefree (Nat.card group) := by
    intro squarefree_order
    have prime_order := CFSG.OrderReductions.Helpers.prime_card_of_simple_squarefree group squarefree_order
    have : Fact (Nat.card group).Prime := ⟨prime_order⟩
    have : IsCyclic group := isCyclic_of_prime_card (p := Nat.card group) rfl
    exact noncommutative inferInstance
  have not_prime_power : ¬ IsPrimePow (Nat.card group) := by
    intro prime_power
    have prime_order := CFSG.OrderReductions.Helpers.prime_card_of_simple_prime_power group prime_power
    have : Fact (Nat.card group).Prime := ⟨prime_order⟩
    have : IsCyclic group := isCyclic_of_prime_card (p := Nat.card group) rfl
    exact noncommutative inferInstance
  have squarefree_thirty : Squarefree (30 : ℕ) := by
    have squarefree_three : Squarefree (3 : ℕ) :=
      (Nat.prime_iff.mp (by decide : Nat.Prime 3)).squarefree
    have squarefree_five : Squarefree (5 : ℕ) :=
      (Nat.prime_iff.mp (by decide : Nat.Prime 5)).squarefree
    have squarefree_six : Squarefree (6 : ℕ) :=
      Nat.squarefree_mul_iff.mpr ⟨by decide, Nat.squarefree_two, squarefree_three⟩
    exact Nat.squarefree_mul_iff.mpr ⟨by decide, squarefree_six, squarefree_five⟩
  have divisor : Nat.card group ∈ (60 : ℕ).divisors :=
    Nat.mem_divisors.mpr ⟨card_dvd, by decide⟩
  have divisors_eq : (60 : ℕ).divisors = {1, 2, 3, 4, 5, 6, 10, 12, 15, 20, 30, 60} := by
    decide
  simp only [divisors_eq, Finset.mem_insert, Finset.mem_singleton] at divisor
  rcases divisor with card_eq | card_eq | card_eq | card_eq | card_eq | card_eq |
    card_eq | card_eq | card_eq | card_eq | card_eq | card_eq
  all_goals
    try solve | exact False.elim (not_squarefree (by
      apply squarefree_thirty.squarefree_of_dvd
      rw [card_eq]
      decide))
  all_goals
    try solve | exact False.elim (not_squarefree (by simpa only [card_eq] using squarefree_thirty))
  all_goals
    try solve | exact False.elim (not_prime_power (by
      rw [card_eq, isPrimePow_nat_iff_bounded_log_minFac]
      decide))
  all_goals
    try exact card_eq
  all_goals
    first
    | have card_twelve : Nat.card group = 12 := card_eq
      have : Fact (Nat.Prime 3) := ⟨by decide⟩
      obtain ⟨sylow⟩ : Nonempty (Sylow 3 group) := inferInstance
      have exponent_eq : (Nat.card group).factorization 3 = 1 := by
        have prime_three : Nat.Prime 3 := by decide
        have positive := prime_three.factorization_pos_of_dvd Nat.card_pos.ne'
          (show 3 ∣ Nat.card group by rw [card_twelve]; decide)
        have not_two_le : ¬ 2 ≤ (Nat.card group).factorization 3 := by
          rw [← prime_three.pow_dvd_iff_le_factorization Nat.card_pos.ne', card_twelve]
          decide
        omega
      have sylow_card : Nat.card sylow = 3 := by
        simpa only [exponent_eq, pow_one] using sylow.card_eq_multiplicity
      have bound := simple_noncommutative_sylow_card_mul_five_le_card group noncommutative
        3 (by rw [card_twelve]; decide) sylow
      omega
    | have card_twenty : Nat.card group = 20 := card_eq
      have : Fact (Nat.Prime 5) := ⟨by decide⟩
      obtain ⟨sylow⟩ : Nonempty (Sylow 5 group) := inferInstance
      have exponent_eq : (Nat.card group).factorization 5 = 1 := by
        have prime_five : Nat.Prime 5 := by decide
        have positive := prime_five.factorization_pos_of_dvd Nat.card_pos.ne'
          (show 5 ∣ Nat.card group by rw [card_twenty]; decide)
        have not_two_le : ¬ 2 ≤ (Nat.card group).factorization 5 := by
          rw [← prime_five.pow_dvd_iff_le_factorization Nat.card_pos.ne', card_twenty]
          decide
        omega
      have sylow_card : Nat.card sylow = 5 := by
        simpa only [exponent_eq, pow_one] using sylow.card_eq_multiplicity
      have bound := simple_noncommutative_sylow_card_mul_five_le_card group noncommutative
        5 (by rw [card_twenty]; decide) sylow
      omega

theorem simple_card_mem_orders_of_index_le_five (group : Type*) [Group group]
    [Finite group] [IsSimpleGroup group] (subgroup : Subgroup group)
    (proper : subgroup ≠ ⊤) (small_index : subgroup.index ≤ 5) :
    Nat.card group ∈ cfsgOrders := by
  classical
  by_cases commutative : IsMulCommutative group
  · have := commutative
    exact CFSG.OrderReductions.Helpers.card_mem_cfsgOrders_of_simple_commutative group
  · have card_dvd : Nat.card group ∣ 60 := by
      simpa only [show Nat.factorial 5 / 2 = 60 by decide] using
        simple_noncommutative_card_dvd_alternating_order_of_index_bound
        group commutative subgroup proper 5 (by decide) small_index
    apply CFSG.OrderReductions.Helpers.mem_cfsgOrders_of_alternating (degree := 5) (by decide)
    simpa only [show Nat.factorial 5 / 2 = 60 by decide] using
      simple_noncommutative_card_eq_sixty_of_dvd_sixty group commutative card_dvd

theorem simple_card_dvd_card_or_index_gt_four (group : Type*) [Group group] [Finite group]
    [IsSimpleGroup group] (nonprime_order : ¬ (Nat.card group).Prime)
    (subgroup : Subgroup group) : subgroup = ⊤ ∨ 5 ≤ subgroup.index := by
  classical
  by_cases proper : subgroup = ⊤
  · exact Or.inl proper
  · right
    by_contra small
    exact nonprime_order (simple_prime_card_of_index_le_four group subgroup proper (by omega))

theorem simple_noncommutative_sylow_card_constraints (group : Type*) [Group group]
    [Finite group] [IsSimpleGroup group] (noncommutative : ¬ IsMulCommutative group)
    (prime : ℕ) [Fact prime.Prime] (divides : prime ∣ Nat.card group) :
    5 ≤ Nat.card (Sylow prime group) ∧
      Nat.card (Sylow prime group) * prime ^ (Nat.card group).factorization prime ∣
        Nat.card group ∧ Nat.card (Sylow prime group) % prime = 1 % prime := by
  obtain ⟨sylow⟩ : Nonempty (Sylow prime group) := inferInstance
  refine ⟨simple_noncommutative_sylow_card_ge_five group noncommutative prime divides, ?_,
    card_sylow_modEq_one prime group⟩
  have divides_index := sylow.card_dvd_index
  have multiply_divides := mul_dvd_mul_left (Nat.card sylow) divides_index
  rw [← sylow.card_eq_multiplicity, mul_comm (Nat.card (Sylow prime group))]
  rwa [(sylow : Subgroup group).card_mul_index] at multiply_divides

theorem simple_noncommutative_small_order_of_dvd_360 (group : Type*) [Group group]
    [Finite group] [IsSimpleGroup group] (noncommutative : ¬ IsMulCommutative group)
    (card_dvd : Nat.card group ∣ 360) :
    Nat.card group = 60 ∨ 72 ≤ Nat.card group := by
  have divisor : Nat.card group ∈ (360 : ℕ).divisors :=
    Nat.mem_divisors.mpr ⟨card_dvd, by decide⟩
  have small_order : Nat.card group = 1 ∨ Nat.card group = 2 ∨ Nat.card group = 3 ∨
      Nat.card group = 4 ∨ Nat.card group = 5 ∨ Nat.card group = 6 ∨ Nat.card group = 8 ∨
      Nat.card group = 9 ∨ Nat.card group = 10 ∨ Nat.card group = 12 ∨ Nat.card group = 15 ∨
      Nat.card group = 18 ∨ Nat.card group = 20 ∨ Nat.card group = 24 ∨
      Nat.card group = 30 ∨ Nat.card group = 36 ∨ Nat.card group = 40 ∨
      Nat.card group = 45 ∨ Nat.card group = 60 ∨ 72 ≤ Nat.card group := by
    have divisors_eq : (360 : ℕ).divisors =
        {1, 2, 3, 4, 5, 6, 8, 9, 10, 12, 15, 18, 20, 24, 30, 36, 40, 45,
          60, 72, 90, 120, 180, 360} := by decide
    simp only [divisors_eq, Finset.mem_insert, Finset.mem_singleton] at divisor
    omega
  have squarefree_thirty : Squarefree (30 : ℕ) := by
    have squarefree_three : Squarefree (3 : ℕ) :=
      (Nat.prime_iff.mp (by decide : Nat.Prime 3)).squarefree
    have squarefree_five : Squarefree (5 : ℕ) :=
      (Nat.prime_iff.mp (by decide : Nat.Prime 5)).squarefree
    have squarefree_six : Squarefree (6 : ℕ) :=
      Nat.squarefree_mul_iff.mpr ⟨by decide, Nat.squarefree_two, squarefree_three⟩
    exact Nat.squarefree_mul_iff.mpr ⟨by decide, squarefree_six, squarefree_five⟩
  have not_squarefree : ¬ Squarefree (Nat.card group) := by
    intro squarefree_order
    have prime_order := CFSG.OrderReductions.Helpers.prime_card_of_simple_squarefree group squarefree_order
    have : Fact (Nat.card group).Prime := ⟨prime_order⟩
    have : IsCyclic group := isCyclic_of_prime_card (p := Nat.card group) rfl
    exact noncommutative inferInstance
  have not_prime_power : ¬ IsPrimePow (Nat.card group) := by
    intro prime_power
    have prime_order := CFSG.OrderReductions.Helpers.prime_card_of_simple_prime_power group prime_power
    have : Fact (Nat.card group).Prime := ⟨prime_order⟩
    have : IsCyclic group := isCyclic_of_prime_card (p := Nat.card group) rfl
    exact noncommutative inferInstance
  rcases small_order with card_eq | card_eq | card_eq | card_eq | card_eq | card_eq |
    card_eq | card_eq | card_eq | card_eq | card_eq | card_eq | card_eq | card_eq |
    card_eq | card_eq | card_eq | card_eq | card_eq | large
  all_goals try solve | exact Or.inr large
  all_goals try solve | exact Or.inl card_eq
  all_goals try solve | exact False.elim (not_squarefree (by
    apply squarefree_thirty.squarefree_of_dvd
    rw [card_eq]
    decide))
  all_goals try solve | exact False.elim (not_squarefree (by
    simpa only [card_eq] using squarefree_thirty))
  all_goals try solve | exact False.elim (not_prime_power (by
    rw [card_eq, isPrimePow_nat_iff_bounded_log_minFac]
    decide))
  all_goals try solve |
    have card_dvd_sixty : Nat.card group ∣ 60 := by rw [card_eq]; decide
    exact Or.inl (simple_noncommutative_card_eq_sixty_of_dvd_sixty group noncommutative
      card_dvd_sixty)
  all_goals try solve |
    have minimum_square :=
      CFSG.OrderReductions.Helpers.simple_noncommutative_minFac_sq_dvd_card group noncommutative
    rw [card_eq] at minimum_square
    norm_num [Nat.minFac] at minimum_square
  all_goals
    first
    | have prime : Fact (Nat.Prime 3) := ⟨by decide⟩
      obtain ⟨sylow⟩ : Nonempty (Sylow 3 group) := inferInstance
      have p_square_dvd : 3 ^ 2 ∣ Nat.card group := by rw [card_eq]; decide
      have sylow_square := sylow.pow_dvd_card_of_pow_dvd_card p_square_dvd
      have sylow_bound : 9 ≤ Nat.card sylow := Nat.le_of_dvd Nat.card_pos sylow_square
      have group_bound := simple_noncommutative_sylow_card_mul_five_le_card group
        noncommutative 3 (by rw [card_eq]; decide) sylow
      omega
    | have prime : Fact (Nat.Prime 3) := ⟨by decide⟩
      obtain ⟨sylow⟩ : Nonempty (Sylow 3 group) := inferInstance
      have sylow_card_eq : Nat.card sylow = 3 := by
        have prime_three : Nat.Prime 3 := by decide
        have positive := prime_three.factorization_pos_of_dvd Nat.card_pos.ne'
          (show 3 ∣ Nat.card group by rw [card_eq]; decide)
        have not_two_le : ¬ 2 ≤ (Nat.card group).factorization 3 := by
          rw [← prime_three.pow_dvd_iff_le_factorization Nat.card_pos.ne', card_eq]
          decide
        have exponent_one : (Nat.card group).factorization 3 = 1 := by omega
        simpa only [exponent_one, pow_one] using sylow.card_eq_multiplicity
      obtain ⟨count_bound, count_dvd, count_mod⟩ :=
        simple_noncommutative_sylow_card_constraints group noncommutative 3
          (by rw [card_eq]; decide)
      rw [← sylow.card_eq_multiplicity, sylow_card_eq, card_eq] at count_dvd
      have count_le : Nat.card (Sylow 3 group) ≤ 8 := by
        have product_bound := Nat.le_of_dvd (by rw [card_eq]; decide : 0 < Nat.card group)
          (by rwa [card_eq] : Nat.card (Sylow 3 group) * 3 ∣ Nat.card group)
        rw [card_eq] at product_bound
        omega
      interval_cases count_eq : Nat.card (Sylow 3 group) <;> omega
    | have prime : Fact (Nat.Prime 5) := ⟨by decide⟩
      obtain ⟨sylow⟩ : Nonempty (Sylow 5 group) := inferInstance
      have sylow_card_eq : Nat.card sylow = 5 := by
        have prime_five : Nat.Prime 5 := by decide
        have positive := prime_five.factorization_pos_of_dvd Nat.card_pos.ne'
          (show 5 ∣ Nat.card group by rw [card_eq]; decide)
        have not_two_le : ¬ 2 ≤ (Nat.card group).factorization 5 := by
          rw [← prime_five.pow_dvd_iff_le_factorization Nat.card_pos.ne', card_eq]
          decide
        have exponent_one : (Nat.card group).factorization 5 = 1 := by omega
        simpa only [exponent_one, pow_one] using sylow.card_eq_multiplicity
      obtain ⟨count_bound, count_dvd, count_mod⟩ :=
        simple_noncommutative_sylow_card_constraints group noncommutative 5
          (by rw [card_eq]; decide)
      rw [← sylow.card_eq_multiplicity, sylow_card_eq, card_eq] at count_dvd
      have count_le : Nat.card (Sylow 5 group) ≤ 8 := by
        have product_bound := Nat.le_of_dvd (by rw [card_eq]; decide : 0 < Nat.card group)
          (by rwa [card_eq] : Nat.card (Sylow 5 group) * 5 ∣ Nat.card group)
        rw [card_eq] at product_bound
        omega
      interval_cases count_eq : Nat.card (Sylow 5 group) <;> omega

theorem simple_noncommutative_not_card_72 (group : Type*) [Group group] [Finite group]
    [IsSimpleGroup group] (noncommutative : ¬ IsMulCommutative group) :
    Nat.card group ≠ 72 := by
  intro card_eq
  have : Fact (Nat.Prime 3) := ⟨by decide⟩
  obtain ⟨sylow⟩ : Nonempty (Sylow 3 group) := inferInstance
  have prime_three : Nat.Prime 3 := by decide
  have exponent_two : (Nat.card group).factorization 3 = 2 := by
    have two_le : 2 ≤ (Nat.card group).factorization 3 :=
      (prime_three.pow_dvd_iff_le_factorization Nat.card_pos.ne').mp
        (by rw [card_eq]; decide)
    have not_three_le : ¬ 3 ≤ (Nat.card group).factorization 3 := by
      rw [← prime_three.pow_dvd_iff_le_factorization Nat.card_pos.ne', card_eq]
      decide
    omega
  have sylow_card : Nat.card sylow = 9 := by
    simpa only [exponent_two, show (3 : ℕ) ^ 2 = 9 by decide] using sylow.card_eq_multiplicity
  obtain ⟨count_lower, count_dvd, count_mod⟩ :=
    simple_noncommutative_sylow_card_constraints group noncommutative 3
      (by rw [card_eq]; decide)
  rw [exponent_two] at count_dvd
  have count_dvd_eight : Nat.card (Sylow 3 group) ∣ 8 := by
    apply (Nat.mul_dvd_mul_iff_right (by decide : 0 < (9 : ℕ))).mp
    simpa only [show (3 : ℕ) ^ 2 = 9 by decide, card_eq,
      show (8 : ℕ) * 9 = 72 by decide] using count_dvd
  have count_upper : Nat.card (Sylow 3 group) ≤ 8 := Nat.le_of_dvd (by decide) count_dvd_eight
  interval_cases count_eq : Nat.card (Sylow 3 group) <;> omega

theorem simple_card_sixty_or_360_of_embedding_alternating_six (group : Type*)
    [Group group] [Finite group] [IsSimpleGroup group]
    (noncommutative : ¬ IsMulCommutative group)
    (homomorphism : group →* alternatingGroup (Fin 6))
    (injective : Function.Injective homomorphism) :
    Nat.card group = 60 ∨ Nat.card group = 360 := by
  classical
  let equivalence := MulEquiv.ofBijective homomorphism.rangeRestrict
    ⟨MonoidHom.rangeRestrict_injective_iff.mpr injective, homomorphism.rangeRestrict_surjective⟩
  have range_card : Nat.card homomorphism.range = Nat.card group :=
    (Nat.card_congr equivalence.toEquiv).symm
  have ambient_card : Nat.card (alternatingGroup (Fin 6)) = 360 := by
    rw [nat_card_alternatingGroup, Nat.card_fin]
    decide
  let _ : IsSimpleGroup (alternatingGroup (Fin 6)) :=
    alternatingGroup.isSimpleGroup (by simp)
  have card_dvd : Nat.card group ∣ 360 := by
    simpa only [ambient_card] using Subgroup.card_dvd_of_injective homomorphism injective
  by_cases range_top : homomorphism.range = ⊤
  · right
    rw [← range_card, range_top, Subgroup.card_top, ambient_card]
  · have ambient_noncommutative : ¬ IsMulCommutative (alternatingGroup (Fin 6)) := by
      intro commutative
      let := commutative
      have prime_order := CFSG.OrderReductions.Helpers.prime_card_of_simple_commutative
        (alternatingGroup (Fin 6))
      rw [ambient_card] at prime_order
      norm_num at prime_order
    have index_lower := simple_noncommutative_proper_subgroup_index_ge_five
      (alternatingGroup (Fin 6)) ambient_noncommutative homomorphism.range range_top
    have card_index := homomorphism.range.card_mul_index
    rw [range_card, ambient_card] at card_index
    have card_upper : Nat.card group ≤ 72 := by nlinarith
    rcases simple_noncommutative_small_order_of_dvd_360 group noncommutative card_dvd with
      card_sixty | card_lower
    · exact Or.inl card_sixty
    · exact False.elim (simple_noncommutative_not_card_72 group noncommutative (by omega))

theorem simple_card_mem_orders_of_index_le_six (group : Type*) [Group group]
    [Finite group] [IsSimpleGroup group] (subgroup : Subgroup group)
    (proper : subgroup ≠ ⊤) (small_index : subgroup.index ≤ 6) :
    Nat.card group ∈ cfsgOrders := by
  classical
  by_cases commutative : IsMulCommutative group
  · let := commutative
    exact CFSG.OrderReductions.Helpers.card_mem_cfsgOrders_of_simple_commutative group
  · let _ : Fintype (group ⧸ subgroup) := Fintype.ofFinite _
    let := CFSG.OrderReductions.Helpers.simple_noncommutative_isPerfect group commutative
    have coset_bound : Fintype.card (group ⧸ subgroup) ≤ Fintype.card (Fin 6) := by
      simpa only [subgroup.index_eq_card, Nat.card_eq_fintype_card, Fintype.card_fin] using
        small_index
    obtain ⟨embedding⟩ := Function.Embedding.nonempty_of_card_le coset_bound
    let permutation_hom := (Equiv.Perm.viaEmbeddingHom embedding).comp
      (MulAction.toPermHom group (group ⧸ subgroup))
    have permutation_injective : Function.Injective permutation_hom :=
      (Equiv.Perm.viaEmbeddingHom_injective embedding).comp
        (simple_coset_action_injective group subgroup proper)
    let alternating_hom := permutation_hom.codRestrict (alternatingGroup (Fin 6))
      (perfect_perm_hom_mem_alternating group (Fin 6) permutation_hom)
    have alternating_injective : Function.Injective alternating_hom := by
      intro first second equal_images
      exact permutation_injective (congrArg Subtype.val equal_images)
    rcases simple_card_sixty_or_360_of_embedding_alternating_six group commutative
      alternating_hom alternating_injective with card_sixty | card_360
    · exact CFSG.OrderReductions.Helpers.mem_cfsgOrders_of_alternating (degree := 5) (by decide)
        (by simpa only [show Nat.factorial 5 / 2 = 60 by decide] using card_sixty)
    · exact CFSG.OrderReductions.Helpers.mem_cfsgOrders_of_alternating (degree := 6) (by decide)
        (by simpa only [show Nat.factorial 6 / 2 = 360 by decide] using card_360)

end CFSG.OrderReductions.PermutationReduction

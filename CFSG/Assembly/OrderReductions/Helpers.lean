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

public section

open CFSG.Open

namespace CFSG.OrderReductions.Helpers

theorem mem_cfsgOrders_of_prime {order : ℕ} (prime_order : order.Prime) :
    order ∈ cfsgOrders := by
  simp only [cfsgOrders, Set.mem_union, Set.mem_ofPred_eq]
  tauto

theorem mem_cfsgOrders_of_alternating {order degree : ℕ} (degree_bound : 5 ≤ degree)
    (order_eq : order = Nat.factorial degree / 2) : order ∈ cfsgOrders := by
  have alternating_order : ∃ degree : ℕ, 5 ≤ degree ∧ order = Nat.factorial degree / 2 :=
    ⟨degree, degree_bound, order_eq⟩
  simp only [cfsgOrders, Set.mem_union, Set.mem_ofPred_eq]
  iterate 10 apply Or.inl
  exact Or.inr alternating_order

theorem card_mem_cfsgOrders_of_mulEquiv {source : Type*} {target : Type*}
    [Group source] [Group target] (equivalence : source ≃* target)
    (target_order : Nat.card target ∈ cfsgOrders) : Nat.card source ∈ cfsgOrders := by
  rw [Nat.card_congr equivalence.toEquiv]
  exact target_order

theorem prime_card_of_simple_commutative (group : Type*) [Group group]
    [IsSimpleGroup group] [IsMulCommutative group] : (Nat.card group).Prime :=
  Group.is_simple_iff_prime_card.mp inferInstance

theorem card_mem_cfsgOrders_of_simple_commutative (group : Type*) [Group group]
    [IsSimpleGroup group] [IsMulCommutative group] : Nat.card group ∈ cfsgOrders :=
  mem_cfsgOrders_of_prime (prime_card_of_simple_commutative group)

theorem simple_solvable_isMulCommutative (group : Type*) [Group group]
    [IsSimpleGroup group] [Group.IsSolvable group] : IsMulCommutative group :=
  IsMulCommutative.of_comm (IsSimpleGroup.comm_iff_isSolvable.mpr inferInstance)

theorem prime_card_of_simple_solvable (group : Type*) [Group group]
    [IsSimpleGroup group] [Group.IsSolvable group] : (Nat.card group).Prime := by
  let := simple_solvable_isMulCommutative group
  exact prime_card_of_simple_commutative group

theorem card_mem_cfsgOrders_of_simple_solvable (group : Type*) [Group group]
    [IsSimpleGroup group] [Group.IsSolvable group] : Nat.card group ∈ cfsgOrders :=
  mem_cfsgOrders_of_prime (prime_card_of_simple_solvable group)

theorem card_mem_cfsgOrders_alternating (degree : ℕ) (degree_bound : 5 ≤ degree) :
    Nat.card (alternatingGroup (Fin degree)) ∈ cfsgOrders := by
  have : Nontrivial (Fin degree) := Fin.nontrivial_iff_two_le.mpr (by omega)
  apply mem_cfsgOrders_of_alternating degree_bound
  simpa using (nat_card_alternatingGroup (α := Fin degree))

theorem card_mem_cfsgOrders_of_alternating_equiv (group : Type*) [Group group]
    (degree : ℕ) (degree_bound : 5 ≤ degree)
    (equivalence : group ≃* alternatingGroup (Fin degree)) : Nat.card group ∈ cfsgOrders :=
  card_mem_cfsgOrders_of_mulEquiv equivalence
    (card_mem_cfsgOrders_alternating degree degree_bound)

theorem simple_noncommutative_isPerfect (group : Type*) [Group group]
    [IsSimpleGroup group] (noncommutative : ¬ IsMulCommutative group) :
    Group.IsPerfect group := by
  apply Group.IsPerfect.mk
  rcases CFSG.eq_bot_or_eq_top_of_normal (commutator group) inferInstance with
    commutator_bot | commutator_top
  · exact False.elim (noncommutative ((commutator_eq_bot_iff group).mp commutator_bot))
  · exact commutator_top

theorem simple_noncommutative_center_eq_bot (group : Type*) [Group group]
    [IsSimpleGroup group] (noncommutative : ¬ IsMulCommutative group) :
    Subgroup.center group = ⊥ := by
  rcases CFSG.eq_bot_or_eq_top_of_normal (Subgroup.center group) inferInstance with
    center_bot | center_top
  · exact center_bot
  · exact False.elim (noncommutative (Subgroup.center_eq_top_iff.mp center_top))

theorem simple_noncommutative_not_solvable (group : Type*) [Group group]
    [IsSimpleGroup group] (noncommutative : ¬ IsMulCommutative group) :
    ¬ Group.IsSolvable group := by
  intro solvable
  have := solvable
  exact noncommutative (simple_solvable_isMulCommutative group)

theorem prime_card_of_simple_prime_power (group : Type*) [Group group] [Finite group]
    [IsSimpleGroup group] (prime_power_order : IsPrimePow (Nat.card group)) :
    (Nat.card group).Prime := by
  obtain ⟨prime, exponent, prime_prime, _, order_eq⟩ :=
    (isPrimePow_nat_iff (Nat.card group)).mp prime_power_order
  have : Fact prime.Prime := ⟨prime_prime⟩
  have : Group.IsNilpotent group := (IsPGroup.of_card order_eq.symm).isNilpotent
  exact prime_card_of_simple_solvable group

theorem card_mem_cfsgOrders_of_simple_prime_power (group : Type*) [Group group]
    [Finite group] [IsSimpleGroup group] (prime_power_order : IsPrimePow (Nat.card group)) :
    Nat.card group ∈ cfsgOrders :=
  mem_cfsgOrders_of_prime (prime_card_of_simple_prime_power group prime_power_order)

theorem prime_card_of_simple_squarefree (group : Type*) [Group group] [Finite group]
    [IsSimpleGroup group] (squarefree_order : Squarefree (Nat.card group)) :
    (Nat.card group).Prime := by
  let := IsZGroup.of_squarefree squarefree_order
  exact prime_card_of_simple_solvable group

theorem card_mem_cfsgOrders_of_simple_squarefree (group : Type*) [Group group]
    [Finite group] [IsSimpleGroup group] (squarefree_order : Squarefree (Nat.card group)) :
    Nat.card group ∈ cfsgOrders :=
  mem_cfsgOrders_of_prime (prime_card_of_simple_squarefree group squarefree_order)

theorem perfect_hom_to_commutative_eq_one (group : Type*) [Group group]
    [Group.IsPerfect group] (target : Type*) [CommGroup target]
    (homomorphism : group →* target) : homomorphism = 1 := by
  apply MonoidHom.ker_eq_top_iff.mp
  exact top_unique (by
    rw [← Group.IsPerfect.commutator_eq_top (G := group)]
    exact Abelianization.commutator_subset_ker homomorphism)

theorem perfect_minFac_sylow_not_cyclic (group : Type*) [Group group] [Finite group]
    [Nontrivial group] [Group.IsPerfect group]
    (sylow : Sylow (Nat.card group).minFac group) :
    ¬ IsCyclic sylow := by
  intro cyclic
  have order_ne_one : Nat.card group ≠ 1 := by
    intro order_one
    have := (Nat.card_eq_one_iff_unique.mp order_one).1
    exact not_subsingleton group inferInstance
  have prime : (Nat.card group).minFac.Prime := Nat.minFac_prime order_ne_one
  have : Fact (Nat.card group).minFac.Prime := ⟨prime⟩
  let normalizer_inclusion := cyclic.normalizer_le_centralizer rfl
  let transfer := MonoidHom.transferSylow sylow normalizer_inclusion
  let := cyclic
  let _ : CommGroup sylow := IsMulCommutative.instCommGroup
  have transfer_trivial : transfer = 1 :=
    perfect_hom_to_commutative_eq_one group sylow transfer
  have kernel_top : transfer.ker = ⊤ := MonoidHom.ker_eq_top_iff.mpr transfer_trivial
  have not_dvd_kernel := MonoidHom.not_dvd_card_ker_transferSylow sylow normalizer_inclusion
  apply not_dvd_kernel
  change (Nat.card group).minFac ∣ Nat.card transfer.ker
  rw [kernel_top, Nat.card_congr (Subgroup.topEquiv : (⊤ : Subgroup group) ≃* group).toEquiv]
  exact Nat.minFac_dvd (Nat.card group)

theorem perfect_minFac_sq_dvd_card (group : Type*) [Group group] [Finite group]
    [Nontrivial group] [Group.IsPerfect group] :
    (Nat.card group).minFac ^ 2 ∣ Nat.card group := by
  have order_ne_one : Nat.card group ≠ 1 := by
    intro order_one
    have := (Nat.card_eq_one_iff_unique.mp order_one).1
    exact not_subsingleton group inferInstance
  have prime : (Nat.card group).minFac.Prime := Nat.minFac_prime order_ne_one
  have : Fact (Nat.card group).minFac.Prime := ⟨prime⟩
  have exponent_pos : 0 < (Nat.card group).factorization (Nat.card group).minFac :=
    prime.factorization_pos_of_dvd Nat.card_pos.ne' (Nat.minFac_dvd (Nat.card group))
  apply (prime.pow_dvd_iff_le_factorization Nat.card_pos.ne').mpr
  by_contra exponent_small
  have exponent_one : (Nat.card group).factorization (Nat.card group).minFac = 1 := by
    omega
  obtain ⟨sylow⟩ : Nonempty (Sylow (Nat.card group).minFac group) := inferInstance
  apply perfect_minFac_sylow_not_cyclic group sylow
  apply isCyclic_of_prime_card (p := (Nat.card group).minFac)
  simpa only [exponent_one, pow_one] using sylow.card_eq_multiplicity

theorem simple_noncommutative_minFac_sylow_not_cyclic (group : Type*) [Group group]
    [Finite group] [IsSimpleGroup group] (noncommutative : ¬ IsMulCommutative group)
    (sylow : Sylow (Nat.card group).minFac group) : ¬ IsCyclic sylow := by
  let := simple_noncommutative_isPerfect group noncommutative
  exact perfect_minFac_sylow_not_cyclic group sylow

theorem simple_noncommutative_minFac_sq_dvd_card (group : Type*) [Group group]
    [Finite group] [IsSimpleGroup group] (noncommutative : ¬ IsMulCommutative group) :
    (Nat.card group).minFac ^ 2 ∣ Nat.card group := by
  let := simple_noncommutative_isPerfect group noncommutative
  exact perfect_minFac_sq_dvd_card group

theorem simple_noncommutative_four_dvd_card_of_even (group : Type*) [Group group]
    [Finite group] [IsSimpleGroup group] (noncommutative : ¬ IsMulCommutative group)
    (even_order : Even (Nat.card group)) : 4 ∣ Nat.card group := by
  have minFac_two : (Nat.card group).minFac = 2 :=
    (Nat.minFac_eq_two_iff (Nat.card group)).mpr even_order.two_dvd
  simpa only [minFac_two, show (2 : ℕ) ^ 2 = 4 by decide] using
    simple_noncommutative_minFac_sq_dvd_card group noncommutative

theorem card_mem_cfsgOrders_of_simple_even_not_four_dvd (group : Type*) [Group group]
    [Finite group] [IsSimpleGroup group] (even_order : Even (Nat.card group))
    (not_four_dvd : ¬ 4 ∣ Nat.card group) : Nat.card group ∈ cfsgOrders := by
  classical
  by_cases commutative : IsMulCommutative group
  · have := commutative
    exact card_mem_cfsgOrders_of_simple_commutative group
  · exact False.elim (not_four_dvd
      (simple_noncommutative_four_dvd_card_of_even group commutative even_order))

end CFSG.OrderReductions.Helpers

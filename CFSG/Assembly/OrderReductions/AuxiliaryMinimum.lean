module

public import CFSG.Assembly.OrderReductions.OutsideCentralizer

public section

namespace CFSG.OrderReductions.AuxiliaryMinimum

open CFSG.OrderReductions.InvolutionGraph
open CFSG.OrderReductions.NormalizerAuxiliary
open CFSG.OrderReductions.PrimeComplementCore
open CFSG.OrderReductions.InvolutiveIntersection
open CFSG.OrderReductions.PrimeRegular

theorem inversionSet_card_eq_orbit {group : Type*} [Group group] [Finite group]
    (subgroup : Subgroup group) (odd_subgroup : Odd (Nat.card subgroup))
    (involution : Involution group)
    (normalizes : involution.val ∈ Subgroup.normalizer (subgroup : Set group)) :
    Nat.card (inversionSet subgroup involution) = Nat.card (MulAction.orbit subgroup involution) := by
  have invariant : subgroup.map (MulAut.conj involution.val).toMonoidHom = subgroup :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp normalizes
  let automorphism := CFSG.OrderReductions.InvariantSylow.restrictedAutomorphism
    (MulAut.conj involution.val) subgroup invariant
  let equivalence : inversionSet subgroup involution ≃ CFSG.OrderReductions.OddInversion.InvertedElements automorphism :=
    { toFun := fun element => ⟨⟨element.val, element.property.1⟩, Subtype.ext element.property.2⟩
      invFun := fun element => ⟨element.val.val, element.val.property,
        congrArg Subtype.val element.property⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  rw [Nat.card_congr equivalence, CFSG.OrderReductions.OddInversion.inverted_card_eq_fixed_index automorphism
    (CFSG.OrderReductions.InvariantSylow.restrictedAutomorphism_involutive _
      (involution_conjugation_involutive involution) subgroup invariant) odd_subgroup]
  have fixed_eq : CFSG.OrderReductions.OddInversion.fixedSubgroup automorphism =
      (Subgroup.centralizer ({involution.val} : Set group)).subgroupOf subgroup := by
    ext element
    change automorphism element = element ↔ element.val ∈ Subgroup.centralizer ({involution.val} : Set group)
    rw [← involution_fixedSubgroup_eq_centralizer]
    change automorphism element = element ↔ (MulAut.conj involution.val) element.val = element.val
    exact Subtype.ext_iff
  rw [fixed_eq, ← involution_fixedSubgroup_eq_centralizer]
  exact involution_fixedIndex_eq_orbit_card subgroup involution

theorem inverted_closure_invariant {group : Type*} [Group group]
    (subgroup : Subgroup group) (involution : Involution group)
    (normalizes : involution.val ∈ Subgroup.normalizer (subgroup : Set group)) :
    (Subgroup.closure (inversionSet subgroup involution)).map
      (MulAut.conj involution.val).toMonoidHom = Subgroup.closure (inversionSet subgroup involution) := by
  rw [MonoidHom.map_closure]
  change Subgroup.closure ((MulAut.conj involution.val) '' inversionSet subgroup involution) = _
  rw [CFSG.OrderReductions.OutsideCentralizer.inversionSet_invariant subgroup involution normalizes]

theorem inversionSet_closure_eq {group : Type*} [Group group]
    (subgroup : Subgroup group) (involution : Involution group) :
    inversionSet (Subgroup.closure (inversionSet subgroup involution)) involution =
      inversionSet subgroup involution := by
  have closure_le : Subgroup.closure (inversionSet subgroup involution) ≤ subgroup :=
    (Subgroup.closure_le _).mpr fun element element_mem => element_mem.1
  apply Set.Subset.antisymm
  · intro element element_mem
    exact ⟨closure_le element_mem.1, element_mem.2⟩
  · intro element element_mem
    exact ⟨Subgroup.subset_closure element_mem, element_mem.2⟩

theorem pRegular_pair_of_inversion_card {group : Type*} [Group group] [Finite group]
    (prime : ℕ) [Fact (Nat.Prime prime)] (first second : Component group) (distinct : first ≠ second)
    (subgroup : Subgroup group) (prime_group : IsPGroup prime subgroup)
    (odd_subgroup : Odd (Nat.card subgroup)) (contains : subgroup ≤ componentStabilizer first)
    (involution : Involution group) (mem_first : involution.val ∈ componentStabilizer first)
    (normalizes : involution.val ∈ Subgroup.normalizer (subgroup : Set group))
    (inverted_second : inversionSet subgroup involution ⊆ componentStabilizer second)
    (large : CFSG.OrderReductions.PrimePart.primePart prime (Nat.card (Involution (componentStabilizer first))) ≤
      Nat.card (inversionSet subgroup involution)) :
    PRegular prime (CFSG.OrderReductions.TwoPointInvolutions.pairSubgroup first second) (componentStabilizer first) := by
  let generated := Subgroup.closure (inversionSet subgroup involution)
  have generated_le : generated ≤ subgroup := (Subgroup.closure_le _).mpr fun element element_mem => element_mem.1
  have generated_pair : generated ≤ CFSG.OrderReductions.TwoPointInvolutions.pairSubgroup first second := by
    apply (Subgroup.closure_le _).mpr
    intro element element_mem
    exact ⟨contains element_mem.1, inverted_second element_mem⟩
  have generated_normalizes : involution.val ∈ Subgroup.normalizer (generated : Set group) :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mpr (inverted_closure_invariant subgroup involution normalizes)
  have generated_odd := odd_subgroup.of_dvd_nat (Subgroup.card_dvd_of_le generated_le)
  apply (pRegular_iff_prime_orbit_large prime _ _
    (distinct_componentStabilizers_odd_intersection first second distinct)).mpr
  refine ⟨involution, mem_first, generated, prime_group.to_le generated_le, generated_pair,
    generated_normalizes, ?_⟩
  change CFSG.OrderReductions.PrimePart.primePart prime
    (Nat.card (MulAction.orbit (CFSG.OrderReductions.TwoPointInvolutions.pairSubgroup first second) involution)) ≤ _
  rw [pair_involution_orbit_card first second distinct involution mem_first,
    ← inversionSet_card_eq_orbit generated generated_odd involution generated_normalizes]
  rw [inversionSet_closure_eq]
  exact large

theorem intersection_map_equiv {source target : Type*} [Group source] [Group target]
    (equivalence : source ≃* target) (subgroup : Subgroup source) (involution : Involution source) :
    intersection (MulAut.conj (equivalence involution.val)) (subgroup.map equivalence.toMonoidHom) =
      (intersection (MulAut.conj involution.val) subgroup).map equivalence.toMonoidHom := by
  rw [intersection, intersection, Subgroup.map_inf _ _ _ equivalence.injective,
    Subgroup.map_map, Subgroup.map_map]
  congr 1
  congr 1
  ext element
  change equivalence involution.val * equivalence element * (equivalence involution.val)⁻¹ =
    equivalence (involution.val * element * involution.val⁻¹)
  rw [map_mul, map_mul, map_inv]

theorem pRegular_map_equiv {source target : Type*} [Group source] [Group target]
    [Finite source] [Finite target] (prime : ℕ) (equivalence : source ≃* target)
    (subgroup ambient : Subgroup source) (regular : PRegular prime subgroup ambient) :
    PRegular prime (subgroup.map equivalence.toMonoidHom) (ambient.map equivalence.toMonoidHom) := by
  obtain ⟨involution, mem_ambient, full_primePart⟩ := regular
  refine ⟨mapInvolution equivalence.toMonoidHom equivalence.injective involution,
    Subgroup.mem_map_of_mem _ mem_ambient, ?_⟩
  change CFSG.OrderReductions.PrimePart.primePart prime
    (Nat.card (intersection (MulAut.conj (equivalence involution.val)) (subgroup.map equivalence.toMonoidHom))) = _
  rw [intersection_map_equiv, Subgroup.card_map_of_injective equivalence.injective,
    Subgroup.card_map_of_injective equivalence.injective]
  exact full_primePart

theorem pRegular_pair_symm {group : Type*} [Group group] [Finite group]
    (prime : ℕ) (first second : Component group) (distinct : first ≠ second)
    (regular : PRegular prime (CFSG.OrderReductions.TwoPointInvolutions.pairSubgroup first second)
      (componentStabilizer first)) :
    PRegular prime (CFSG.OrderReductions.TwoPointInvolutions.pairSubgroup first second) (componentStabilizer second) := by
  obtain ⟨flip, first_moves, second_moves⟩ :=
    CFSG.OrderReductions.InvolutionFusion.involution_swapping_components first second distinct
  have invariant : (CFSG.OrderReductions.TwoPointInvolutions.pairSubgroup first second).map
      (MulAut.conj flip.val).toMonoidHom = CFSG.OrderReductions.TwoPointInvolutions.pairSubgroup first second :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp
      (CFSG.OrderReductions.TwoPointInvolutions.flip_normalizes_pair first second flip first_moves second_moves)
  have transported := pRegular_map_equiv prime (MulAut.conj flip.val) _ _ regular
  rwa [invariant, ← componentStabilizer_smul, first_moves] at transported

theorem auxiliary_exists_outside {group : Type*} [Group group] [Finite group]
    (prime : ℕ) [Fact (Nat.Prime prime)] (point : Component group)
    (elements : Set group) (inside : Involution group) (inside_mem : inside.val ∈ componentStabilizer point)
    (extension : Subgroup group) (auxiliary : AuxiliaryData point elements inside prime extension) :
    ∃ outside : Involution group, outside.val ∈ extension ∧ outside.val ∉ componentStabilizer point := by
  let internal_subgroup := (componentStabilizer point).subgroupOf extension
  have exists_element : ∃ element : extension, element ∉ internal_subgroup := by
    by_contra no_element
    push Not at no_element
    exact auxiliary.2.1.1 (internal_subgroup.eq_top_iff'.mpr no_element)
  obtain ⟨acting, acting_not_mem⟩ := exists_element
  let outside := acting.val • inside
  have outside_extension : outside.val ∈ extension := by
    rw [involution_smul_val]
    exact extension.mul_mem (extension.mul_mem acting.property auxiliary.1)
      (extension.inv_mem acting.property)
  refine ⟨outside, outside_extension, ?_⟩
  intro outside_mem
  let internal_inside : Involution extension :=
    ⟨⟨inside.val, auxiliary.1⟩, by rw [← Subgroup.orderOf_coe]; exact inside.property⟩
  apply acting_not_mem
  apply stronglyEmbedded_involution_conjugator_mem internal_subgroup auxiliary.2.1
    internal_inside inside_mem acting
  exact outside_mem

theorem exists_minimum_core_outside {group : Type*} [Group group] [Finite group]
    (prime : ℕ) [Fact (Nat.Prime prime)] (point : Component group)
    (elements : Set group) (inside : Involution group) (inside_mem : inside.val ∈ componentStabilizer point)
    (extension : Subgroup group) (auxiliary : AuxiliaryData point elements inside prime extension) :
    ∃ outside : Involution group, outside.val ∈ extension ∧ outside.val ∉ componentStabilizer point ∧
      ∀ competitor : Involution group, competitor.val ∈ extension → competitor.val ∉ componentStabilizer point →
        Nat.card (ambientCore prime (CFSG.OrderReductions.TwoPointInvolutions.pairSubgroup point
          ((commutingGraph group).connectedComponentMk outside))) ≤
        Nat.card (ambientCore prime (CFSG.OrderReductions.TwoPointInvolutions.pairSubgroup point
          ((commutingGraph group).connectedComponentMk competitor))) := by
  classical
  let candidates := {outside : Involution group | outside.val ∈ extension ∧ outside.val ∉ componentStabilizer point}
  have nonempty : candidates.Nonempty := auxiliary_exists_outside prime point elements inside inside_mem extension auxiliary
  obtain ⟨outside, minimal⟩ := Set.Finite.exists_minimalFor
    (fun outside : Involution group => Nat.card (ambientCore prime (CFSG.OrderReductions.TwoPointInvolutions.pairSubgroup point
      ((commutingGraph group).connectedComponentMk outside)))) candidates (Set.toFinite _) nonempty
  refine ⟨outside, minimal.prop.1, minimal.prop.2, ?_⟩
  intro competitor competitor_mem competitor_outside
  exact minimal.le ⟨competitor_mem, competitor_outside⟩

theorem reflected_pair_eq_intersection {group : Type*} [Group group] [Finite group]
    (point : Component group) (inside outside : Involution group)
    (inside_mem : inside.val ∈ componentStabilizer point) :
    CFSG.OrderReductions.TwoPointInvolutions.pairSubgroup point
      ((commutingGraph group).connectedComponentMk (outside.val • inside)) =
        intersection (MulAut.conj outside.val) (componentStabilizer point) := by
  rw [CFSG.OrderReductions.TwoPointInvolutions.pairSubgroup, ← componentMk_smul,
    (componentStabilizer_involution_iff point inside).mp inside_mem,
    componentStabilizer_smul]
  rfl

theorem pair_intersection_eq_triple {group : Type*} [Group group]
    (point : Component group) (outside : Involution group) :
    intersection (MulAut.conj outside.val) (CFSG.OrderReductions.TwoPointInvolutions.pairSubgroup point
      ((commutingGraph group).connectedComponentMk outside)) =
        componentStabilizer ((commutingGraph group).connectedComponentMk outside) ⊓
          intersection (MulAut.conj outside.val) (componentStabilizer point) := by
  have point_fixed : outside.val • (commutingGraph group).connectedComponentMk outside =
      (commutingGraph group).connectedComponentMk outside := involution_mem_componentStabilizer outside
  rw [intersection, CFSG.OrderReductions.TwoPointInvolutions.pairSubgroup,
    Subgroup.map_inf _ _ _ (MulAut.conj outside.val).injective,
    ← componentStabilizer_smul outside.val ((commutingGraph group).connectedComponentMk outside),
    point_fixed]
  ext element
  change (element ∈ componentStabilizer point ∧
    element ∈ componentStabilizer ((commutingGraph group).connectedComponentMk outside)) ∧
      (element ∈ (componentStabilizer point).map (MulAut.conj outside.val).toMonoidHom ∧
        element ∈ componentStabilizer ((commutingGraph group).connectedComponentMk outside)) ↔
    element ∈ componentStabilizer ((commutingGraph group).connectedComponentMk outside) ∧
      element ∈ componentStabilizer point ∧
        element ∈ (componentStabilizer point).map (MulAut.conj outside.val).toMonoidHom
  tauto

theorem minimum_core_equalities {group : Type*} [Group group] [Finite group]
    (prime : ℕ) [Fact (Nat.Prime prime)] (point : Component group)
    (strong : StronglyEmbedded (componentStabilizer point))
    (subgroup : Subgroup group) (prime_group : IsPGroup prime subgroup)
    (odd_subgroup : Odd (Nat.card subgroup)) (contains : subgroup ≤ componentStabilizer point)
    (inside : Involution group) (inside_mem : inside.val ∈ componentStabilizer point)
    (normalizes : inside.val ∈ Subgroup.normalizer (subgroup : Set group))
    (large : CFSG.OrderReductions.PrimePart.primePart prime (Nat.card (Involution (componentStabilizer point))) ≤
      Nat.card (inversionSet subgroup inside))
    (extension : Subgroup group) (auxiliary : AuxiliaryData point (inversionSet subgroup inside) inside prime extension)
    (outside : Involution group) (outside_extension : outside.val ∈ extension)
    (outside_not_mem : outside.val ∉ componentStabilizer point)
    [Group.IsSolvable (CFSG.OrderReductions.TwoPointInvolutions.pairSubgroup point
      ((commutingGraph group).connectedComponentMk outside))]
    (minimum : ∀ competitor : Involution group, competitor.val ∈ extension →
      competitor.val ∉ componentStabilizer point →
        Nat.card (ambientCore prime (CFSG.OrderReductions.TwoPointInvolutions.pairSubgroup point
          ((commutingGraph group).connectedComponentMk outside))) ≤
        Nat.card (ambientCore prime (CFSG.OrderReductions.TwoPointInvolutions.pairSubgroup point
          ((commutingGraph group).connectedComponentMk competitor)))) :
    ambientCore prime (intersection (MulAut.conj outside.val) (componentStabilizer point)) =
      ambientCore prime (CFSG.OrderReductions.TwoPointInvolutions.pairSubgroup point
        ((commutingGraph group).connectedComponentMk outside)) ∧
    ambientCore prime (intersection (MulAut.conj outside.val)
      (CFSG.OrderReductions.TwoPointInvolutions.pairSubgroup point ((commutingGraph group).connectedComponentMk outside))) =
      ambientCore prime (CFSG.OrderReductions.TwoPointInvolutions.pairSubgroup point
        ((commutingGraph group).connectedComponentMk outside)) := by
  have distinct : point ≠ (commutingGraph group).connectedComponentMk outside := by
    intro equal
    exact outside_not_mem ((componentStabilizer_involution_iff point outside).mpr equal.symm)
  have regular := pRegular_pair_of_inversion_card prime point _ distinct subgroup prime_group odd_subgroup
    contains inside inside_mem normalizes (auxiliary.2.2 outside outside_extension outside_not_mem).1 large
  have regular_second := pRegular_pair_symm prime point _ distinct regular
  have lower := (auxiliary.2.2 outside outside_extension outside_not_mem).2
  rw [← pair_intersection_eq_triple] at lower
  have : Group.IsSolvable (CFSG.OrderReductions.TwoPointInvolutions.pairSubgroup
      ((commutingGraph group).connectedComponentMk outside) point) := by
    have pair_eq : CFSG.OrderReductions.TwoPointInvolutions.pairSubgroup
        ((commutingGraph group).connectedComponentMk outside) point =
          CFSG.OrderReductions.TwoPointInvolutions.pairSubgroup point
            ((commutingGraph group).connectedComponentMk outside) := inf_comm _ _
    rw [pair_eq]
    infer_instance
  have upper := CFSG.OrderReductions.RegularCore.regular_pair_intersection_core_le prime
    ((commutingGraph group).connectedComponentMk outside) point distinct.symm
    (by simpa only [CFSG.OrderReductions.TwoPointInvolutions.pairSubgroup, inf_comm] using regular_second)
    outside (involution_mem_componentStabilizer outside)
  have upper_original : ambientCore prime (intersection (MulAut.conj outside.val)
      (CFSG.OrderReductions.TwoPointInvolutions.pairSubgroup point ((commutingGraph group).connectedComponentMk outside))) ≤
      ambientCore prime (CFSG.OrderReductions.TwoPointInvolutions.pairSubgroup point
        ((commutingGraph group).connectedComponentMk outside)) := by
    simpa only [CFSG.OrderReductions.TwoPointInvolutions.pairSubgroup, inf_comm] using upper
  let competitor := outside.val • inside
  have competitor_extension : competitor.val ∈ extension := by
    rw [involution_smul_val]
    exact extension.mul_mem (extension.mul_mem outside_extension auxiliary.1) (extension.inv_mem outside_extension)
  have competitor_outside : competitor.val ∉ componentStabilizer point := by
    intro mem_point
    exact outside_not_mem (stronglyEmbedded_involution_conjugator_mem _ strong inside inside_mem outside.val mem_point)
  have card_lower := minimum competitor competitor_extension competitor_outside
  rw [reflected_pair_eq_intersection point inside outside inside_mem] at card_lower
  have equal_outer := Subgroup.eq_of_le_of_card_ge (lower.trans upper_original) card_lower
  have equal_inner := Subgroup.eq_of_le_of_card_ge upper_original
    (card_lower.trans (Subgroup.card_le_of_le lower))
  exact ⟨equal_outer, equal_inner⟩

end CFSG.OrderReductions.AuxiliaryMinimum

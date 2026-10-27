module

public import CFSG.Assembly.OrderReductions.OddInversion
public import CFSG.Assembly.OrderReductions.OutsideInvolutions

public section

namespace CFSG.OrderReductions.TwoPointInvolutions

open CFSG.OrderReductions.InvolutionGraph
open CFSG.OrderReductions.OutsideInvolutions

abbrev ComponentVertices {group : Type*} [Group group] (component : Component group) :=
  {involution : Involution group // (commutingGraph group).connectedComponentMk involution = component}

@[expose] noncomputable def componentVerticesEquiv {group : Type*} [Group group] [Finite group]
    (component : Component group) : ComponentVertices component ≃
      Involution (componentStabilizer component) :=
  ((Equiv.refl (Involution group)).subtypeEquiv (fun involution =>
    (componentStabilizer_involution_iff component involution).symm)).trans
      (involutionsInEquiv (componentStabilizer component))

theorem componentVertices_card_eq {group : Type*} [Group group] [Finite group]
    (first second : Component group) :
    Nat.card (ComponentVertices first) = Nat.card (ComponentVertices second) := by
  obtain ⟨conjugator, conjugates⟩ := components_transitive first second
  have stabilizer_equiv : componentStabilizer first ≃* componentStabilizer second :=
    MulAction.stabilizerEquivStabilizer conjugates.symm
  exact Nat.card_congr ((componentVerticesEquiv first).trans
    ((involutionEquiv stabilizer_equiv).trans (componentVerticesEquiv second).symm))

abbrev Transporters {group : Type*} [Group group] (first second : Component group) :=
  {involution : Involution group // involution.val • first = second}

@[expose] def transportVertex {group : Type*} [Group group] (first second : Component group)
    (vertex : Involution group) (vertex_component :
      (commutingGraph group).connectedComponentMk vertex = first)
    (transporter : Transporters first second) : ComponentVertices second :=
  ⟨transporter.val.val • vertex, by
    rw [← componentMk_smul, vertex_component, transporter.property]⟩

theorem transportVertex_bijective {group : Type*} [Group group] [Finite group]
    (first second : Component group) (distinct : first ≠ second)
    (vertex : Involution group)
    (vertex_component : (commutingGraph group).connectedComponentMk vertex = first) :
    Function.Bijective (transportVertex first second vertex vertex_component) := by
  have disconnected : ∃ other : Component group, other ≠ first := ⟨second, distinct.symm⟩
  have strong := componentStabilizer_stronglyEmbedded first disconnected
  have vertex_mem := (componentStabilizer_involution_iff first vertex).mpr vertex_component
  have outside_transporter (transporter : Transporters first second) :
      transporter.val.val ∉ componentStabilizer first := by
    intro stabilizes
    exact distinct ((MulAction.mem_stabilizer_iff.mp stabilizes).symm.trans transporter.property)
  constructor
  · intro first_transporter second_transporter equal_images
    have images : outsideConjugation (componentStabilizer first) strong vertex vertex_mem
        ⟨first_transporter.val, outside_transporter first_transporter⟩ =
        outsideConjugation (componentStabilizer first) strong vertex vertex_mem
          ⟨second_transporter.val, outside_transporter second_transporter⟩ := by
      apply Subtype.ext
      have equal_vertices := congrArg Subtype.val equal_images
      exact equal_vertices
    apply Subtype.ext
    have equal_vertices := congrArg Subtype.val
      ((outsideConjugation_bijective (componentStabilizer first) strong vertex vertex_mem).injective
        images)
    exact equal_vertices
  · intro target
    have outside_target : target.val.val ∉ componentStabilizer first := by
      intro mem_first
      exact distinct (((componentStabilizer_involution_iff first target.val).mp mem_first).symm.trans
        target.property)
    obtain ⟨conjugator, conjugates, _⟩ := unique_outside_conjugator (componentStabilizer first)
      strong vertex target.val vertex_mem outside_target
    have transports : conjugator.val • first = second := by
      rw [← vertex_component, componentMk_smul, conjugates]
      exact target.property
    exact ⟨⟨conjugator, transports⟩, Subtype.ext conjugates⟩

theorem transporters_card_eq {group : Type*} [Group group] [Finite group]
    (first second : Component group) (distinct : first ≠ second) :
    Nat.card (Transporters first second) = Nat.card (Involution (componentStabilizer first)) := by
  induction first using SimpleGraph.ConnectedComponent.ind with
  | h vertex =>
      rw [Nat.card_congr (Equiv.ofBijective
        (transportVertex _ second vertex rfl) (transportVertex_bijective _ second distinct vertex rfl)),
        ← componentVertices_card_eq ((commutingGraph group).connectedComponentMk vertex) second]
      exact Nat.card_congr (componentVerticesEquiv _)

theorem transporters_self_card_eq {group : Type*} [Group group] [Finite group]
    (component : Component group) :
    Nat.card (Transporters component component) = Nat.card (Involution (componentStabilizer component)) := by
  have equal_predicates : (fun involution : Involution group => involution.val • component = component) =
      (fun involution => involution.val ∈ componentStabilizer component) := rfl
  rw [show Transporters component component =
    {involution : Involution group // involution.val ∈ componentStabilizer component} from
      congrArg Subtype equal_predicates]
  exact Nat.card_congr (involutionsInEquiv _)

@[expose] def pairSubgroup {group : Type*} [Group group] (first second : Component group) :
    Subgroup group := componentStabilizer first ⊓ componentStabilizer second

theorem flip_normalizes_pair {group : Type*} [Group group]
    (first second : Component group) (flip : Involution group)
    (first_moves : flip.val • first = second) (second_moves : flip.val • second = first) :
    flip.val ∈ Subgroup.normalizer (pairSubgroup first second : Set group) := by
  rw [Subgroup.mem_normalizer_iff_map_conj_eq]
  change (pairSubgroup first second).map (MulAut.conj flip.val).toMonoidHom = _
  dsimp only [pairSubgroup]
  rw [Subgroup.map_inf _ _ _ (MulAut.conj flip.val).injective,
    ← componentStabilizer_smul, ← componentStabilizer_smul, first_moves, second_moves, inf_comm]

@[expose] def flipAutomorphism {group : Type*} [Group group]
    (first second : Component group) (flip : Involution group)
    (first_moves : flip.val • first = second) (second_moves : flip.val • second = first) :
    MulAut (pairSubgroup first second) :=
  (pairSubgroup first second).normalizerMonoidHom
    ⟨flip.val, flip_normalizes_pair first second flip first_moves second_moves⟩

theorem flipAutomorphism_val {group : Type*} [Group group]
    (first second : Component group) (flip : Involution group)
    (first_moves : flip.val • first = second) (second_moves : flip.val • second = first)
    (element : pairSubgroup first second) :
    (flipAutomorphism first second flip first_moves second_moves element).val =
      flip.val * element.val * flip.val⁻¹ :=
  Subgroup.normalizerMonoidHom_apply_apply_coe _ _ _

theorem flipAutomorphism_involutive {group : Type*} [Group group]
    (first second : Component group) (flip : Involution group)
    (first_moves : flip.val • first = second) (second_moves : flip.val • second = first) :
    Function.Involutive (flipAutomorphism first second flip first_moves second_moves) := by
  intro element
  apply Subtype.ext
  rw [flipAutomorphism_val, flipAutomorphism_val,
    inv_eq_self_of_orderOf_eq_two flip.property]
  have square_one := CFSG.OrderReductions.InvolutionFusion.involution_mul_self flip
  calc
    flip.val * (flip.val * element.val * flip.val) * flip.val =
        (flip.val * flip.val) * element.val * (flip.val * flip.val) := by group
    _ = element.val := by rw [square_one, one_mul, mul_one]

@[expose] def invertedTransporter {group : Type*} [Group group] [Finite group]
    (first second : Component group) (distinct : first ≠ second) (flip : Involution group)
    (first_moves : flip.val • first = second) (second_moves : flip.val • second = first)
    (element : CFSG.OrderReductions.OddInversion.InvertedElements
      (flipAutomorphism first second flip first_moves second_moves)) :
    Transporters first second := by
  have flip_not_mem : flip.val ∉ componentStabilizer first := by
    intro stabilizes
    exact distinct ((MulAction.mem_stabilizer_iff.mp stabilizes).symm.trans first_moves)
  have inversion : flip.val * element.val.val * flip.val = element.val.val⁻¹ := by
    have underlying := congrArg Subtype.val element.property
    simpa only [flipAutomorphism_val, inv_eq_self_of_orderOf_eq_two flip.property,
      Subgroup.coe_inv] using underlying
  have square_one : (element.val.val * flip.val) ^ 2 = 1 := by
    rw [pow_two, mul_assoc]
    have inversion_assoc : flip.val * (element.val.val * flip.val) = element.val.val⁻¹ := by
      simpa only [mul_assoc] using inversion
    rw [inversion_assoc, mul_inv_cancel]
  have ne_one : element.val.val * flip.val ≠ 1 := by
    intro equal_one
    have equal_flip : flip.val = element.val.val⁻¹ := by
      have multiplied := congrArg (fun product : group => element.val.val⁻¹ * product) equal_one
      simpa only [← mul_assoc, inv_mul_cancel, one_mul, mul_one] using multiplied
    exact flip_not_mem (equal_flip ▸ (componentStabilizer first).inv_mem element.val.property.1)
  have product_order : orderOf (element.val.val * flip.val) = 2 := by
    rcases (Nat.dvd_prime (by decide : Nat.Prime 2)).mp
      (orderOf_dvd_of_pow_eq_one square_one) with order_one | order_two
    · exact False.elim (ne_one (orderOf_eq_one_iff.mp order_one))
    · exact order_two
  refine ⟨⟨element.val.val * flip.val, product_order⟩, ?_⟩
  change (element.val.val * flip.val) • first = second
  rw [mul_smul, first_moves]
  exact element.val.property.2

@[expose] def transporterInverted {group : Type*} [Group group]
    (first second : Component group) (flip : Involution group)
    (first_moves : flip.val • first = second) (second_moves : flip.val • second = first)
    (transporter : Transporters first second) :
    CFSG.OrderReductions.OddInversion.InvertedElements
      (flipAutomorphism first second flip first_moves second_moves) := by
  have transporter_reverse : transporter.val.val • second = first := by
    calc
      transporter.val.val • second = transporter.val.val • transporter.val.val • first :=
        congrArg (fun component : Component group => transporter.val.val • component)
          transporter.property.symm
      _ = first := by
        rw [← mul_smul, CFSG.OrderReductions.InvolutionFusion.involution_mul_self, one_smul]
  have mem_pair : transporter.val.val * flip.val ∈ pairSubgroup first second := by
    constructor
    · change (transporter.val.val * flip.val) • first = first
      rw [mul_smul, first_moves, transporter_reverse]
    · change (transporter.val.val * flip.val) • second = second
      rw [mul_smul, second_moves, transporter.property]
  refine ⟨⟨transporter.val.val * flip.val, mem_pair⟩, ?_⟩
  apply Subtype.ext
  rw [flipAutomorphism_val]
  change flip.val * (transporter.val.val * flip.val) * flip.val⁻¹ =
    (transporter.val.val * flip.val)⁻¹
  rw [mul_inv_rev,
    inv_eq_self_of_orderOf_eq_two flip.property,
    inv_eq_self_of_orderOf_eq_two transporter.val.property]
  simp only [mul_assoc, CFSG.OrderReductions.InvolutionFusion.involution_mul_self, mul_one]

@[expose] def invertedTransporterEquiv {group : Type*} [Group group] [Finite group]
    (first second : Component group) (distinct : first ≠ second) (flip : Involution group)
    (first_moves : flip.val • first = second) (second_moves : flip.val • second = first) :
    CFSG.OrderReductions.OddInversion.InvertedElements
      (flipAutomorphism first second flip first_moves second_moves) ≃ Transporters first second where
  toFun := invertedTransporter first second distinct flip first_moves second_moves
  invFun := transporterInverted first second flip first_moves second_moves
  left_inv element := by
    apply Subtype.ext
    apply Subtype.ext
    dsimp only [transporterInverted, invertedTransporter]
    change (element.val.val * flip.val) * flip.val = element.val.val
    rw [mul_assoc, CFSG.OrderReductions.InvolutionFusion.involution_mul_self, mul_one]
  right_inv transporter := by
    apply Subtype.ext
    apply Subtype.ext
    dsimp only [transporterInverted, invertedTransporter]
    change (transporter.val.val * flip.val) * flip.val = transporter.val.val
    rw [mul_assoc, CFSG.OrderReductions.InvolutionFusion.involution_mul_self, mul_one]

theorem inverted_flip_card_eq {group : Type*} [Group group] [Finite group]
    (first second : Component group) (distinct : first ≠ second) (flip : Involution group)
    (first_moves : flip.val • first = second) (second_moves : flip.val • second = first) :
    Nat.card (CFSG.OrderReductions.OddInversion.InvertedElements
      (flipAutomorphism first second flip first_moves second_moves)) =
        Nat.card (Involution (componentStabilizer first)) := by
  rw [Nat.card_congr (invertedTransporterEquiv first second distinct flip first_moves second_moves)]
  exact transporters_card_eq first second distinct

@[expose] def invertedVertex {group : Type*} [Group group]
    (first second : Component group) (flip : Involution group)
    (first_moves : flip.val • first = second) (second_moves : flip.val • second = first)
    (vertex : ComponentVertices first)
    (element : CFSG.OrderReductions.OddInversion.InvertedElements
      (flipAutomorphism first second flip first_moves second_moves)) : ComponentVertices first :=
  ⟨element.val.val • vertex.val, by
    rw [← componentMk_smul, vertex.property]
    exact element.val.property.1⟩

theorem invertedVertex_bijective {group : Type*} [Group group] [Finite group]
    (first second : Component group) (distinct : first ≠ second) (flip : Involution group)
    (first_moves : flip.val • first = second) (second_moves : flip.val • second = first)
    (vertex : ComponentVertices first) :
    Function.Bijective (invertedVertex first second flip first_moves second_moves vertex) := by
  classical
  have strong := componentStabilizer_stronglyEmbedded first ⟨second, distinct.symm⟩
  have flip_not_mem : flip.val ∉ componentStabilizer first := by
    intro stabilizes
    exact distinct ((MulAction.mem_stabilizer_iff.mp stabilizes).symm.trans first_moves)
  let cast_inverted : CFSG.OrderReductions.OddInversion.InvertedElements
      (flipAutomorphism first second flip first_moves second_moves) →
        InvertedBy (componentStabilizer first) flip := fun element =>
    ⟨⟨element.val.val, element.val.property.1⟩, by
      have underlying := congrArg Subtype.val element.property
      simpa only [flipAutomorphism_val, Subgroup.coe_inv, MulAut.conj_apply] using underlying⟩
  have cast_injective : Function.Injective cast_inverted := by
    intro first_element second_element equal_images
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun element : InvertedBy (componentStabilizer first) flip => element.val.val)
      equal_images
  have injection : Function.Injective
      (invertedVertex first second flip first_moves second_moves vertex) := by
    intro first_element second_element equal_images
    apply cast_injective
    apply inverted_conjugation_injective (componentStabilizer first) strong vertex.val flip
      ((componentStabilizer_involution_iff first vertex.val).mpr vertex.property) flip_not_mem
    have equal_vertices := congrArg Subtype.val equal_images
    exact equal_vertices
  let _ : Fintype (CFSG.OrderReductions.OddInversion.InvertedElements
    (flipAutomorphism first second flip first_moves second_moves)) := Fintype.ofFinite _
  let _ : Fintype (ComponentVertices first) := Fintype.ofFinite _
  apply (Fintype.bijective_iff_injective_and_card _).mpr
  refine ⟨injection, ?_⟩
  simp only [← Nat.card_eq_fintype_card]
  rw [inverted_flip_card_eq first second distinct flip first_moves second_moves]
  exact (Nat.card_congr (componentVerticesEquiv first)).symm

instance componentVertexAction {group : Type*} [Group group]
    (first second : Component group) : MulAction (pairSubgroup first second) (ComponentVertices first) where
  smul element vertex := ⟨element.val • vertex.val, by
    rw [← componentMk_smul, vertex.property]
    exact element.property.1⟩
  one_smul vertex := by
    apply Subtype.ext
    exact one_smul group vertex.val
  mul_smul first_element second_element vertex := by
    apply Subtype.ext
    exact mul_smul first_element.val second_element.val vertex.val

theorem pair_transitive_on_vertices {group : Type*} [Group group] [Finite group]
    (first second : Component group) (distinct : first ≠ second) :
    MulAction.IsPretransitive (pairSubgroup first second) (ComponentVertices first) := by
  obtain ⟨flip, first_moves, second_moves⟩ :=
    CFSG.OrderReductions.InvolutionFusion.involution_swapping_components first second distinct
  constructor
  intro first_vertex second_vertex
  obtain ⟨inverted, moves⟩ :=
    (invertedVertex_bijective first second distinct flip first_moves second_moves first_vertex).surjective
      second_vertex
  exact ⟨inverted.val, moves⟩

theorem involution_card_dvd_pair_card {group : Type*} [Group group] [Finite group]
    (first second : Component group) (distinct : first ≠ second) :
    Nat.card (Involution (componentStabilizer first)) ∣ Nat.card (pairSubgroup first second) := by
  classical
  have := pair_transitive_on_vertices first second distinct
  induction first using SimpleGraph.ConnectedComponent.ind with
  | h vertex =>
      let base : ComponentVertices ((commutingGraph group).connectedComponentMk vertex) := ⟨vertex, rfl⟩
      let _ : Fintype (pairSubgroup ((commutingGraph group).connectedComponentMk vertex) second) :=
        Fintype.ofFinite _
      let _ : Fintype (ComponentVertices ((commutingGraph group).connectedComponentMk vertex)) :=
        Fintype.ofFinite _
      let _ : Fintype (MulAction.stabilizer
          (pairSubgroup ((commutingGraph group).connectedComponentMk vertex) second) base) :=
        Fintype.ofFinite _
      have product_eq := MulAction.card_orbit_mul_card_stabilizer_eq_card_group
        (pairSubgroup ((commutingGraph group).connectedComponentMk vertex) second) base
      simp only [← Nat.card_eq_fintype_card] at product_eq
      rw [MulAction.orbit_eq_univ] at product_eq
      rw [Nat.card_congr (Equiv.Set.univ _), Nat.card_congr (componentVerticesEquiv _)] at product_eq
      exact ⟨_, product_eq.symm⟩

theorem component_involution_card_odd {group : Type*} [Group group] [Finite group]
    (first second : Component group) (distinct : first ≠ second) :
    Odd (Nat.card (Involution (componentStabilizer first))) :=
  (distinct_componentStabilizers_odd_intersection first second distinct).of_dvd_nat
    (involution_card_dvd_pair_card first second distinct)

theorem flip_fixed_index_eq_involution_card {group : Type*} [Group group] [Finite group]
    (first second : Component group) (distinct : first ≠ second) (flip : Involution group)
    (first_moves : flip.val • first = second) (second_moves : flip.val • second = first) :
    (CFSG.OrderReductions.OddInversion.fixedSubgroup
      (flipAutomorphism first second flip first_moves second_moves)).index =
        Nat.card (Involution (componentStabilizer first)) := by
  rw [← CFSG.OrderReductions.OddInversion.inverted_card_eq_fixed_index
    (flipAutomorphism first second flip first_moves second_moves)
    (flipAutomorphism_involutive first second flip first_moves second_moves)
    (distinct_componentStabilizers_odd_intersection first second distinct)]
  exact inverted_flip_card_eq first second distinct flip first_moves second_moves

theorem pair_card_ge_three_of_commuting {group : Type*} [Group group] [Finite group]
    (first second : Component group) (distinct : first ≠ second)
    (first_involution second_involution : Involution (componentStabilizer first))
    (distinct_involutions : first_involution ≠ second_involution)
    (commuting : Commute first_involution.val second_involution.val) :
    3 ≤ Nat.card (pairSubgroup first second) := by
  have involution_bound := CFSG.OrderReductions.InvolutionFusion.involution_card_ge_three_of_commuting
    first_involution second_involution distinct_involutions commuting
  have divides := involution_card_dvd_pair_card first second distinct
  have positive : 0 < Nat.card (pairSubgroup first second) := Nat.card_pos
  exact involution_bound.trans (Nat.le_of_dvd positive divides)

theorem exists_odd_prime_dvd_pair_of_commuting {group : Type*} [Group group] [Finite group]
    (first second : Component group) (distinct : first ≠ second)
    (first_involution second_involution : Involution (componentStabilizer first))
    (distinct_involutions : first_involution ≠ second_involution)
    (commuting : Commute first_involution.val second_involution.val) :
    ∃ prime : ℕ, prime.Prime ∧ Odd prime ∧
      prime ∣ Nat.card (Involution (componentStabilizer first)) ∧
      prime ∣ Nat.card (pairSubgroup first second) := by
  have involution_bound := CFSG.OrderReductions.InvolutionFusion.involution_card_ge_three_of_commuting
    first_involution second_involution distinct_involutions commuting
  obtain ⟨prime, prime_prime, divides⟩ := Nat.exists_prime_and_dvd
    (by omega : Nat.card (Involution (componentStabilizer first)) ≠ 1)
  have prime_odd := (component_involution_card_odd first second distinct).of_dvd_nat divides
  exact ⟨prime, prime_prime, prime_odd, divides,
    divides.trans (involution_card_dvd_pair_card first second distinct)⟩

end CFSG.OrderReductions.TwoPointInvolutions

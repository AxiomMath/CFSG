module

public import CFSG.Assembly.OrderReductions.StrongEmbeddingInheritance
public import CFSG.Assembly.OrderReductions.TwoPointInvolutions

public section

namespace CFSG.OrderReductions.InternalComponents

open CFSG.OrderReductions.InvolutionGraph

@[expose] def pointGraphHom {group : Type*} [Group group] [Finite group]
    (point : Component group) (subgroup : Subgroup group)
    (contains : ∀ involution : Involution group,
      involution.val ∈ componentStabilizer point → involution.val ∈ subgroup) :
    point.toSimpleGraph →g commutingGraph subgroup where
  toFun vertex := ⟨⟨vertex.val.val, contains vertex.val
    ((componentStabilizer_involution_iff point vertex.val).mpr
      ((point.mem_supp_iff vertex.val).mp vertex.property))⟩,
        by rw [← Subgroup.orderOf_coe]; exact vertex.val.property⟩
  map_rel' := by
    intro first second adjacent
    have ambient_adjacent := (point.toSimpleGraph_adj first.property second.property).mp adjacent
    refine ⟨?_, ?_⟩
    · intro equal
      apply ambient_adjacent.1
      apply Subtype.ext
      exact congrArg (fun vertex : Involution subgroup => vertex.val.val) equal
    · change (⟨first.val.val, _⟩ : subgroup) * ⟨second.val.val, _⟩ =
        (⟨second.val.val, _⟩ : subgroup) * ⟨first.val.val, _⟩
      exact Subtype.ext ambient_adjacent.2.eq

theorem internal_reachable_of_same_point {group : Type*} [Group group] [Finite group]
    (point : Component group) (subgroup : Subgroup group)
    (contains : ∀ involution : Involution group,
      involution.val ∈ componentStabilizer point → involution.val ∈ subgroup)
    (first second : Involution subgroup)
    (first_point : (mapInvolution subgroup.subtype Subtype.val_injective first).val ∈ componentStabilizer point)
    (second_point : (mapInvolution subgroup.subtype Subtype.val_injective second).val ∈ componentStabilizer point) :
    (commutingGraph subgroup).Reachable first second := by
  let first_ambient := mapInvolution subgroup.subtype Subtype.val_injective first
  let second_ambient := mapInvolution subgroup.subtype Subtype.val_injective second
  let first_vertex : point := ⟨first_ambient,
    (point.mem_supp_iff first_ambient).mpr ((componentStabilizer_involution_iff point first_ambient).mp first_point)⟩
  let second_vertex : point := ⟨second_ambient,
    (point.mem_supp_iff second_ambient).mpr ((componentStabilizer_involution_iff point second_ambient).mp second_point)⟩
  have reachable := (point.connected_toSimpleGraph.preconnected first_vertex second_vertex).map
    (pointGraphHom point subgroup contains)
  exact reachable

theorem stabilizer_intersection_eq_internal {group : Type*} [Group group] [Finite group]
    (point : Component group) (strong : StronglyEmbedded (componentStabilizer point))
    (subgroup : Subgroup group)
    (contains : ∀ involution : Involution group,
      involution.val ∈ componentStabilizer point → involution.val ∈ subgroup)
    (inside : Involution subgroup)
    (inside_point : inside.val.val ∈ componentStabilizer point) :
    (componentStabilizer point).subgroupOf subgroup =
      componentStabilizer ((commutingGraph subgroup).connectedComponentMk inside) := by
  let inside_ambient := mapInvolution subgroup.subtype Subtype.val_injective inside
  ext element
  constructor
  · intro fixes_point
    have conjugate_point : (mapInvolution subgroup.subtype Subtype.val_injective (element • inside)).val ∈
        componentStabilizer point := by
      have conjugate_mem := CFSG.OrderReductions.OutsideInvolutions.conjugate_mem_of_mem
        (componentStabilizer point) element.val inside_ambient fixes_point inside_point
      exact conjugate_mem
    have reachable := internal_reachable_of_same_point point subgroup contains
      (element • inside) inside conjugate_point inside_point
    change element • (commutingGraph subgroup).connectedComponentMk inside = _
    rw [componentMk_smul]
    exact SimpleGraph.ConnectedComponent.sound reachable
  · intro fixes_internal
    have same_component : (commutingGraph subgroup).connectedComponentMk (element • inside) =
        (commutingGraph subgroup).connectedComponentMk inside := by
      rw [← componentMk_smul]
      exact fixes_internal
    have ambient_reachable := (SimpleGraph.ConnectedComponent.eq.mp same_component).map
      (mapGraph subgroup.subtype Subtype.val_injective)
    have conjugate_point : (element.val • inside_ambient).val ∈ componentStabilizer point := by
      apply (componentStabilizer_involution_iff point (element.val • inside_ambient)).mpr
      exact (SimpleGraph.ConnectedComponent.sound ambient_reachable).trans
        ((componentStabilizer_involution_iff point inside_ambient).mp inside_point)
    exact stronglyEmbedded_involution_conjugator_mem _ strong inside_ambient inside_point element.val conjugate_point

@[expose] def componentsToConjugates {group : Type*} [Group group] [Finite group]
    (point : Component group) : Component group → CFSG.OrderReductions.StrongEmbedding.Conjugates (componentStabilizer point) :=
  fun other => ⟨componentStabilizer other, by
    obtain ⟨acting, moves⟩ := components_transitive point other
    refine ⟨acting, ?_⟩
    change acting • componentStabilizer point = componentStabilizer other
    rw [CFSG.OrderReductions.StrongEmbedding.subgroup_smul, ← componentStabilizer_smul, moves]⟩

theorem componentsToConjugates_bijective {group : Type*} [Group group] [Finite group]
    (point : Component group) : Function.Bijective (componentsToConjugates point) := by
  constructor
  · intro first second equal
    exact componentStabilizer_injective (congrArg Subtype.val equal)
  · intro conjugate
    obtain ⟨acting, conjugates⟩ := conjugate.property
    refine ⟨acting • point, ?_⟩
    apply Subtype.ext
    change componentStabilizer (acting • point) = conjugate.val
    rw [componentStabilizer_smul]
    exact conjugates

@[expose] noncomputable def componentsEquivConjugates {group : Type*} [Group group] [Finite group]
    (point : Component group) : Component group ≃ CFSG.OrderReductions.StrongEmbedding.Conjugates (componentStabilizer point) :=
  Equiv.ofBijective (componentsToConjugates point) (componentsToConjugates_bijective point)

theorem componentsEquivConjugates_equivariant {group : Type*} [Group group] [Finite group]
    (point : Component group) (acting : group) (other : Component group) :
    componentsEquivConjugates point (acting • other) = acting • componentsEquivConjugates point other := by
  apply Subtype.ext
  exact componentStabilizer_smul acting other

theorem components_two_transitive_iff_conjugates {group : Type*} [Group group] [Finite group]
    (point : Component group) :
    MulAction.IsMultiplyPretransitive group (Component group) 2 ↔
      MulAction.IsMultiplyPretransitive group (CFSG.OrderReductions.StrongEmbedding.Conjugates (componentStabilizer point)) 2 := by
  exact CFSG.OrderReductions.StrongEmbeddingInheritance.equivariant_bijective_two_pretransitive_iff
    (MonoidHom.id group) Function.surjective_id (componentsEquivConjugates point)
    (componentsEquivConjugates_equivariant point)

theorem conjugate_internal_stabilizer_eq {group : Type*} [Group group] [Finite group]
    (point : Component group) (subgroup : Subgroup group) (inside : Involution subgroup)
    (stabilizer_eq : (componentStabilizer point).subgroupOf subgroup =
      componentStabilizer ((commutingGraph subgroup).connectedComponentMk inside))
    (acting : subgroup) :
    (componentStabilizer (acting.val • point)).subgroupOf subgroup =
      componentStabilizer (acting • (commutingGraph subgroup).connectedComponentMk inside) := by
  rw [componentStabilizer_smul, componentStabilizer_smul, ← stabilizer_eq]
  apply Subgroup.map_injective (f := subgroup.subtype) Subtype.val_injective
  rw [CFSG.OrderReductions.StrongEmbeddingInheritance.map_conjugate, Subgroup.subgroupOf_map_subtype,
    Subgroup.subgroupOf_map_subtype, Subgroup.map_inf _ _ _ (MulAut.conj acting.val).injective]
  have invariant : subgroup.map (MulAut.conj acting.val).toMonoidHom = subgroup :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp (subgroup.le_normalizer acting.property)
  change (componentStabilizer point).map (MulAut.conj acting.val).toMonoidHom ⊓ subgroup =
    (componentStabilizer point).map (MulAut.conj acting.val).toMonoidHom ⊓
      subgroup.map (MulAut.conj acting.val).toMonoidHom
  rw [invariant]

theorem internal_pair_eq {group : Type*} [Group group] [Finite group]
    (point : Component group) (subgroup : Subgroup group) (inside : Involution subgroup)
    (stabilizer_eq : (componentStabilizer point).subgroupOf subgroup =
      componentStabilizer ((commutingGraph subgroup).connectedComponentMk inside))
    (acting : subgroup) :
    (CFSG.OrderReductions.TwoPointInvolutions.pairSubgroup point (acting.val • point)).subgroupOf subgroup =
      CFSG.OrderReductions.TwoPointInvolutions.pairSubgroup
        ((commutingGraph subgroup).connectedComponentMk inside)
        (acting • (commutingGraph subgroup).connectedComponentMk inside) := by
  rw [CFSG.OrderReductions.TwoPointInvolutions.pairSubgroup]
  change ((componentStabilizer point ⊓ componentStabilizer (acting.val • point)).comap subgroup.subtype) = _
  rw [Subgroup.comap_inf]
  change (componentStabilizer point).subgroupOf subgroup ⊓
    (componentStabilizer (acting.val • point)).subgroupOf subgroup = _
  rw [stabilizer_eq, conjugate_internal_stabilizer_eq point subgroup inside stabilizer_eq acting]
  rfl

theorem internal_pair_distinct {group : Type*} [Group group] [Finite group]
    (point : Component group) (subgroup : Subgroup group) (inside : Involution subgroup)
    (stabilizer_eq : (componentStabilizer point).subgroupOf subgroup =
      componentStabilizer ((commutingGraph subgroup).connectedComponentMk inside))
    (acting : subgroup) (moves : acting.val • point ≠ point) :
    (commutingGraph subgroup).connectedComponentMk inside ≠
      acting • (commutingGraph subgroup).connectedComponentMk inside := by
  intro equal
  have fixes : acting ∈ componentStabilizer ((commutingGraph subgroup).connectedComponentMk inside) := equal.symm
  rw [← stabilizer_eq] at fixes
  exact moves fixes

end CFSG.OrderReductions.InternalComponents

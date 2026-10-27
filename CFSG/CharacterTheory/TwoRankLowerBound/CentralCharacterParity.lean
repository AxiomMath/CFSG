module

public import CFSG.CharacterTheory.TwoRankLowerBound.QuaternionEightCentralizer

public section

open scoped BigOperators Classical

namespace CFSG.TwoRankLowerBound.Helpers

theorem irreducible_central_element_is_scalar {G vector : Type*} [Group G]
    [AddCommGroup vector] [Module ℂ vector] [FiniteDimensional ℂ vector]
    (representation : Representation ℂ G vector) [representation.IsIrreducible]
    (element : G) (hcentral : element ∈ Subgroup.center G) :
    ∃ scalar : ℂ, representation element = scalar • (1 : Module.End ℂ vector) := by
  let intertwiner : representation.IntertwiningMap representation :=
    { toLinearMap := representation element
      isIntertwining' := by
        intro member
        change representation element * representation member =
          representation member * representation element
        rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.mp hcentral member] }
  obtain ⟨scalar, hscalar⟩ :=
    Representation.IsIrreducible.algebraMap_intertwiningMap_bijective_of_isAlgClosed.2 intertwiner
  refine ⟨scalar, ?_⟩
  have hequal := congrArg Representation.IntertwiningMap.toLinearMap hscalar
  rw [Representation.IntertwiningMap.algebraMap_apply,
    Representation.IntertwiningMap.toLinearMap_smul] at hequal
  have hone : (1 : representation.IntertwiningMap representation).toLinearMap =
      (1 : Module.End ℂ vector) := by
    ext member
    exact congrFun (Representation.IntertwiningMap.coe_one representation) member
  rw [hone] at hequal
  exact hequal.symm

theorem irreducible_central_involution_parity {G vector : Type*} [Group G]
    [AddCommGroup vector] [Module ℂ vector] [FiniteDimensional ℂ vector]
    (representation : Representation ℂ G vector) [representation.IsIrreducible]
    (involution : G) (hcentral : involution ∈ Subgroup.center G)
    (hsquare : involution ^ 2 = 1) :
    ∃ parity : ℂ, (parity = 1 ∨ parity = -1) ∧
      representation involution = parity • (1 : Module.End ℂ vector) ∧
      ∀ element : G, representation.character (element * involution) =
        parity * representation.character element := by
  obtain ⟨parity, hscalar⟩ := irreducible_central_element_is_scalar representation involution hcentral
  let : Nontrivial representation.asModule :=
    IsSimpleModule.nontrivial (MonoidAlgebra ℂ G) representation.asModule
  let : Nontrivial vector := representation.asModuleEquiv.symm.toEquiv.nontrivial
  have hparitySquare : parity * parity = 1 := by
    apply smul_left_injective ℂ (show (1 : Module.End ℂ vector) ≠ 0 from one_ne_zero)
    calc
      (parity * parity) • (1 : Module.End ℂ vector) =
          representation involution * representation involution := by
        rw [hscalar, smul_mul_smul_comm, one_mul]
      _ = 1 := by rw [← map_mul, ← pow_two, hsquare, map_one]
      _ = (1 : ℂ) • (1 : Module.End ℂ vector) := (one_smul _ _).symm
  refine ⟨parity, mul_self_eq_one_iff.mp hparitySquare, hscalar, ?_⟩
  intro element
  change LinearMap.trace ℂ vector (representation (element * involution)) =
    parity * LinearMap.trace ℂ vector (representation element)
  rw [map_mul, hscalar, mul_smul_comm, mul_one, map_smul, smul_eq_mul]

theorem irreducible_character_central_involution_parity {G : Type*} [Group G]
    (data : FiniteComplexRepresentation G) (hirreducible : data.IsIrreducible)
    (involution : G) (hcentral : involution ∈ Subgroup.center G)
    (hsquare : involution ^ 2 = 1) :
    ∃ parity : ℂ, (parity = 1 ∨ parity = -1) ∧
      data.character involution = parity * data.character 1 ∧
      ∀ element : G, data.character (element * involution) = parity * data.character element := by
  let : data.representation.IsIrreducible := hirreducible
  obtain ⟨parity, hsign, _, hvalues⟩ :=
    irreducible_central_involution_parity data.representation involution hcentral hsquare
  exact ⟨parity, hsign, by simpa only [one_mul] using hvalues 1, hvalues⟩

theorem central_character_parity_unique {G : Type*} [Group G]
    (data : FiniteComplexRepresentation G) (hirreducible : data.IsIrreducible)
    (involution : G) (left right : ℂ)
    (hleft : data.character involution = left * data.character 1)
    (hright : data.character involution = right * data.character 1) : left = right := by
  exact mul_right_cancel₀ (irreducible_character_degree_ne_zero data hirreducible) (hleft.symm.trans hright)

theorem odd_character_vanishes_of_conjugate_involution_translate {G : Type*} [Group G]
    (data : FiniteComplexRepresentation G) (involution element : G)
    (hodd : ∀ member : G, data.character (member * involution) = -data.character member)
    (hconjugate : IsConj element (element * involution)) : data.character element = 0 := by
  obtain ⟨conjugator, hconjugator⟩ := isConj_iff.mp hconjugate
  have hvalue : data.character (element * involution) = data.character element := by
    rw [← hconjugator]
    exact Representation.char_conj data.representation element conjugator
  rw [hodd] at hvalue
  linear_combination -(1 / 2 : ℂ) * hvalue

theorem quaternionEight_four_isConj_translate (element : QuaternionGroup 2)
    (horder : orderOf element = 4) :
    IsConj element (element * QuaternionGroup.a (2 : ZMod 4)) := by
  have hsquare := quaternionEight_four_square element horder
  have hinverse : element * QuaternionGroup.a (2 : ZMod 4) = element⁻¹ := by
    rw [← hsquare]
    have hfour : element ^ 4 = 1 := by rw [← horder]; exact pow_orderOf_eq_one element
    apply mul_right_cancel (b := element)
    rw [inv_mul_cancel]
    calc
      element * element ^ 2 * element = element ^ 4 := by group
      _ = 1 := hfour
  rw [hinverse]
  rcases quaternionEight_element_class element with hone | hinvolution | ⟨label, hrepresentative⟩
  · rw [hone, orderOf_one] at horder
    omega
  · rw [hinvolution, quaternionEight_involution_order] at horder
    omega
  · rcases hrepresentative with hrepresentative | hinverse
    · rw [hrepresentative]
      exact quaternionEight_representative_isConj_inverse label
    · rw [hinverse, inv_inv]
      exact (quaternionEight_representative_isConj_inverse label).symm

theorem sylow_quaternion_eight_odd_character_zero_on_order_four {G : Type*}
    [Group G] [Finite G] (sylow : Sylow 2 G)
    (isomorphism : (sylow : Subgroup G) ≃* QuaternionGroup 2) :
    let involution := isomorphism.symm (QuaternionGroup.a (2 : ZMod 4))
    let centralizer := Subgroup.centralizer ({(involution : G)} : Set G)
    let hle := (sylow_quaternion_eight_involution_data sylow isomorphism).2.2
    let localInvolution : centralizer := ⟨involution, hle involution.property⟩
    ∀ data : FiniteComplexRepresentation centralizer,
      (∀ member : centralizer, data.character (member * localInvolution) = -data.character member) →
      ∀ element : centralizer, orderOf element = 4 → data.character element = 0 := by
  intro involution centralizer hle localInvolution data hodd element horder
  let localSylow := sylow.subtype hle
  obtain ⟨member, hconj⟩ := two_element_isConj_sylow localSylow element ⟨2, by norm_num [horder]⟩
  have hmemberOriginal : ((member : centralizer) : G) ∈ (sylow : Subgroup G) := by
    have hmember := member.property
    simpa only [localSylow, Sylow.coe_subtype, Subgroup.mem_subgroupOf] using hmember
  let originalMember : (sylow : Subgroup G) := ⟨(member : centralizer), hmemberOriginal⟩
  let embedding : QuaternionGroup 2 →* centralizer :=
    { toFun := fun quaternion => ⟨isomorphism.symm quaternion, hle (isomorphism.symm quaternion).property⟩
      map_one' := by
        apply Subtype.ext
        change ((isomorphism.symm 1 : (sylow : Subgroup G)) : G) = 1
        exact congrArg Subtype.val isomorphism.symm.map_one
      map_mul' := by
        intro left right
        apply Subtype.ext
        change ((isomorphism.symm (left * right) : (sylow : Subgroup G)) : G) =
          ((isomorphism.symm left : (sylow : Subgroup G)) : G) * isomorphism.symm right
        exact congrArg Subtype.val (isomorphism.symm.map_mul left right) }
  have hquaternionOrder : orderOf (isomorphism originalMember) = 4 := by
    rw [isomorphism.orderOf_eq, ← Subgroup.orderOf_coe originalMember]
    change orderOf ((member : centralizer) : G) = 4
    rw [Subgroup.orderOf_coe, ← orderOf_eq_of_isConj hconj, horder]
  have hmemberConj : IsConj (member : centralizer) ((member : centralizer) * localInvolution) := by
    have hmapped := isConj_map_group_hom embedding
      (quaternionEight_four_isConj_translate (isomorphism originalMember) hquaternionOrder)
    have hfirst : embedding (isomorphism originalMember) = (member : centralizer) := by
      apply Subtype.ext
      change ((isomorphism.symm (isomorphism originalMember) : (sylow : Subgroup G)) : G) =
        ((member : centralizer) : G)
      rw [MulEquiv.symm_apply_apply]
    have hsecond : embedding (QuaternionGroup.a (2 : ZMod 4)) = localInvolution := rfl
    rw [map_mul, hfirst, hsecond] at hmapped
    exact hmapped
  have hzero := odd_character_vanishes_of_conjugate_involution_translate data localInvolution
    (member : centralizer) hodd hmemberConj
  obtain ⟨conjugator, hconjugator⟩ := isConj_iff.mp hconj
  have hvalue : data.character (member : centralizer) = data.character element := by
    rw [← hconjugator]
    exact Representation.char_conj data.representation element conjugator
  rw [← hvalue]
  exact hzero

end CFSG.TwoRankLowerBound.Helpers

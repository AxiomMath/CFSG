module

public import CFSG.Dihedral.DisconnectedInvolutionGraph.CyclicRootTI

public section

namespace CFSG.DisconnectedInvolutionGraph.Helpers

variable {G Scalar : Type*} [Group G] [Fintype G] [Field Scalar]

@[expose] noncomputable def inducedSupportedFunction (subgroup : Subgroup G) (function : G → Scalar) :
    G → Scalar :=
  fun element => (Nat.card subgroup : Scalar)⁻¹ *
    ∑ actor : G, function (actor * element * actor⁻¹)

theorem sum_subgroup_of_zero_outside (subgroup : Subgroup G) [Fintype subgroup]
    (function : G → Scalar) (hzero : ∀ element ∉ subgroup, function element = 0) :
    (∑ element : G, function element) = ∑ element : subgroup, function element := by
  classical
  calc
    (∑ element : G, function element) = ∑ element ∈ Finset.univ.filter (fun element => element ∈ subgroup),
        function element := by
      symm
      apply Finset.sum_subset (Finset.filter_subset _ _)
      intro element _ hnot
      apply hzero
      simpa only [Finset.mem_filter, Finset.mem_univ, true_and] using hnot
    _ = ∑ element : subgroup, function element := by
      apply Finset.sum_subtype
      intro element
      simp

theorem inducedSupportedFunction_conjugation (subgroup : Subgroup G) (function : G → Scalar)
    (actor element : G) :
    inducedSupportedFunction subgroup function (actor * element * actor⁻¹) =
      inducedSupportedFunction subgroup function element := by
  unfold inducedSupportedFunction
  congr 1
  apply Fintype.sum_equiv (Equiv.mulRight actor)
  intro member
  change function (member * (actor * element * actor⁻¹) * member⁻¹) =
    function ((member * actor) * element * (member * actor)⁻¹)
  congr 1
  group

theorem inducedSupportedFunction_zero_outside_conjugates (subgroup : Subgroup G)
    (support : Set G) (function : G → Scalar)
    (hzero : ∀ element ∉ support, function element = 0)
    (element : G) (houtside : ∀ actor : G, actor * element * actor⁻¹ ∉ support) :
    inducedSupportedFunction subgroup function element = 0 := by
  unfold inducedSupportedFunction
  rw [Finset.sum_eq_zero (fun actor _ => hzero _ (houtside actor)), mul_zero]

theorem inducedSupportedFunction_identity_zero (subgroup : Subgroup G)
    (support : Set G) (function : G → Scalar)
    (hidentity : 1 ∉ support) (hzero : ∀ element ∉ support, function element = 0) :
    inducedSupportedFunction subgroup function 1 = 0 := by
  apply inducedSupportedFunction_zero_outside_conjugates subgroup support function hzero
  intro actor
  simpa only [mul_one, mul_inv_cancel] using hidentity

theorem inducedSupportedFunction_involution_zero (subgroup : Subgroup G)
    (support : Set G) (function : G → Scalar)
    (hinvolutions : ∀ involution : Involution G, (involution : G) ∉ support)
    (hzero : ∀ element ∉ support, function element = 0) (involution : Involution G) :
    inducedSupportedFunction subgroup function involution = 0 := by
  apply inducedSupportedFunction_zero_outside_conjugates subgroup support function hzero
  intro actor
  exact hinvolutions (conjugateInvolution actor involution)

theorem inducedSupportedFunction_on_ti_support [CharZero Scalar]
    (subgroup : Subgroup G) (support : Set G) (hti : IsTISupport support subgroup)
    (function : G → Scalar) (hzero : ∀ element ∉ support, function element = 0)
    (hinvariant : ∀ actor ∈ subgroup, ∀ element : G,
      function (actor * element * actor⁻¹) = function element)
    (element : G) (hmem : element ∈ support) :
    inducedSupportedFunction subgroup function element = function element := by
  classical
  let _ : Fintype subgroup := Fintype.ofFinite subgroup
  have hterms : ∀ actor : G, function (actor * element * actor⁻¹) =
      if actor ∈ subgroup then function element else 0 := by
    intro actor
    split_ifs with hactor
    · exact hinvariant actor hactor element
    · apply hzero
      intro hconjugate
      exact hactor (hti.conjugate_mem_forces actor element hmem hconjugate)
  unfold inducedSupportedFunction
  simp only [hterms]
  have hsum : (∑ actor : G, if actor ∈ subgroup then function element else 0) =
      (Nat.card subgroup : Scalar) * function element := by
    rw [sum_subgroup_of_zero_outside subgroup _ (by
      intro actor houtside
      simp only [houtside, ite_false])]
    rw [Finset.sum_congr rfl (fun actor _ => ite_eq_left actor.property)]
    simp only [Finset.sum_const, nsmul_eq_mul, Finset.card_univ, Nat.card_eq_fintype_card]
  rw [hsum]
  have hcardNe : (Nat.card subgroup : Scalar) ≠ 0 := by
    exact_mod_cast (Nat.card_pos (α := subgroup)).ne'
  rw [← mul_assoc, inv_mul_cancel₀ hcardNe, one_mul]

theorem inducedSupportedFunction_pair_zero (subgroup : Subgroup G)
    (support : Set G) (hti : IsTISupport support subgroup)
    (hinverse : ∀ member ∈ support, member⁻¹ ∈ support)
    (function : G → Scalar) (hzero : ∀ element ∉ support, function element = 0)
    (hpairs : ∀ first second : Involution G, (first : G) ∈ subgroup → (second : G) ∈ subgroup →
      function ((first : G) * second) = 0)
    (first second : Involution G) :
    inducedSupportedFunction subgroup function ((first : G) * second) = 0 := by
  unfold inducedSupportedFunction
  rw [Finset.sum_eq_zero, mul_zero]
  intro actor _
  by_cases hmem : actor * ((first : G) * second) * actor⁻¹ ∈ support
  · have hproduct : (conjugateInvolution actor first : G) * conjugateInvolution actor second ∈ support := by
      change (actor * (first : G) * actor⁻¹) * (actor * (second : G) * actor⁻¹) ∈ support
      convert hmem using 1
      group
    obtain ⟨hfirst, hsecond⟩ := ti_involution_product_factors_mem support subgroup hti hinverse
      (conjugateInvolution actor first) (conjugateInvolution actor second) hproduct
    have hvanishing := hpairs (conjugateInvolution actor first) (conjugateInvolution actor second)
      hfirst hsecond
    change function ((actor * (first : G) * actor⁻¹) * (actor * (second : G) * actor⁻¹)) = 0
      at hvanishing
    convert hvanishing using 1
    congr 1
    group
  · exact hzero _ hmem

end CFSG.DisconnectedInvolutionGraph.Helpers

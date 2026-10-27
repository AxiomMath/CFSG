module

public import CFSG.Mathlib.GroupTheory.Basic
public import CFSG.Dihedral.DisconnectedInvolutionGraph.InvolutionGraph

public section

namespace CFSG.DisconnectedInvolutionGraph.Helpers

variable {G : Type*} [Group G]

theorem commuting_involution_closure_square (first second : Involution G)
    (hcommute : (first : G) * second = (second : G) * first)
    (element : G) (hmem : element ∈ Subgroup.closure ({(first : G), (second : G)} : Set G)) :
    element ^ 2 = 1 := by
  have hgeneratorsCommute : ∀ firstElement ∈ ({(first : G), (second : G)} : Set G),
      ∀ secondElement ∈ ({(first : G), (second : G)} : Set G),
        firstElement * secondElement = secondElement * firstElement := by
    intro firstElement hfirst secondElement hsecond
    rcases Set.mem_insert_iff.mp hfirst with rfl | hfirst
    · rcases Set.mem_insert_iff.mp hsecond with rfl | hsecond
      · rfl
      · rw [Set.mem_singleton_iff.mp hsecond]
        exact hcommute
    · rw [Set.mem_singleton_iff.mp hfirst]
      rcases Set.mem_insert_iff.mp hsecond with rfl | hsecond
      · exact hcommute.symm
      · rw [Set.mem_singleton_iff.mp hsecond]
  have hclosureCommute := CFSG.subgroup_isMulCommutative_closure hgeneratorsCommute
  induction hmem using Subgroup.closure_induction with
  | mem candidate hcandidate =>
    rcases Set.mem_insert_iff.mp hcandidate with rfl | hcandidate
    · simpa only [first.property] using pow_orderOf_eq_one (first : G)
    · rw [Set.mem_singleton_iff.mp hcandidate]
      simpa only [second.property] using pow_orderOf_eq_one (second : G)
  | one => exact one_pow _
  | mul firstElement secondElement hfirst hsecond hfirstSquare hsecondSquare =>
    have hcomm : Commute firstElement secondElement := by
      let _ := hclosureCommute
      exact congrArg (fun element : Subgroup.closure ({(first : G), (second : G)} : Set G) =>
        element.val) (mul_comm' ⟨firstElement, hfirst⟩ ⟨secondElement, hsecond⟩)
    rw [hcomm.mul_pow, hfirstSquare, hsecondSquare, one_mul]
  | inv candidate _ hsquare => rw [inv_pow, hsquare, inv_one]

theorem commuting_involution_closure_isPGroup (first second : Involution G)
    (hcommute : (first : G) * second = (second : G) * first) :
    IsPGroup 2 (Subgroup.closure ({(first : G), (second : G)} : Set G)) := by
  intro element
  refine ⟨1, ?_⟩
  apply Subtype.ext
  change element.val ^ (2 ^ 1) = 1
  rw [pow_one]
  exact commuting_involution_closure_square first second hcommute element.val element.property

end CFSG.DisconnectedInvolutionGraph.Helpers

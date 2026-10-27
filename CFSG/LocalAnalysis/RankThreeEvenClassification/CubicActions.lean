module

public import CFSG.Mathlib.GroupTheory.Basic
public import CFSG.LocalAnalysis.RankThreeEvenClassification.InvariantPairing
public import CFSG.LocalAnalysis.RankThreeEvenClassification.ClassTwoPairing

public section

namespace CFSG.RankThreeEvenClassification.Helpers

universe u v

open scoped commutatorElement

local instance cubicCenterCommGroup {G : Type u} [Group G] : CommGroup (Subgroup.center G) :=
  @IsMulCommutative.instCommGroup (Subgroup.center G) inferInstance inferInstance

@[expose] def automorphismDifference {G : Type u} [Group G] (automorphism : MulAut G) (element : G) : G :=
  element⁻¹ * automorphism element

def additiveAbelianAction {G : Type u} [Group G] (automorphism : MulAut G) :
    Additive (Abelianization G) →+ Additive (Abelianization G) :=
  MonoidHom.toAdditive (Abelianization.map automorphism.toMonoidHom)

def additiveAbelianImage {G : Type u} [Group G] (element : G) : Additive (Abelianization G) :=
  Additive.ofMul (Abelianization.of element)

theorem additiveAbelianAction_image {G : Type u} [Group G] (automorphism : MulAut G) (element : G) :
    additiveAbelianAction automorphism (additiveAbelianImage element) =
      additiveAbelianImage (automorphism element) := by
  exact congrArg Additive.ofMul (Abelianization.map_of automorphism.toMonoidHom element)

theorem additiveAbelianImage_difference {G : Type u} [Group G] (automorphism : MulAut G) (element : G) :
    additiveAbelianImage (automorphismDifference automorphism element) =
      additiveAbelianAction automorphism (additiveAbelianImage element) - additiveAbelianImage element := by
  rw [additiveAbelianAction_image]
  change Abelianization.of (element⁻¹ * automorphism element) =
    Abelianization.of (automorphism element) / Abelianization.of element
  rw [map_mul, map_inv, div_eq_mul_inv, mul_comm]

theorem additiveAbelianAction_commute {G : Type u} [Group G]
    (first second : MulAut G) (hcommute : Commute first second) :
    (additiveAbelianAction first).comp (additiveAbelianAction second) =
      (additiveAbelianAction second).comp (additiveAbelianAction first) := by
  apply AddMonoidHom.ext
  intro element
  change Abelianization.map first.toMonoidHom (Abelianization.map second.toMonoidHom (Additive.toMul element)) =
    Abelianization.map second.toMonoidHom (Abelianization.map first.toMonoidHom (Additive.toMul element))
  have hhom : first.toMonoidHom.comp second.toMonoidHom = second.toMonoidHom.comp first.toMonoidHom := by
    ext member
    exact DFunLike.congr_fun hcommute.eq member
  exact DFunLike.congr_fun
    ((Abelianization.map_comp second.toMonoidHom first.toMonoidHom).trans
      ((congrArg Abelianization.map hhom).trans
        (Abelianization.map_comp first.toMonoidHom second.toMonoidHom).symm)) (Additive.toMul element)

theorem odd_pGroup_square_eq_one {G : Type u} [Group G]
    (prime : ℕ) (hodd : Odd prime) (hpgroup : IsPGroup prime G)
    (element : G) (hsquare : element ^ 2 = 1) : element = 1 := by
  obtain ⟨exponent, hpower⟩ := hpgroup element
  exact (pow_eq_one_iff_of_coprime (hodd.pow.coprime_two_left : Nat.Coprime 2 (prime ^ exponent))).mp
    ⟨hsquare, hpower⟩

theorem odd_pGroup_additive_center_no_two {G : Type u} [Group G]
    (prime : ℕ) (hodd : Odd prime) (hpgroup : IsPGroup prime G)
    (value : Additive (Subgroup.center G)) (hdouble : value + value = 0) : value = 0 := by
  have hsquare : Additive.toMul value ^ 2 = 1 := by
    change Additive.toMul value * Additive.toMul value = 1 at hdouble
    simpa only [pow_two] using hdouble
  exact odd_pGroup_square_eq_one prime hodd (hpgroup.to_subgroup (Subgroup.center G))
    (Additive.toMul value) hsquare

theorem cubic_classTwo_differences_commute {G : Type u} [Group G]
    (prime : ℕ) (hodd : Odd prime) (hpgroup : IsPGroup prime G)
    (hclass : commutator G ≤ Subgroup.center G)
    (first second : MulAut G) (hcommute : Commute first second)
    (hfirstFixed : ∀ element ∈ commutator G, first element = element)
    (hsecondFixed : ∀ element ∈ commutator G, second element = element)
    (element : G)
    (hcubicFirst : first (automorphismDifference second (automorphismDifference first element)) =
      automorphismDifference second (automorphismDifference first element))
    (hcubicSecond : second (automorphismDifference second (automorphismDifference first element)) =
      automorphismDifference second (automorphismDifference first element)) :
    Commute (automorphismDifference first element) (automorphismDifference second element) := by
  have hfixedFirst : additiveAbelianAction first
      (additiveAbelianImage (automorphismDifference second (automorphismDifference first element))) =
        additiveAbelianImage (automorphismDifference second (automorphismDifference first element)) := by
    rw [additiveAbelianAction_image, hcubicFirst]
  have hfixedSecond : additiveAbelianAction second
      (additiveAbelianImage (automorphismDifference second (automorphismDifference first element))) =
        additiveAbelianImage (automorphismDifference second (automorphismDifference first element)) := by
    rw [additiveAbelianAction_image, hcubicSecond]
  simp only [additiveAbelianImage_difference] at hfixedFirst hfixedSecond
  have hvanish := invariant_alternating_pairing_mixed_difference_eq_zero
    (classTwoAdditivePairing hclass) (classTwoAdditivePairing_alternating hclass)
    (odd_pGroup_additive_center_no_two prime hodd hpgroup)
    (additiveAbelianAction first) (additiveAbelianAction second)
    (additiveAbelianAction_commute first second hcommute)
    (classTwoAdditivePairing_invariant hclass first hfirstFixed)
    (classTwoAdditivePairing_invariant hclass second hsecondFixed)
    (additiveAbelianImage element) hfixedFirst hfixedSecond
  rw [← additiveAbelianImage_difference, ← additiveAbelianImage_difference] at hvanish
  apply commutatorElement_eq_one_iff_commute.mp
  have hgroup : (classTwoAbelianPairing hclass
      (Abelianization.of (automorphismDifference first element))
      (Abelianization.of (automorphismDifference second element)) : G) = 1 :=
    congrArg (fun value : Additive (Subgroup.center G) =>
      ((Additive.toMul value : Subgroup.center G) : G)) hvanish
  rwa [classTwoAbelianPairing_apply] at hgroup

theorem cubic_classTwo_generated_differences_abelian
    {actor : Type u} {acted : Type v} [Group actor] [Group acted]
    (prime : ℕ) (hodd : Odd prime) (hpgroup : IsPGroup prime acted)
    (hclass : commutator acted ≤ Subgroup.center acted)
    (habelian : IsMulCommutative actor) (action : actor →* MulAut acted)
    (hfixed : ∀ member element, element ∈ commutator acted → action member element = element)
    (element : acted)
    (hcubic : ∀ first second third : actor,
      automorphismDifference (action third)
        (automorphismDifference (action second) (automorphismDifference (action first) element)) = 1) :
    IsMulCommutative (Subgroup.closure (Set.range (fun member => automorphismDifference (action member) element))) := by
  apply CFSG.subgroup_isMulCommutative_closure
  rintro firstDifference ⟨first, rfl⟩ secondDifference ⟨second, rfl⟩
  have hcommute : Commute (action first) (action second) := by
    change action first * action second = action second * action first
    rw [← map_mul, ← map_mul, isMulCommutative_iff.mp habelian first second]
  have hfixFirst : action first (automorphismDifference (action second)
      (automorphismDifference (action first) element)) =
        automorphismDifference (action second) (automorphismDifference (action first) element) := by
    have heq := hcubic first second first
    change _⁻¹ * _ = 1 at heq
    exact (inv_mul_eq_one.mp heq).symm
  have hfixSecond : action second (automorphismDifference (action second)
      (automorphismDifference (action first) element)) =
        automorphismDifference (action second) (automorphismDifference (action first) element) := by
    have heq := hcubic first second second
    change _⁻¹ * _ = 1 at heq
    exact (inv_mul_eq_one.mp heq).symm
  exact (cubic_classTwo_differences_commute prime hodd hpgroup hclass
    (action first) (action second) hcommute (hfixed first) (hfixed second)
    element hfixFirst hfixSecond).eq

end CFSG.RankThreeEvenClassification.Helpers

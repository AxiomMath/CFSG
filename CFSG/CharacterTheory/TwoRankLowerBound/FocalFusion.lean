module

public import CFSG.CharacterTheory.TwoRankLowerBound.Helpers

public section

open scoped commutatorElement

namespace CFSG.TwoRankLowerBound.Helpers

set_option backward.isDefEq.respectTransparency false in
theorem sylow_focal_eq_self_of_perfect {G : Type*} [Group G] [Finite G]
    [Group.IsPerfect G] (prime : ℕ) [Fact (Nat.Prime prime)] (sylow : Sylow prime G) :
    (sylow : Subgroup G).focalSubgroup = (sylow : Subgroup G) := by
  let quotient := (sylow : Subgroup G) ⧸ (sylow : Subgroup G).focalSubgroupOf
  let : CommGroup quotient := @IsMulCommutative.instCommGroup quotient inferInstance
    (Subgroup.instIsMulCommutativeQuotientSubtypeMemFocalSubgroupOf (sylow : Subgroup G))
  have hkernel := ker_eq_top_of_perfect G quotient (sylow : Subgroup G).transferFocal
  have hintersection := Subgroup.ker_transferFocal_inf_eq_focalSubgroup sylow
  rw [hkernel, top_inf_eq] at hintersection
  exact hintersection.symm

theorem fusion_invariant_hom_trivial_of_perfect_sylow {G target : Type*}
    [Group G] [Finite G] [Group.IsPerfect G] [CommGroup target]
    (prime : ℕ) [Fact (Nat.Prime prime)] (sylow : Sylow prime G)
    (homomorphism : (sylow : Subgroup G) →* target)
    (hfusion : ∀ left right : (sylow : Subgroup G), ∀ conjugator : G,
      conjugator * (left : G) * conjugator⁻¹ = right →
        homomorphism left = homomorphism right) :
    ∀ member : (sylow : Subgroup G), homomorphism member = 1 := by
  have hfocal : (sylow : Subgroup G).focalSubgroupOf ≤ homomorphism.ker := by
    rw [Subgroup.focalSubgroupOf_eq_closure]
    apply (Subgroup.closure_le homomorphism.ker).mpr
    rintro member ⟨left, hleft, conjugator, hequal⟩
    let leftMember : (sylow : Subgroup G) := ⟨left, hleft⟩
    have hconjugateMember : conjugator * left * conjugator⁻¹ ∈ (sylow : Subgroup G) := by
      have hmul := (sylow : Subgroup G).mul_mem
        ((sylow : Subgroup G).inv_mem member.property) hleft
      have hconjugate : (member : G)⁻¹ * left = conjugator * left * conjugator⁻¹ := by
        rw [hequal]
        simp only [commutatorElement_def]
        group
      rwa [hconjugate] at hmul
    let conjugateMember : (sylow : Subgroup G) :=
      ⟨conjugator * left * conjugator⁻¹, hconjugateMember⟩
    have hvalue := hfusion leftMember conjugateMember conjugator rfl
    have hfactor : member = leftMember * conjugateMember⁻¹ := by
      apply Subtype.ext
      rw [hequal]
      change ⁅left, conjugator⁆ = left * (conjugator * left * conjugator⁻¹)⁻¹
      simp only [commutatorElement_def]
      group
    change homomorphism member = 1
    rw [hfactor, map_mul, map_inv, hvalue, mul_inv_cancel]
  have hfocalTop : (sylow : Subgroup G).focalSubgroupOf = ⊤ := by
    rw [Subgroup.focalSubgroupOf_def, sylow_focal_eq_self_of_perfect prime sylow,
      Subgroup.subgroupOf_self]
  intro member
  exact hfocal (hfocalTop ▸ Subgroup.mem_top member)

end CFSG.TwoRankLowerBound.Helpers

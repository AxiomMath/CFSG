module

public import CFSG.Assembly.Defs

public section

open CFSG.Open

namespace CFSG.ComponentClassification.ElementaryInvolutionExtension

theorem cyclic_cases {G : Type*} [Group G] (involution : G) (horder : orderOf involution = 2)
    (member : G) (hmember : member ∈ Subgroup.zpowers involution) : member = 1 ∨ member = involution := by
  obtain ⟨exponent, rfl⟩ := Subgroup.mem_zpowers_iff.mp hmember
  rw [← zpow_mod_orderOf, horder]
  change involution ^ (exponent % (2 : ℤ)) = 1 ∨ involution ^ (exponent % (2 : ℤ)) = involution
  have hcases : exponent % 2 = 0 ∨ exponent % 2 = 1 := by omega
  rcases hcases with hzero | hone
  · simp only [hzero, zpow_zero, true_or]
  · simp only [hone, zpow_one, or_true]

theorem extend {G : Type*} [Group G] [Finite G] (elementary : Subgroup G)
    (helementary : IsElemAbelian 2 elementary) (rank : ℕ) (hcard : Nat.card elementary = 2 ^ rank)
    (involution : G) (horder : orderOf involution = 2) (houtside : involution ∉ elementary)
    (hcommutes : ∀ member ∈ elementary, Commute member involution) :
    IsElemAbelian 2 (elementary ⊔ Subgroup.zpowers involution) ∧
      Nat.card ↥(elementary ⊔ Subgroup.zpowers involution) = 2 ^ (rank + 1) := by
  let cyclic := Subgroup.zpowers involution
  have hcyclicSquare : ∀ member ∈ cyclic, member ^ 2 = 1 := by
    intro member hmember
    rcases cyclic_cases involution horder member hmember with hone | heq
    · rw [hone, one_pow]
    · rw [heq, ← horder]
      exact pow_orderOf_eq_one involution
  have hcommuting : ∀ first : elementary, ∀ second : cyclic, Commute first.val second.val := by
    intro first second
    rcases cyclic_cases involution horder second.val second.property with hone | heq
    · rw [hone]
      exact Commute.one_right _
    · rw [heq]
      exact hcommutes first.val first.property
  let multiplication := elementary.subtype.noncommCoprod cyclic.subtype hcommuting
  have hrange : multiplication.range = elementary ⊔ cyclic := by
    exact (MonoidHom.noncommCoprod_range elementary.subtype cyclic.subtype hcommuting).trans
      (congrArg₂ (fun first second : Subgroup G => first ⊔ second)
        (Subgroup.range_subtype elementary) (Subgroup.range_subtype cyclic))
  have hdisjoint : Disjoint elementary cyclic := by
    apply Subgroup.disjoint_def.mpr
    intro member hfirst hsecond
    rcases cyclic_cases involution horder member hsecond with hone | heq
    · exact hone
    · exact (houtside (heq ▸ hfirst)).elim
  have hinjective : Function.Injective multiplication := by
    apply (MonoidHom.ker_eq_bot_iff _).mp
    apply le_antisymm _ bot_le
    intro pair hpair
    have hproduct : pair.1.val * pair.2.val = 1 := hpair
    have heq : pair.1.val = pair.2.val⁻¹ := (eq_inv_iff_mul_eq_one).mpr hproduct
    have hfirst : pair.1.val = 1 := Subgroup.disjoint_def.mp hdisjoint pair.1.property
      (heq ▸ cyclic.inv_mem pair.2.property)
    have hsecond : pair.2.val = 1 := by simpa only [hfirst, one_mul] using hproduct
    apply Subgroup.mem_bot.mpr
    exact Prod.ext (Subtype.ext hfirst) (Subtype.ext hsecond)
  have hsurjective : Function.Surjective multiplication.rangeRestrict := multiplication.rangeRestrict_surjective
  have hrangeElementary : IsElemAbelian 2 multiplication.range := by
    refine ⟨isMulCommutative_iff.mpr ?_, ?_⟩
    · intro first second
      obtain ⟨firstPair, rfl⟩ := hsurjective first
      obtain ⟨secondPair, rfl⟩ := hsurjective second
      rw [← map_mul, ← map_mul]
      apply congrArg multiplication.rangeRestrict
      let : IsMulCommutative elementary := helementary.1
      exact mul_comm' firstPair secondPair
    · intro member hmember
      obtain ⟨pair, hpair⟩ := MonoidHom.mem_range.mp hmember
      rw [← hpair, ← map_pow]
      have hpairSquare : pair ^ 2 = 1 := Prod.ext
        (Subtype.ext (helementary.2 pair.1.val pair.1.property))
        (Subtype.ext (hcyclicSquare pair.2.val pair.2.property))
      rw [hpairSquare, map_one]
  have hsize : Nat.card multiplication.range = 2 ^ (rank + 1) := by
    have hinjectiveRange : Function.Injective multiplication.rangeRestrict :=
      MonoidHom.rangeRestrict_injective_iff.mpr hinjective
    rw [← Nat.card_congr (MulEquiv.ofBijective multiplication.rangeRestrict
      ⟨hinjectiveRange, hsurjective⟩).toEquiv, Nat.card_prod, hcard, Nat.card_zpowers, horder, pow_succ]
  exact ⟨hrange ▸ hrangeElementary, hrange ▸ hsize⟩

end CFSG.ComponentClassification.ElementaryInvolutionExtension

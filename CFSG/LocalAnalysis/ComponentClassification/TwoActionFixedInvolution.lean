module

public import CFSG.LocalAnalysis.ComponentClassification.InvolutionFixedPoints

public section

namespace CFSG.ComponentClassification.TwoActionFixedInvolution

theorem involution_card_odd {G : Type*} [Group G] [Finite G]
    (heven : Even (Nat.card G)) : Odd (Nat.card {member : G // orderOf member = 2}) := by
  classical
  let inverse := Function.Involutive.toPerm (fun member : G => member⁻¹) inv_inv
  have hmod := InvolutionFixedPoints.fixed_card_mod_two inverse inv_inv
  let decomposition : {member : G // inverse member = member} ≃
      Unit ⊕ {member : G // orderOf member = 2} :=
    { toFun := fun member => if hone : member.val = 1 then Sum.inl () else
        Sum.inr ⟨member.val, orderOf_eq_prime (by
          have hinverse : member.val⁻¹ = member.val := member.property
          rw [pow_two]
          exact (congrArg (fun value : G => value * member.val) hinverse).symm.trans
            (inv_mul_cancel member.val)) hone⟩
      invFun := fun member => match member with
        | Sum.inl _ => ⟨1, inv_one⟩
        | Sum.inr member => ⟨member.val, inv_eq_self_of_orderOf_eq_two member.property⟩
      left_inv := by
        intro member
        by_cases hone : member.val = 1
        · simp only [dite_eq_left hone]
          exact Subtype.ext hone.symm
        · simp only [dite_eq_right hone]
      right_inv := by
        intro member
        cases member with
        | inl singleton => cases singleton; simp
        | inr member =>
            have hne : member.val ≠ 1 := by
              intro hone
              have horder := member.property
              rw [hone, orderOf_one] at horder
              omega
            simp only [dite_eq_right hne] }
  have hcard : Nat.card {member : G // inverse member = member} =
      1 + Nat.card {member : G // orderOf member = 2} := by
    rw [Nat.card_congr decomposition, Nat.card_sum]
    have hunit : Nat.card Unit = 1 := Nat.card_eq_one_iff_unique.mpr ⟨inferInstance, inferInstance⟩
    rw [hunit]
  have hevenMod := Nat.even_iff.mp heven
  apply Nat.odd_iff.mpr
  omega

@[expose, instance_reducible] noncomputable def action {A G : Type*} [Group A] [Group G]
    (homomorphism : A →* MulAut G) : MulAction A {member : G // orderOf member = 2} where
  smul actor member := ⟨(homomorphism actor) member.val,
    (orderOf_injective (homomorphism actor).toMonoidHom (homomorphism actor).injective member.val).trans member.property⟩
  one_smul member := Subtype.ext (congrArg (fun automorphism : MulAut G => automorphism member.val) homomorphism.map_one)
  mul_smul first second member := Subtype.ext
    (congrArg (fun automorphism : MulAut G => automorphism member.val) (homomorphism.map_mul first second))

theorem exists_fixed {A G : Type*} [Group A] [Group G] [Finite G]
    (htwo : IsPGroup 2 A) (heven : Even (Nat.card G)) (homomorphism : A →* MulAut G) :
    ∃ member : G, orderOf member = 2 ∧ ∀ actor : A, (homomorphism actor) member = member := by
  let := action homomorphism
  have hnot : ¬ 2 ∣ Nat.card {member : G // orderOf member = 2} := by
    have hodd := Nat.odd_iff.mp (involution_card_odd heven)
    intro hdivides
    have heven := Nat.mod_eq_zero_of_dvd hdivides
    omega
  obtain ⟨member, hfixed⟩ := htwo.nonempty_fixed_point_of_prime_not_dvd_card
    {member : G // orderOf member = 2} hnot
  exact ⟨member.val, member.property,
    fun actor => congrArg Subtype.val (MulAction.mem_fixedPoints.mp hfixed actor)⟩

end CFSG.ComponentClassification.TwoActionFixedInvolution

module

public import CFSG.GH74.Generic.S3.Leaves
public import CFSG.GH74.Generic.S3.ReflLin
public import CFSG.GH74.Generic.S3.ReflUni

public section

namespace CFSG.GH74.Generic.S3

open CFSG CFSG.GH74 CFSG.GH74.Generic Subgroup

theorem ringChar_ne_two_of_odd_card {F : Type} [Field F] [Finite F] (h : Odd (Nat.card F)) :
    ringChar F ≠ 2 := by
  intro hc
  have h2F : (2 : F) ≠ 0 := CFSG.ClassicalInvolution.Models.two_ne_zero_of_odd_natCard h
  apply h2F
  have := ringChar.of_eq hc
  simpa using CharP.cast_eq_zero F 2

theorem b_S3_L4Reflection_lin : B_S3_L4Reflection_lin := by
  intro G _ _ hG F _ _ p f hp hp2 hF hq hq4 x z u Y hx hA3 hRefl
  have hchar := ringChar_ne_two_of_odd_card (F := F)
    (by rw [hF]; exact (hp.odd_of_ne_two hp2).pow)
  obtain ⟨j, hjY, hjj, hconj⟩ := exists_refl_conj_lin hA3 p f hp hp2 hF hq hq4
  obtain ⟨g1, hg1, hg1z⟩ := hA3.exists_noncommuting p f hp hp2 hF hq
  obtain ⟨hiso, hz0, hz2, hu1, -, -, hY02, -, -⟩ := hA3
  obtain ⟨e0⟩ := hiso 0
  obtain ⟨e2⟩ := hiso 2
  have hz1 : z ≠ 1 := fun h => by
    have := hz0.2.1
    rw [h, orderOf_one] at this
    omega
  have hzz : z * z = 1 := by
    have := pow_orderOf_eq_one z
    rwa [hz0.2.1, pow_two] at this
  have huu : u * u = 1 := by
    have := pow_orderOf_eq_one u
    rwa [hu1.2.1, pow_two] at this
  have hxx : x * x = 1 := by
    have := pow_orderOf_eq_one x
    rwa [hx, pow_two] at this
  have hx1 : x ≠ 1 := fun h => by
    rw [h, orderOf_one] at hx
    omega
  exact not_gen4_of_reflection hchar e0 e2 hY02 hz0.1 hz2.1 hz0.2.2 hz2.2.2 hz1 hzz huu hxx hx1
    hRefl.1 hRefl.2.1 hRefl.2.2 ⟨g1, hg1, hg1z⟩ hjY hjj hconj hG

theorem b_S3_L4Reflection_uni : B_S3_L4Reflection_uni := by
  intro G _ _ hG F₂ F _ _ _ _ p f hp hp2 hF₂ hF hq hq4 x z u Y hx hA3 hRefl
  have : Fact p.Prime := ⟨hp⟩
  have : CharP F₂ p :=
    CFSG.SectionRank.ClassicalOdd.charP_of_card (p := p) (f := f * 2) (by rw [hF₂, pow_mul])
  have hchar := ringChar_ne_two_of_odd_card (F := F)
    (by rw [hF]; exact (hp.odd_of_ne_two hp2).pow)
  obtain ⟨j, hjY, hjj, hconj⟩ := exists_refl_conj_uni p f hA3 hp2 hF₂ hF hq hq4
  obtain ⟨g1, hg1, hg1z⟩ := hA3.exists_noncommuting hF₂ hF hp2 hq
  obtain ⟨hiso, hz0, hz2, hu1, -, -, hY02, -, -⟩ := hA3
  obtain ⟨e0⟩ := hiso 0
  obtain ⟨e2⟩ := hiso 2
  have hz1 : z ≠ 1 := fun h => by
    have := hz0.2.1
    rw [h, orderOf_one] at this
    omega
  have hzz : z * z = 1 := by
    have := pow_orderOf_eq_one z
    rwa [hz0.2.1, pow_two] at this
  have huu : u * u = 1 := by
    have := pow_orderOf_eq_one u
    rwa [hu1.2.1, pow_two] at this
  have hxx : x * x = 1 := by
    have := pow_orderOf_eq_one x
    rwa [hx, pow_two] at this
  have hx1 : x ≠ 1 := fun h => by
    rw [h, orderOf_one] at hx
    omega
  exact not_gen4_of_reflection hchar e0 e2 hY02 hz0.1 hz2.1 hz0.2.2 hz2.2.2 hz1 hzz huu hxx hx1
    hRefl.1 hRefl.2.1 hRefl.2.2 ⟨g1, hg1, hg1z⟩ hjY hjj hconj hG

theorem b_S3_L4Reflection : B_S3_L4Reflection :=
  ⟨b_S3_L4Reflection_lin, b_S3_L4Reflection_uni⟩

end CFSG.GH74.Generic.S3

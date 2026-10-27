module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.GzOrbit.Card

public section

namespace CFSG.EvenSporadicStandard.HNRecog.Section3

open CFSG.EvenSporadicStandard.HNRecog

theorem y4a_exists_hom {X : Type} [Group X] (hX : IsShapeTwoTwoTimesTwoFourA5 X) :
    ∃ π : X →* alternatingGroup (Fin 5), Function.Surjective π ∧ Nat.card ↥π.ker = 64 ∧
      ∀ k₁ ∈ π.ker, ∀ k₂ ∈ π.ker, k₁ * k₂ = k₂ * k₁ := by
  have hXcard : Nat.card X = 3840 := card_of_isShapeTwoTwoTimesTwoFourA5 hX
  obtain ⟨Y, _, ⟨N, hNnorm, ⟨eN⟩, ⟨eQ⟩⟩, ⟨e⟩⟩ := hX
  haveI : N.Normal := hNnorm
  set π : X →* alternatingGroup (Fin 5) :=
    (eQ.toMonoidHom).comp ((QuotientGroup.mk' N).comp
      ((MonoidHom.snd (Elem2 2) Y).comp e.toMonoidHom)) with hπ
  have hsurj : Function.Surjective π := by
    intro y
    obtain ⟨q, hq⟩ := eQ.surjective y
    obtain ⟨w, hw⟩ := QuotientGroup.mk'_surjective N q
    obtain ⟨x, hx⟩ := e.surjective (1, w)
    refine ⟨x, ?_⟩
    rw [hπ]
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, hx]
    simp [hw, hq]
  have hmem : ∀ k : X, k ∈ π.ker → (e k).2 ∈ N := by
    intro k hk
    rw [MonoidHom.mem_ker, hπ] at hk
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MonoidHom.coe_snd,
      QuotientGroup.mk'_apply] at hk
    rwa [MulEquiv.map_eq_one_iff, QuotientGroup.eq_one_iff] at hk
  have hN : ∀ n₁ ∈ N, ∀ n₂ ∈ N, n₁ * n₂ = n₂ * n₁ := by
    intro n₁ h₁ n₂ h₂
    have h' : (⟨n₁, h₁⟩ : ↥N) * ⟨n₂, h₂⟩ = ⟨n₂, h₂⟩ * ⟨n₁, h₁⟩ :=
      eN.injective (by rw [map_mul, map_mul, mul_comm])
    exact congrArg Subtype.val h'
  refine ⟨π, hsurj, ?_, ?_⟩
  · have h := Subgroup.card_ker_mul_card_of_surjective (f := π) hsurj
    have h60 : Nat.card (alternatingGroup (Fin 5)) = 60 := by
      rw [nat_card_alternatingGroup, Nat.card_fin]
      decide
    rw [hXcard, h60] at h
    omega
  · intro k₁ hk₁ k₂ hk₂
    apply e.injective
    rw [map_mul, map_mul]
    refine Prod.ext ?_ ?_
    · simp only [Prod.fst_mul]
      exact mul_comm _ _
    · simp only [Prod.snd_mul]
      exact hN _ (hmem k₁ hk₁) _ (hmem k₂ hk₂)

end CFSG.EvenSporadicStandard.HNRecog.Section3

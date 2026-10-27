module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.Lemma37.RankOneRoot

public section

namespace CFSG.ProperTwoGeneratedCore.Lemma37

open CFSG.Open CFSG.ProperTwoGeneratedCore.Assembly

theorem quaternionTwo_exists_inv_conj : ∀ g : QuaternionGroup 2, g * g ≠ 1 →
    ∃ k : QuaternionGroup 2, k * g * k⁻¹ = g⁻¹ ∧ k * k = .a 2 := by
  decide

theorem involution_pair_identities {X : Type*} [Group X] {u b c b' c' : X} (hu2 : u * u = 1)
    (hbc : b * c * b⁻¹ = c⁻¹) (hbc' : b' * c' * b'⁻¹ = c'⁻¹) (hb : b * b = u)
    (hb' : b' * b' = u) (hc : c * c = u) (h1 : Commute b b') (h2 : Commute b c')
    (h3 : Commute c b') (h4 : Commute c c') (ht : c * c' * (c * c') = 1) :
    (b * b') * (b * b') = 1 ∧ (b * b' * c) * (b * b' * c) = 1 ∧
      Commute (b * b') (c * c') ∧ Commute (b * b' * c) (c * c') ∧
      ((b * b') * (b * b' * c)) ^ 2 = u := by
  have hbc2 : b * c = c⁻¹ * b := by rw [← hbc]; group
  have hbc2' : b' * c' = c'⁻¹ * b' := by rw [← hbc']; group
  have hinv : c⁻¹ * c'⁻¹ = c * c' := by
    rw [h4.inv_inv.eq, ← mul_inv_rev]
    exact inv_eq_of_mul_eq_one_right ht
  have hi1 : (b * b') * (b * b') = 1 := by
    calc (b * b') * (b * b') = b * (b' * b) * b' := by group
      _ = b * (b * b') * b' := by rw [← h1.eq]
      _ = (b * b) * (b' * b') := by group
      _ = 1 := by rw [hb, hb', hu2]
  have hi : Commute (b * b') (c * c') := by
    calc b * b' * (c * c') = b * (b' * c) * c' := by group
      _ = b * (c * b') * c' := by rw [← h3.eq]
      _ = (b * c) * (b' * c') := by group
      _ = (c⁻¹ * b) * (c'⁻¹ * b') := by rw [hbc2, hbc2']
      _ = c⁻¹ * (b * c'⁻¹) * b' := by group
      _ = c⁻¹ * (c'⁻¹ * b) * b' := by rw [h2.inv_right.eq]
      _ = (c⁻¹ * c'⁻¹) * (b * b') := by group
      _ = c * c' * (b * b') := by rw [hinv]
  refine ⟨hi1, ?_, hi, hi.mul_left ((Commute.refl c).mul_right h4), ?_⟩
  · calc b * b' * c * (b * b' * c) = b * (b' * c) * b * b' * c := by group
      _ = b * (c * b') * b * b' * c := by rw [← h3.eq]
      _ = b * c * (b' * b) * b' * c := by group
      _ = b * c * (b * b') * b' * c := by rw [← h1.eq]
      _ = (b * c) * b * (b' * b') * c := by group
      _ = (c⁻¹ * b) * b * (b' * b') * c := by rw [hbc2]
      _ = c⁻¹ * (b * b) * (b' * b') * c := by group
      _ = c⁻¹ * (u * u) * c := by rw [hb, hb']; group
      _ = 1 := by rw [hu2]; group
  · rw [← mul_assoc, hi1, one_mul, pow_two, hc]

variable {G : Type} [Group G] [Finite G] {S : Sylow 2 G} {H : Subgroup G} {z : G}
  {J : Subgroup (EscapingQuotient z)}

namespace RankOneSetting

variable (h : RankOneSetting G S H z J)
include h

theorem eq_one_or_eq_bar_of_sq_eq_one {a : EscapingQuotient z} (haJ : a ∈ J) (ha : a ^ 2 = 1) :
    a = 1 ∨ a = escapingBar z := by
  by_cases ha1 : a = 1
  · exact Or.inl ha1
  · exact Or.inr (h.unique a haJ (orderOf_eq_prime ha ha1))

theorem sq_eq_of_mem_sylowImage_inf
    {a : EscapingQuotient z} (haS : a ∈ escapingSylowImage S z)
    (haJ : a ∈ J) : a ^ 2 = 1 ∨ a ^ 2 = escapingBar z := by
  by_cases ha1 : a ^ 2 = 1
  · exact Or.inl ha1
  · refine Or.inr (h.unique _ (Subgroup.pow_mem _ haJ 2) (orderOf_eq_prime ?_ ha1))
    rw [← pow_mul]
    exact h.pow_four_eq_one haS haJ

theorem exists_inv_conj_of_sq_eq_bar
    {c : EscapingQuotient z} (hcS : c ∈ escapingSylowImage S z)
    (hcJ : c ∈ J) (hc2 : c ^ 2 = escapingBar z) :
    ∃ b ∈ escapingSylowImage S z, b ∈ J ∧ b * c * b⁻¹ = c⁻¹ ∧ b ^ 2 = escapingBar z := by
  obtain ⟨P, hP⟩ := h.exists_sylow_inf h.component
  obtain ⟨eP⟩ := h.sylow_mulEquiv_quaternion_two P
  obtain ⟨g, rfl⟩ := exists_quaternionElt_eq P hP eP hcS hcJ
  have hg : g * g ≠ 1 := fun h1 => h.bar_ne_one (by
    rw [← hc2, pow_two, ← quaternionElt_mul, h1]
    simp [quaternionElt])
  obtain ⟨k, hk, hk2⟩ := quaternionTwo_exists_inv_conj g hg
  refine ⟨quaternionElt P eP k, quaternionElt_mem_sylowImage P hP eP k,
    quaternionElt_mem P eP k, ?_, ?_⟩
  · have := congrArg (quaternionElt P eP) hk
    simpa [quaternionElt] using this
  · rw [pow_two, ← quaternionElt_mul, hk2, h.quaternionElt_a_two P eP]

end RankOneSetting

end CFSG.ProperTwoGeneratedCore.Lemma37

module

public import CFSG.LocalAnalysis.ComponentClassification.Asc76YSec4Induction

public section

namespace CFSG.ComponentClassification.Asc76.Sec4

open Subgroup CFSG.ABGLocalTools CFSG.ComponentClassification.AschbacherTightEmbedding
  CFSG.ComponentClassification.AS76b CFSG.ComponentClassification.AschbacherTheorem3

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}

@[expose] def Lemma42 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (Ω : Set (Subgroup G)), Assumption41 Ω → ∀ K ∈ Ω,
    twoPrimeLayerIn K ≠ oddCoreIn K → K.Normal

theorem isTwoNil_of_isTwoNil {K R R' : Subgroup G} (hR : IsSylowOf 2 R K)
    (hR' : IsSylowOf 2 R' K) (h : IsTwoNil K R) : IsTwoNil K R' := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨k, hk, hkR⟩ := CFSG.ComponentClassification.Asc76.L26.IsSylowOf.exists_conj_mem hR hR'
  have hReq : R' = AschbacherTightEmbedding.rightConjugate R k⁻¹ := by
    ext x
    rw [hkR, mem_rightConjugate_iff, inv_inv]
  rw [hReq]
  exact h.rightConjugate (inv_mem hk)

theorem asc76Theorem5_of (h22 : Asc76Lemma22) (h1 : Asc76Theorem1) (h42 : Lemma42)
    (hflat : Thm5Flat) : Asc76Theorem5 := by
  intro G _ _ Ω hΩ S hS
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  by_cases hnorm : ∃ K ∈ Ω, K.Normal
  · exact Or.inl hnorm
  push Not at hnorm
  right
  have hlayer : ∀ K ∈ Ω, twoPrimeLayerIn K = oddCoreIn K := fun K hK => by
    by_contra hne
    exact hnorm K hK (h42 G Ω hΩ K hK hne)
  have hnil : ∀ K ∈ Ω, ∀ R, IsSylowOf 2 R K → IsTwoNil K R := by
    intro K hK R hR
    by_contra hR0
    have hall : ∀ R', IsSylowOf 2 R' K → ¬ IsTwoNil K R' := fun R' hR' h =>
      hR0 (isTwoNil_of_isTwoNil hR' hR h)
    exact hnorm K hK (normal_of_not_twoNil h22 h1 hΩ hK (hlayer K hK) hall)
  exact conclusion2_of_normal h22 hΩ hS hnil (hflat G Ω hΩ hnil S hS)

end CFSG.ComponentClassification.Asc76.Sec4

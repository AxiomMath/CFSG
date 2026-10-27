module

public import CFSG.LocalAnalysis.ComponentClassification.Asc76S5C1g
public import CFSG.LocalAnalysis.ComponentClassification.Asc76S5C1f

public section

namespace CFSG.ComponentClassification.Asc76.Sec5

open Subgroup CFSG.Open CFSG.ABGLocalTools CFSG.ComponentClassification.AschbacherTightEmbedding
  CFSG.ComponentClassification.AS76b CFSG.ComponentClassification.AschbacherTheorem3

variable {G : Type} [Group G] [Finite G]

theorem Overlap.star {A R T : Subgroup G} {g : G} (h : Overlap A R g T)
    (H : ∀ (x : G) (V : Subgroup G), Overlap A R x V →
      IsSylowOf 2 V (rightConjugate (centralizer (A : Set G)) x) ∨
        R ⊓ centralizer (V : Set G) = R ⊓ centralizer (T : Set G))
    (hJN : normalizer (centralizer (A : Set G) : Set G) ≤ normalizer
      (oUpperTwoPrime (R ⊓ centralizer (T : Set G) ⊔ oddCoreIn (centralizer (A : Set G))) :
        Set G)) :
    ∀ y : G, Even (Nat.card (rightConjugate (oUpperTwoPrime
      (R ⊓ centralizer (T : Set G) ⊔ oddCoreIn (centralizer (A : Set G)))) y ⊓ normalizer
        (oUpperTwoPrime (R ⊓ centralizer (T : Set G) ⊔ oddCoreIn (centralizer (A : Set G))) :
          Set G) : Subgroup G)) →
      ∃ S : Subgroup G, IsSylowOf 2 S (rightConjugate (oUpperTwoPrime
        (R ⊓ centralizer (T : Set G) ⊔ oddCoreIn (centralizer (A : Set G)))) y) ∧
        S ≤ normalizer (oUpperTwoPrime
          (R ⊓ centralizer (T : Set G) ⊔ oddCoreIn (centralizer (A : Set G))) : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set K := centralizer (A : Set G) with hKdef
  set C := R ⊓ centralizer (T : Set G) with hCdef
  set J₀ := oUpperTwoPrime (C ⊔ oddCoreIn K) with hJ₀def
  have hNA : normalizer (K : Set G) = normalizer (A : Set G) := normalizer_centralizer_eq h.standard
  have hCK : C ≤ K := inf_le_left.trans h.sylowR.le
  have hCp : IsPGroup 2 C := h.sylowR.isPGroup.to_le inf_le_left
  obtain ⟨hCsyl, hCJ₀⟩ := isSylowOf_oUpperTwoPrime_sup hCK hCp
  have hJ₀K : J₀ ≤ K := (oUpperTwoPrime_le _).trans (sup_le hCK (oddCoreIn_le K))
  have hC1 : C ≠ ⊥ := by
    intro hb
    have h1 := h.card_inf_centralizer
    rw [← hCdef, hb, card_bot] at h1
    exact h.ne_bot (card_eq_one.mp h1.symm)
  have hJ₀even : Even (Nat.card J₀) := even_iff_two_dvd.mpr
    ((even_card_of_isPGroup hCp hC1).two_dvd.trans (card_dvd_of_le hCJ₀))
  have hJ₀N' : normalizer (J₀ : Set G) ≤ normalizer (K : Set G) :=
    normalizer_le_normalizer_of_tightlyEmbedded h.tight hJ₀K hJ₀even
  have hNeq : normalizer (J₀ : Set G) = normalizer (K : Set G) := le_antisymm hJ₀N' hJN
  have hKJ₀ : K ≤ normalizer (J₀ : Set G) := le_normalizer.trans hJN
  intro y heven
  by_cases hy : y ∈ normalizer (K : Set G)
  · have hJy : rightConjugate J₀ y = J₀ := (rightConjugate_eq_self_iff J₀ y).mpr (hJN hy)
    refine ⟨C, by rw [hJy]; exact hCsyl, hCJ₀.trans le_normalizer⟩
  have hKy : rightConjugate J₀ y ⊓ normalizer (J₀ : Set G) ≤
      rightConjugate K y ⊓ normalizer (K : Set G) := by
    rw [hNeq]
    exact inf_le_inf_right _ (rightConjugate_le_rightConjugate hJ₀K y)
  have heven' : Even (Nat.card (rightConjugate K y ⊓ normalizer (K : Set G) : Subgroup G)) :=
    even_iff_two_dvd.mpr (heven.two_dvd.trans (card_dvd_of_le hKy))
  obtain ⟨V, hV⟩ := exists_isSylowOf 2 (rightConjugate K y ⊓ normalizer (K : Set G))
  have hV1 : V ≠ ⊥ := isSylowOf_ne_bot_of_even hV heven'
  have hyA : y⁻¹ ∉ normalizer (A : Set G) := by
    rw [← hNA]
    exact fun h' => hy (by simpa using inv_mem h')
  have hV' : IsSylowOf 2 (rightConjugate V y⁻¹) (K ⊓
      normalizer (rightConjugate K y⁻¹ : Set G)) := by
    have h1 := isSylowOf_rightConjugate hV y⁻¹
    rwa [AschbacherTheorem3.rightConjugate_inf, rightConjugate_mul, mul_inv_cancel,
      rightConjugate_one, AschbacherTheorem3.rightConjugate_normalizer] at h1
  have hV'1 : rightConjugate V y⁻¹ ≠ ⊥ := fun hb => hV1 ((rightConjugate_eq_bot_iff).mp hb)
  have hVy : rightConjugate (rightConjugate V y⁻¹) y = V := by
    rw [rightConjugate_mul, inv_mul_cancel, rightConjugate_one]
  have hVN : V ≤ normalizer (J₀ : Set G) := by
    rw [hNeq]
    exact hV.le.trans inf_le_right
  rcases h.isSylowOf_or_eq_rightConjugate H hyA hV' hV'1 with hs | ⟨k, hk, hVk⟩
  ·
    have hVs : IsSylowOf 2 V (rightConjugate K y) := by
      have h1 := isSylowOf_rightConjugate hs y
      rwa [hVy] at h1
    refine ⟨V ⊓ rightConjugate J₀ y, hVs.inf_of_le_normalizer
      (rightConjugate_le_rightConjugate hJ₀K y) ?_, inf_le_left.trans hVN⟩
    rw [← AschbacherTheorem3.rightConjugate_normalizer]
    exact rightConjugate_le_rightConjugate hKJ₀ y
  ·
    have hJk : rightConjugate J₀ k = J₀ := (rightConjugate_eq_self_iff J₀ k).mpr (hKJ₀ hk)
    have hCk : IsSylowOf 2 (rightConjugate C k) J₀ := by
      have h1 := isSylowOf_rightConjugate hCsyl k
      rwa [hJk] at h1
    refine ⟨V, ?_, hVN⟩
    have h1 := isSylowOf_rightConjugate hCk y
    rwa [← hVk, hVy] at h1

end CFSG.ComponentClassification.Asc76.Sec5

module

public import CFSG.LocalAnalysis.ComponentClassification.CatFC.KGHS3Classical
public import CFSG.LocalAnalysis.ComponentClassification.CatFC.KGHS3ExcSmall
public import CFSG.LocalAnalysis.ComponentClassification.CatFC.KGHS3G2
public import CFSG.LocalAnalysis.ComponentClassification.CatFC.KGHS3TD4
public import CFSG.LocalAnalysis.ComponentClassification.CatFC.KGHS3Char3

public section

namespace CFSG.ComponentClassification.CatFC.KGHS3

open Subgroup CFSG.Open CFSG.Blueprint CFSG.EvenSmallLie.CatalogOrders



theorem false_of_lieOrd_char_three {S : Type} [Group S] [Finite S] {t : StatedLieTag}
    {n f : ℕ} (hadm : StatedLieAdmissible t n 3 f) (hcard : Nat.card S = lieOrd t n (3 ^ f))
    (h3 : (Nat.card S).factorization 3 ≤ 4) (hdvd : 44352000 ∣ Nat.card S) : False := by
  have hpos : 0 < Nat.card S := Nat.card_pos
  have hlt := lieOrd_lt_hs_of_char_three hadm (lieMin_le_of_admissible hadm)
    (hcard ▸ h3) (hcard ▸ hpos.ne')
  have hle := Nat.le_of_dvd hpos hdvd
  rw [← hcard] at hlt
  omega

theorem false_of_lie_model {S : Type} [Group S] [Finite S] (hSimple : IsSimpleGroup S)
    (h3 : (Nat.card S).factorization 3 ≤ 4) (K : Subgroup S) (hK : HSType ↥K)
    (hLie : Milestones.ClassicalRep S ∨ ExceptionalRep S) : False := by
  have hdvd := hK.dvd_card
  rcases hLie with ⟨t, n, p, f, hM⟩ | hExc
  · by_cases hp3 : p = 3
    · subst hp3
      exact false_of_lieOrd_char_three hM.1 (card_eq_lieOrd_of_classical hM) h3 hdvd
    · exact no_hsType_statedClassical hp3 h3 hM K hK
  · rcases hExc with ⟨t, p, f, ht, hM⟩ | ⟨t, p, f, ht, hM⟩ | ⟨p, f, hM⟩
    · by_cases hp3 : p = 3
      · subst hp3
        exact false_of_lieOrd_char_three (n := 0) hM.1 (card_eq_lieOrd_of_exceptional hM) h3 hdvd
      · simp only [chevalleyExceptionalTags, Finset.mem_insert, Finset.mem_singleton] at ht
        rcases ht with rfl | rfl | rfl | rfl | rfl | rfl | rfl
        · exact no_hsType_chevalley_G2 hSimple hp3 hM K hK
        · exact no_hsType_chevalley_large (Or.inl rfl) hp3 h3 hM K hK
        · exact no_hsType_chevalley_large (Or.inr (Or.inl rfl)) hp3 h3 hM K hK
        · exact no_hsType_chevalley_large (Or.inr (Or.inr (Or.inr (Or.inl rfl)))) hp3 h3 hM K hK
        · exact no_hsType_chevalley_large (Or.inr (Or.inr (Or.inr (Or.inr rfl)))) hp3 h3 hM K hK
        · exact no_hsType_chevalley_large (Or.inr (Or.inr (Or.inl rfl))) hp3 h3 hM K hK
        · exact no_hsType_chevalley_D4 hp3 hM K hK
    · simp only [reeTitsTags, Finset.mem_insert, Finset.mem_singleton] at ht
      rcases ht with rfl | rfl | rfl
      · obtain ⟨hp3, -, hc⟩ := card_eq_lieOrd_of_ree hM
        subst hp3
        exact false_of_lieOrd_char_three (n := 0) hM.1 hc h3 hdvd
      · exact no_hsType_reeTits (Or.inl rfl) h3 hM K hK
      · exact no_hsType_reeTits (Or.inr rfl) h3 hM K hK
    · exact no_hsType_suzuki hM K hK

end CFSG.ComponentClassification.CatFC.KGHS3

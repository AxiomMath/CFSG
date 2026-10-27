module

public import CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.A10Defs
public import CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.I1434Defs
public import CFSG.RankThree.PartOne.S11d.PlaneCases
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.RankThree.PartOne.S8.Statements

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor

open CFSG.Open CFSG.RankThree.PartOne

theorem kFactI1434_of_cases (hBridge : TauCetiCatalogBridge)
    (hAlt : I1434AltCase) (hSpor : I1434SporCase) (hDef : I1434DefCase) (hExc : I1434ExcCase)
    (hCl : I1434ClassicalCase) : KFactI1434 := by
  intro K _ _ hs hnab hcat Q hrank hab x hxQ hx1 hx5 J₁ J₂ hne h₁ h₂ hlayer hA₁ hA₂ hd
  haveI : IsSimpleGroup K := hs
  have hD : I1434.Data K Q x J₁ J₂ :=
    ⟨hrank, hab, hxQ, hx1, hx5, ⟨hne, h₁, h₂, hlayer, hA₁, hA₂⟩⟩
  rcases PlaneCases.catalog_cases (hBridge K hnab hcat) with
    ⟨q, hq, ⟨e⟩⟩ | ⟨n, hn5, ⟨e⟩⟩ | ⟨t, n, ℓ, f, hadm, hmodel⟩ | hsp
  · exfalso
    obtain ⟨a, b, hab'⟩ := hnab
    exact hab' (e.injective (by rw [map_mul, map_mul, mul_comm]))
  · exact (hAlt K n hn5 ⟨e⟩ Q x J₁ J₂ hD).elim
  · by_cases hℓ : ℓ = 5
    · subst hℓ
      exact (hDef K t n f hadm hmodel Q x J₁ J₂ hD).elim
    · have hmodel' := hmodel
      rcases hmodel with ⟨ht, hm⟩ | ⟨hn, ht, hm⟩ | ⟨hn, ht, hm⟩ | ⟨hn, ht, hm⟩
      · exact hCl K t n ℓ f hm hℓ hs hnab Q x J₁ J₂ hD hd
      · subst hn
        have ht' : t = .G2 ∨ t = .F4 ∨ t = .E6 ∨ t = .E7 ∨ t = .E8 ∨ t = .twistedE6 ∨
            t = .trialityD4 := by
          simpa [CFSG.Blueprint.chevalleyExceptionalTags] using ht
        exact (hExc K t ℓ f (by rcases ht' with h | h | h | h | h | h | h <;> simp [h]) hmodel' hℓ
          Q hab hrank).elim
      · subst hn
        have ht' : t = .twistedG2 ∨ t = .twistedF4 ∨ t = .Tits := by
          simpa [CFSG.Blueprint.reeTitsTags] using ht
        exact (hExc K t ℓ f (by rcases ht' with h | h | h <;> simp [h]) hmodel' hℓ Q hab
          hrank).elim
      · subst hn
        subst ht
        exact (hExc K _ ℓ f (by simp) hmodel' hℓ Q hab hrank).elim
  · exact (hSpor K hsp Q x J₁ J₂ hD).elim

end CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor

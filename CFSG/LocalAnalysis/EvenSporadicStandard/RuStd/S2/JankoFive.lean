module

public import CFSG.LocalAnalysis.EvenSporadicStandard.RuStd.S2.JankoTransport
public import CFSG.LocalAnalysis.EvenSporadicStandard.RuStd.S2.JankoFiveCard

public section

namespace CFSG.EvenSporadicStandard.RuStd.S2

open Subgroup

theorem janko_five_dvd {G : Type} [Group G] [Finite G] {f t r r₁ : G} {D E : Subgroup G}
    (hf5 : orderOf f = 5) (ht2 : orderOf t = 2) (hft : f * t = t * f)
    (hD : Nonempty (↥D ≃* A5)) (hDf : D ≤ centralizer ({f} : Set G))
    (hDt : D ≤ centralizer ({t} : Set G)) (hDdisj : Disjoint (zpowers f) D)
    (htD : t ∉ zpowers f ⊔ D)
    (hCt : centralizer ({f} : Set G) ⊓ centralizer ({t} : Set G) = zpowers t ⊔ (zpowers f ⊔ D))
    (hE : E ≤ centralizer ({f} : Set G)) (hE8 : Nat.card E = 8) (hE2 : ∀ x ∈ E, x * x = 1)
    (htE : t ∈ E) (hr : r ∈ centralizer ({f} : Set G)) (hrE : r ∈ normalizer (E : Set G))
    (hr₁ : r₁ ∈ centralizer ({f} : Set G)) (hr₁E : r₁ ∈ normalizer (E : Set G))
    (hr3 : orderOf r = 3) (hr₁3 : orderOf r₁ = 3)
    (htrans : ∀ e ∈ E, e ≠ 1 → ∀ e' ∈ E, e' ≠ 1 →
      ∃ y ∈ closure ({r, r₁} : Set G), y * e * y⁻¹ = e')
    {r' : G} (hr' : r' ∈ centralizer ({f} : Set G)) (hr'3 : orderOf r' = 3) :
    25 ∣ Nat.card ↥(centralizer ({f} : Set G) ⊓ centralizer ({r'} : Set G)) := by
  have hset := jankoSetting_of_G hf5 ht2 hft hD hDf hDt hDdisj htD hCt hE hE8 hE2 htE hr hrE
    hr₁ hr₁E hr3 hr₁3 htrans
  rw [JankoFive.card_inf_centralizer (centralizer ({f} : Set G)) hr']
  exact hset.five_dvd_centralizer_three (r' := ⟨r', hr'⟩)
    (by rw [← Subgroup.orderOf_coe]; exact hr'3)

end CFSG.EvenSporadicStandard.RuStd.S2

module

public import CFSG.LocalAnalysis.ComponentClassification.GS82PCSporOrd

public section

namespace CFSG.ComponentClassification.GS82PumpInputs.PCSpor

open CFSG Subgroup CFSG.Blueprint CFSG.ComponentClassification.CatLeaf HarrisLit.T1.SporRow

theorem sporOrder_eq_sporOrd' (s : TauCeti.SporadicName) :
    GSThmB.QPUSpor.sporOrder s = AGLEmbedding.sporOrd s := by
  cases s <;> norm_num [GSThmB.QPUSpor.sporOrder, GSThmB.QPUSpor.sporFactors,
    AGLEmbedding.sporOrd]

theorem not_cTypeOrder_sporOrd (s : TauCeti.SporadicName) :
    ¬ CTypeOrder (AGLEmbedding.sporOrd s) := by
  rintro (hO | ⟨n, -, hn⟩ | h)
  · rw [← sporOrder_eq_sporOrd'] at hO
    exact not_oddLieOrder_sporOrder s hO
  · cases s <;> exact factorial_div_two_ne (N := 45) (by decide) (by decide) n hn.symm
  · cases s <;> simp [AGLEmbedding.sporOrd] at h


theorem false_of_top (hcard : ∀ s, Nat.card (NativeSporadic.Carrier s) = AGLEmbedding.sporOrd s)
    {Y : Type} [Group Y] [Finite Y] {β : MulAut Y} {T : Subgroup Y} (h : Setting Y β T)
    (hT : T = ⊤) {s : TauCeti.SporadicName} (e : Y ⧸ center Y ≃* NativeSporadic.Carrier s) :
    False := by
  subst hT
  have hc := cTypeOrder_of_typC h.typC
  have : Nontrivial Y := LocalCores.isQuasisimple_nontrivial h.quasisimple
  have hZ : Open.fusionZStar Y = center Y :=
    fusionZStar_eq_center_of_quasisimple h.quasisimple (by rw [h.oddCore]; exact bot_ne_top)
  obtain ⟨e₁⟩ := GrSLit.nonempty_fusionZStar_equiv_of_mulEquiv'
    (Subgroup.topEquiv : (⊤ : Subgroup Y) ≃* Y)
  have hcY : Nat.card ((⊤ : Subgroup Y) ⧸ Open.fusionZStar (⊤ : Subgroup Y)) =
      AGLEmbedding.sporOrd s := by
    rw [Nat.card_congr e₁.toEquiv, Nat.card_congr (QuotientGroup.quotientMulEquivOfEq hZ).toEquiv,
      Nat.card_congr e.toEquiv, hcard s]
  rw [hcY] at hc
  exact not_cTypeOrder_sporOrd s hc

end CFSG.ComponentClassification.GS82PumpInputs.PCSpor

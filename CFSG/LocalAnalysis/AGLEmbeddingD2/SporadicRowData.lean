module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.SporadicTable

public section

namespace CFSG.AGLEmbeddingD2

open CFSG.Open CFSG.Blueprint CFSG.ComponentClassification.OuterAutomorphisms

theorem d2IndexDatum_carrier {s : TauCeti.SporadicName} [Finite (NativeSporadic.Carrier s)]
    {p : ℕ} (hp : p.Prime)
    (h : D2IndexDatum (NativeSporadic.Carrier s) p) :
    ∀ (L : Type) [Group L] [Finite L], Nonempty (L ≃* NativeSporadic.Carrier s) →
      D2IndexDatum L p := by
  intro L _ _ ⟨e⟩
  exact D2IndexDatum.of_mulEquiv hp e h

section Rows


theorem not_dvd_card_outer_carrier {s : TauCeti.SporadicName} [Finite (NativeSporadic.Carrier s)]
    (hs : s ≠ .M) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) :
    ¬ p ∣ Nat.card (Outer (NativeSporadic.Carrier s)) := by
  intro hdvd
  have : Finite (MulAut (NativeSporadic.Carrier s)) := MulEquiv.finite_left
  have h1 := Nat.le_of_dvd Nat.card_pos hdvd
  have h2 := card_outer_carrier_le_two_of_ne_M s hs
  have h3 := hp.two_le
  omega

theorem d2IndexDatum_carrier_of_pRank {s : TauCeti.SporadicName}
    [Finite (NativeSporadic.Carrier s)] (hs : s ≠ .M) {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2)
    (h : 3 ≤ Open.pRank p (⊤ : Subgroup (NativeSporadic.Carrier s))) :
    ∀ (L : Type) [Group L] [Finite L], Nonempty (L ≃* NativeSporadic.Carrier s) →
      D2IndexDatum L p :=
  d2IndexDatum_carrier hp ⟨not_dvd_card_outer_carrier hs hp hp2, Or.inr (Or.inl h)⟩

theorem d2IndexDatum_carrier_of_core {s : TauCeti.SporadicName}
    [Finite (NativeSporadic.Carrier s)] (hs : s ≠ .M) {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2)
    (h : ∀ S : Sylow p (NativeSporadic.Carrier s),
      GLBCore p 2 (S : Subgroup (NativeSporadic.Carrier s)) = ⊤) :
    ∀ (L : Type) [Group L] [Finite L], Nonempty (L ≃* NativeSporadic.Carrier s) →
      D2IndexDatum L p :=
  d2IndexDatum_carrier hp ⟨not_dvd_card_outer_carrier hs hp hp2, Or.inr (Or.inr (Or.inr h))⟩

theorem d2IndexDatumPlus_carrier_of_coreSup {s : TauCeti.SporadicName}
    [Finite (NativeSporadic.Carrier s)] (hs : s ≠ .M) {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2)
    (h : ∀ S : Sylow p (NativeSporadic.Carrier s), ∀ A : Subgroup (NativeSporadic.Carrier s),
      A ≤ (S : Subgroup (NativeSporadic.Carrier s)) → IsElemAbelian p A → Nat.card A = p ^ 2 →
        GLBCore p 2 (S : Subgroup (NativeSporadic.Carrier s)) ⊔ GLBCore p 1 A = ⊤) :
    ∀ (L : Type) [Group L] [Finite L], Nonempty (L ≃* NativeSporadic.Carrier s) →
      D2IndexDatumPlus L p := by
  intro L _ _ ⟨e⟩
  exact Or.inr (D2IndexDatumSup.of_mulEquiv hp e ⟨not_dvd_card_outer_carrier hs hp hp2, h⟩)

end Rows

end CFSG.AGLEmbeddingD2

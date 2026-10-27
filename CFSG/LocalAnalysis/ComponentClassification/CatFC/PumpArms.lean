module

public import CFSG.LocalAnalysis.ComponentClassification.CatFC.FixedComponent
public import CFSG.LocalAnalysis.ComponentClassification.CatFC.RuFi23
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.Zassenhaus.OuterPumpTChainTable

public section

namespace CFSG.ComponentClassification.CatFC

open Subgroup CFSG CFSG.Blueprint CFSG.Blueprint.NativeSporadic CFSG.Assembly.LowTwoRank
open CFSG.ComponentClassification.CatLeaf
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.ComponentClassification.GSThmB.QPUSpor (sporOrder)
open CFSG.EvenSporadicStandard.HSStd.Zassenhaus.Outer (not_alt_of_card)

@[expose] def SporadicCompOrder : Prop :=
  ∀ {S : Type} [Group S] [Finite S], IsSimpleGroup S → (∃ a b : S, a * b ≠ b * a) →
    ∀ {s : TauCeti.SporadicName}, (S ≃* Carrier s) → ∀ {σ : MulAut S}, orderOf σ = 2 →
      ∀ {D : Subgroup ↥(fixedSubgroup σ)}, IsComponent D →
        Nat.card (↥D ⧸ center ↥D) ∣ AGLEmbedding.sporOrd s ∧
        (σ ∈ (MulAut.conj : S →* MulAut S).range →
          SporadicInnerRow s (Nat.card (↥D ⧸ center ↥D))) ∧
        (σ ∉ (MulAut.conj : S →* MulAut S).range →
          SporadicOuterRow s (Nat.card (↥D ⧸ center ↥D)))

structure ArmInputs : Prop where
  gls : GLS3OddLieAutComponentsInput
  evenInner : ∀ (T : Type) [Group T], EvenLieType T → ∀ u : T, orderOf u = 2 →
    ∀ B : Subgroup ↥(centralizer ({u} : Set T)), ¬ IsComponent B
  evenOuter : EvenLieOuterTwoComponentsInput
  order : LieOrderFormulasInput
  card : ∀ s : TauCeti.SporadicName, s ≠ .M → Nat.card (Carrier s) = sporOrder s
  table : SporadicCompOrder

variable {S : Type} [Group S] [Finite S]

theorem false_of_sporadic_quotient (I : ArmInputs) [IsSimpleGroup S]
    (hna : ∃ a b : S, a * b ≠ b * a) (hcat : Catalog S) {σ : MulAut S} (hσ : orderOf σ = 2)
    {D : Subgroup ↥(fixedSubgroup σ)} (hD : IsComponent D) {s : TauCeti.SporadicName}
    (hsM : s ≠ .M) (hs : IsSporadic (↥D ⧸ center ↥D) s)
    (halt : ∀ k : ℕ, 5 ≤ k → ¬ Nonempty (↥D ⧸ center ↥D ≃* alternatingGroup (Fin k)))
    (hne2 : ∀ {X : Type} [Group X] {t : StatedLieTag} {n f : ℕ},
      StatedLieAdmissible t n 2 f → LieModel X t n 2 f → Nat.card X ≠ sporOrder s)
    (hrows : ∀ s' : TauCeti.SporadicName, sporOrder s ∣ AGLEmbedding.sporOrd s' →
      ¬ SporadicInnerRow s' (sporOrder s) ∧ ¬ SporadicOuterRow s' (sporOrder s)) : False := by
  obtain ⟨g⟩ := hs
  have hc : Nat.card (↥D ⧸ center ↥D) = sporOrder s := by
    rw [Nat.card_congr g.toEquiv, I.card s hsM]
  rcases catalog_fixed_component I.gls I.evenInner I.evenOuter hna hcat hσ hD with
    ⟨n, k, -, hk5, -, -, -, hDk⟩ | ⟨hodd, -⟩ | ⟨heven, -⟩ | ⟨s', ⟨es⟩⟩
  · exact halt k hk5 hDk
  · exact false_of_oddLie_fixedComponent I.gls I.order hodd hσ hD hc
  · exact false_of_evenLie_fixedComponent I.evenInner I.evenOuter I.order hna heven hσ hD hc hne2
  · obtain ⟨hdvd, hin, hout⟩ := I.table ‹IsSimpleGroup S› hna es hσ hD
    rw [hc] at hdvd hin hout
    by_cases hinn : σ ∈ (MulAut.conj : S →* MulAut S).range
    · exact (hrows s' hdvd).1 (hin hinn)
    · exact (hrows s' hdvd).2 (hout hinn)

theorem rows_none_mcl (s' : TauCeti.SporadicName) (h : sporOrder .McL ∣ AGLEmbedding.sporOrd s') :
    ¬ SporadicInnerRow s' (sporOrder .McL) ∧ ¬ SporadicOuterRow s' (sporOrder .McL) := by
  rw [sporOrder_eq_sporOrd] at h ⊢
  cases s' <;> first
    | exact absurd h (by simp only [AGLEmbedding.sporOrd]; decide)
    | (simp only [SporadicInnerRow, SporadicOuterRow, AGLEmbedding.sporOrd]; decide)

theorem rows_none_hn (s' : TauCeti.SporadicName) (h : sporOrder .HN ∣ AGLEmbedding.sporOrd s') :
    ¬ SporadicInnerRow s' (sporOrder .HN) ∧ ¬ SporadicOuterRow s' (sporOrder .HN) := by
  rw [sporOrder_eq_sporOrd] at h ⊢
  cases s' <;> first
    | exact absurd h (by simp only [AGLEmbedding.sporOrd]; decide)
    | (simp only [SporadicInnerRow, SporadicOuterRow, AGLEmbedding.sporOrd]; decide)

theorem not_alt_of_sporOrder {X : Type} [Group X] {s : TauCeti.SporadicName} {a n : ℕ}
    (hn : 2 ≤ n) (hc : Nat.card X = sporOrder s)
    (h1 : a.factorial < 2 * AGLEmbedding.sporOrd s)
    (h2 : 2 * AGLEmbedding.sporOrd s < (a + 1).factorial) :
    ¬ Nonempty (X ≃* alternatingGroup (Fin n)) :=
  not_alt_of_card hn (hc.trans (sporOrder_eq_sporOrd s)) h1 h2

theorem clause4_of_inputs (I : ArmInputs) [IsSimpleGroup S] (hna : ∃ a b : S, a * b ≠ b * a)
    (hcat : Catalog S) {σ : MulAut S} (hσ : orderOf σ = 2) {D : Subgroup ↥(fixedSubgroup σ)}
    (hD : IsComponent D) :
    ¬ IsSporadic (↥D ⧸ center ↥D) .McL ∧ ¬ IsSporadic (↥D ⧸ center ↥D) .HN := by
  refine ⟨fun hs => ?_, fun hs => ?_⟩
  · obtain ⟨g⟩ := hs
    have hc : Nat.card (↥D ⧸ center ↥D) = sporOrder .McL := by
      rw [Nat.card_congr g.toEquiv, I.card .McL (by decide)]
    refine false_of_sporadic_quotient I hna hcat hσ hD (by decide) ⟨g⟩
      (fun k hk h => not_alt_of_sporOrder (a := 12) (by omega) hc
        (by simp only [AGLEmbedding.sporOrd]; norm_num [Nat.factorial])
        (by simp only [AGLEmbedding.sporOrd]; norm_num [Nat.factorial]) h) ?_ rows_none_mcl
    intro X _ t n f hadm hX
    rw [sporOrder_eq_sporOrd]
    exact lieModel_two_card_ne_mcl I.order hadm hX
  · obtain ⟨g⟩ := hs
    have hc : Nat.card (↥D ⧸ center ↥D) = sporOrder .HN := by
      rw [Nat.card_congr g.toEquiv, I.card .HN (by decide)]
    refine false_of_sporadic_quotient I hna hcat hσ hD (by decide) ⟨g⟩
      (fun k hk h => not_alt_of_sporOrder (a := 17) (by omega) hc
        (by simp only [AGLEmbedding.sporOrd]; norm_num [Nat.factorial])
        (by simp only [AGLEmbedding.sporOrd]; norm_num [Nat.factorial]) h) ?_ rows_none_hn
    intro X _ t n f hadm hX
    rw [sporOrder_eq_sporOrd]
    exact lieModel_two_card_ne_hn I.order hadm hX

end CFSG.ComponentClassification.CatFC

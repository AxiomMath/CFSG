module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanIdentDefs

public section

namespace CFSG.AGLEmbedding

open CFSG.Open

@[expose] def P1ThreeLieCharP : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (Y : Type) [Group Y] [Finite Y] (Rb : Sylow p Y) (Y₀ : Subgroup Y),
    ReducedNongeneration p Y Rb Y₀ → CatalogSimpleSections Y →
    ∀ K : Subgroup Y, IsComponentOf K ⊤ → (∀ L : Subgroup Y, IsComponentOf L ⊤ → L = K) →
      ¬ IsCyclic ((Rb : Subgroup Y) ⊓ K : Subgroup Y) →
      (∀ c ∈ (Rb : Subgroup Y) ⊓ Subgroup.centralizer (K : Set Y), orderOf c = p →
        c ∈ (Subgroup.center K).map K.subtype) →
      ∀ d : TauCeti.ValidLieTypeIndex,
        Nonempty (K ⧸ Subgroup.center K ≃* (TauCeti.CFSGIndex.lie d).Group) →
        p = d.1.characteristic → P1ThreeLieList p d

@[expose] def P1ThreeLieOffChar : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (Y : Type) [Group Y] [Finite Y] (Rb : Sylow p Y) (Y₀ : Subgroup Y),
    ReducedNongeneration p Y Rb Y₀ → CatalogSimpleSections Y →
    ∀ K : Subgroup Y, IsComponentOf K ⊤ → (∀ L : Subgroup Y, IsComponentOf L ⊤ → L = K) →
      ¬ IsCyclic ((Rb : Subgroup Y) ⊓ K : Subgroup Y) →
      (∀ c ∈ (Rb : Subgroup Y) ⊓ Subgroup.centralizer (K : Set Y), orderOf c = p →
        c ∈ (Subgroup.center K).map K.subtype) →
      ∀ d : TauCeti.ValidLieTypeIndex,
        Nonempty (K ⧸ Subgroup.center K ≃* (TauCeti.CFSGIndex.lie d).Group) →
        p ≠ d.1.characteristic → P1ThreeLieList p d

theorem kFactP1ThreeLie_of_families (hc : P1ThreeLieCharP) (ho : P1ThreeLieOffChar) :
    KFactP1ThreeLie := by
  intro p _ Y _ _ Rb Y₀ h hcat K hK huniq hnc hcent d he
  by_cases hchar : p = d.1.characteristic
  · exact hc p Y Rb Y₀ h hcat K hK huniq hnc hcent d he hchar
  · exact ho p Y Rb Y₀ h hcat K hK huniq hnc hcent d he hchar

@[expose] def WeakCharPGenAt (Fam : TauCeti.ValidLieTypeIndex → Prop) : Prop :=
  ∀ (K : Type) [Group K] [Finite K], IsSimpleGroup K → (∃ a b : K, a * b ≠ b * a) →
    ∀ d : TauCeti.ValidLieTypeIndex, Fam d → Nonempty (K ≃* CatGroup d) →
      ∀ p : ℕ, p.Prime → p ≠ 2 → p = d.1.characteristic → ¬ IsRankOneLieIndex d.1 →
        ∀ T : Sylow p K, GLBWeakCore p (T : Subgroup K) = ⊤

theorem weakCharPGenAt_or {F₁ F₂ : TauCeti.ValidLieTypeIndex → Prop}
    (h₁ : WeakCharPGenAt F₁) (h₂ : WeakCharPGenAt F₂) :
    WeakCharPGenAt fun d => F₁ d ∨ F₂ d :=
  fun K _ _ hs hn d hd => hd.elim (h₁ K hs hn d) (h₂ K hs hn d)

end CFSG.AGLEmbedding

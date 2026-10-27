module

public import CFSG.HardMathSupport.Dickson.Sec6.UpD42Aux.Defs

public section

namespace CFSG.HardMathSupport.Dickson.Sec6

open CFSG.Open CFSG.HardMathSupport.Solomon.Coordinator

@[expose] def UpD42Chev2Inn (F : TauCeti.LieTypeIndex → Prop) : Prop :=
  ∀ (S : Type) [Group S] [Finite S], IsSimpleGroup S → (∃ a b : S, a * b ≠ b * a) →
    ∀ d : TauCeti.ValidLieTypeIndex, F d.1 → IsCharTwoLieIndex d.1 →
      Nonempty (S ≃* (TauCeti.CFSGIndex.lie d).Group) →
      ∀ x : S, UpD42Pumpup S (MulAut.conj x) →
        IsCatalogLieIso S IsOmegaTwoBigIndex ∨ IsCatalogLieIso S IsTwE62Index ∨
          IsCatalogLieIso S IsD48Index

@[expose] def UpD42Chev2Out (F : TauCeti.LieTypeIndex → Prop) : Prop :=
  ∀ (S : Type) [Group S] [Finite S], IsSimpleGroup S → (∃ a b : S, a * b ≠ b * a) →
    ∀ d : TauCeti.ValidLieTypeIndex, F d.1 → IsCharTwoLieIndex d.1 →
      Nonempty (S ≃* (TauCeti.CFSGIndex.lie d).Group) →
      ∀ α : MulAut S, α ∉ (MulAut.conj : S →* MulAut S).range → UpD42Pumpup S α →
        IsCatalogLieIso S IsOmegaTwoBigIndex ∨ IsCatalogLieIso S IsTwE62Index ∨
          IsCatalogLieIso S IsD48Index

theorem UpD42Chev2Inn.mono {F F' : TauCeti.LieTypeIndex → Prop} (hle : ∀ d, F' d → F d)
    (h : UpD42Chev2Inn F) : UpD42Chev2Inn F' :=
  fun S _ _ hs hnab d hd hc he x hx => h S hs hnab d (hle _ hd) hc he x hx

theorem UpD42Chev2Inn.union {F F' : TauCeti.LieTypeIndex → Prop} (h : UpD42Chev2Inn F)
    (h' : UpD42Chev2Inn F') : UpD42Chev2Inn fun d => F d ∨ F' d := by
  intro S _ _ hs hnab d hd hc he x hx
  rcases hd with hd | hd
  · exact h S hs hnab d hd hc he x hx
  · exact h' S hs hnab d hd hc he x hx

theorem UpD42Chev2Out.mono {F F' : TauCeti.LieTypeIndex → Prop} (hle : ∀ d, F' d → F d)
    (h : UpD42Chev2Out F) : UpD42Chev2Out F' :=
  fun S _ _ hs hnab d hd hc he α hα hp => h S hs hnab d (hle _ hd) hc he α hα hp

theorem UpD42Chev2Out.union {F F' : TauCeti.LieTypeIndex → Prop} (h : UpD42Chev2Out F)
    (h' : UpD42Chev2Out F') : UpD42Chev2Out fun d => F d ∨ F' d := by
  intro S _ _ hs hnab d hd hc he α hα hp
  rcases hd with hd | hd
  · exact h S hs hnab d hd hc he α hα hp
  · exact h' S hs hnab d hd hc he α hα hp

theorem upD42Chev2Leaf_of_inn_out (hI : UpD42Chev2Inn fun _ => True)
    (hO : UpD42Chev2Out fun _ => True) : UpD42Chev2Leaf := by
  intro S _ _ hs hnab ⟨d, hc, he⟩ α hα
  by_cases hin : α ∈ (MulAut.conj : S →* MulAut S).range
  · obtain ⟨x, rfl⟩ := hin
    exact hI S hs hnab d trivial hc he x hα
  · exact hO S hs hnab d trivial hc he α hin hα

end CFSG.HardMathSupport.Dickson.Sec6

end

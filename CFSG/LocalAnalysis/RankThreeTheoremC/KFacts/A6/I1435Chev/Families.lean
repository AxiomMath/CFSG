module

public import CFSG.LocalAnalysis.RankThreeTheoremC.KFacts.A6.I1435Chev.Setup
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFacts.A6.I1435.Holds

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LocalAnalysis.RankThreeTheoremC.A6.I1435Chev

open Subgroup CFSG.Open CFSG.GH74.Exceptional
open CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData (IsChevTwo IsChevIndexTwo)
open CFSG.LocalAnalysis.RankThreeTheoremC.A6.I1435

@[expose] def FamilyAt (d : TauCeti.LieTypeIndex) : Prop :=
  ∀ (hv : d.Valid) (K : Type) [Group K] [Finite K], IsSimpleGroup K →
    Nonempty (K ≃* TauCeti.ValidLieTypeIndex.Group ⟨d, hv⟩) → AutShape K →
      (3 ∣ Nat.card K → Shape K) → Nonempty (K ≃* PSp43)

@[expose] def ChevIndex (d : TauCeti.LieTypeIndex) : Prop :=
  IsChevIndexTwo d ∨ (∃ q : TauCeti.PrimePower, q.card = 7 ∧ d = .A 1 q) ∨
    (∃ q : TauCeti.PrimePower, q.card = 3 ∧ d = .twistedA 2 q)

theorem FamilyAt.of_not_shape {d : TauCeti.LieTypeIndex}
    (h : ∀ (hv : d.Valid) (K : Type) [Group K] [Finite K], IsSimpleGroup K →
      Nonempty (K ≃* TauCeti.ValidLieTypeIndex.Group ⟨d, hv⟩) →
        3 ∣ Nat.card K ∧ ¬ Shape K) : FamilyAt d := by
  intro hv K _ _ hs he _ hSh
  obtain ⟨h3, hn⟩ := h hv K hs he
  exact absurd (hSh h3) hn

theorem kFact1435ChevTwo_of_families (h : ∀ d, ChevIndex d → FamilyAt d) :
    KFact1435ChevTwo := by
  intro X _ _ K P x hKn hKs hnab hCK hchev hnalt hPW hxJ hx1 hlines hd1 hd2 hsolv
  obtain ⟨e⟩ := hPW
  have e' : ↥(P : Subgroup X) ≃* W3 := e
  have hAut : AutShape ↥K := autShape_of_hyp hKn hCK e'
  have hSh : 3 ∣ Nat.card ↥K → Shape ↥K := fun h3 =>
    shape_of_hyp e' (thompson_le_of_three_dvd hKn e' hd1 h3) hxJ hx1 hlines hsolv
  rcases hchev with ⟨⟨d, hv⟩, hd, he⟩ | ⟨n, -, he⟩ | ⟨⟨d, hv⟩, hd, he⟩
  · exact h d (Or.inl hd) hv ↥K hKs he hAut hSh
  · exact absurd ⟨n, he⟩ hnalt
  · exact h d (Or.inr hd) hv ↥K hKs he hAut hSh

end CFSG.LocalAnalysis.RankThreeTheoremC.A6.I1435Chev

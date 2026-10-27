module

public import CFSG.LocalAnalysis.AGLEmbedding.OneLieMSideDefsAux
public import CFSG.LocalAnalysis.AGLEmbedding.CaseTwoReeFacts

public section

namespace CFSG.AGLEmbedding

theorem kFactCaseTwoReeId_of_ident (hId : KFactOneLieIdent)
    (hL2 : ∀ (d : TauCeti.ValidLieTypeIndex) (n : ℕ), 3 ≤ n → IsLinTwoIndex 3 n d →
      ∀ (A : Subgroup (CatGroup d)) (L : Type) [Group L], IsCaseTwoGroup 3 L →
        ∀ f : A →* L, ¬ Function.Surjective f)
    (hU3 : ∀ d : TauCeti.ValidLieTypeIndex, IsUnitaryIndex 3 d → 2 ≤ d.1.fieldExponent →
      ∀ (A : Subgroup (CatGroup d)) (L : Type) [Group L], IsCaseTwoGroup 3 L →
        ∀ f : A →* L, ¬ Function.Surjective f) :
    KFactCaseTwoReeId := by
  intro K _ _ hs hnonab hcat T hT hcore hrank A L _ hL f hf
  obtain ⟨d, hd, ⟨e⟩⟩ := hId K hs hnonab hcat 3 Nat.prime_three (by decide) T hT hcore
    (by omega)
  set A' : Subgroup (CatGroup d) := A.map e.toMonoidHom with hA'
  set f' : A' →* L := f.comp (A.equivMapOfInjective e.toMonoidHom e.injective).symm.toMonoidHom
    with hf'
  have hsurj : Function.Surjective f' :=
    hf.comp (A.equivMapOfInjective e.toMonoidHom e.injective).symm.surjective
  rcases hd with ⟨n, hn, hd⟩ | ⟨hd, h2⟩ | hd
  · exact (hL2 d n hn hd A' L hL f' hsurj).elim
  · exact (hU3 d hd h2 A' L hL f' hsurj).elim
  · exact ⟨d, hd, ⟨e⟩⟩

end CFSG.AGLEmbedding

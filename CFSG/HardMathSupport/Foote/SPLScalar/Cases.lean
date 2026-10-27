module

public import CFSG.HardMathSupport.Foote.SPLScalar.CasesCore
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.Unitary
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.Ree

public section

namespace CFSG.HardMathSupport.Foote.SPLScalar

open CFSG.AGLEmbedding CFSG.Open

theorem false_of_ree
    {KC : Type} [Group KC] [Finite KC] {d : TauCeti.ValidLieTypeIndex}
    (hd : IsReeGTwoIndex 3 d) (he : Nonempty (KC ≃* CatGroup d)) {W : Subgroup KC}
    {L : Type} [Group L] [Finite L] (hL : IsAltTwoP 3 L ∨ IsSmallUnitary 3 L)
    (f : ↥W →* L) (hf : Function.Surjective f) : False := by
  obtain ⟨e⟩ := he
  exact Core.false_of_ree kFactReeOrder kFactUnitaryOrder hd e hL f hf

theorem false_of_lin_unitaryThree {KC : Type} [Group KC] [Finite KC] {n : ℕ}
    {d : TauCeti.ValidLieTypeIndex} (hn : 1 ≤ n) (hd : IsLinTwoIndex 3 n d)
    (he : Nonempty (KC ≃* CatGroup d)) {L : Type} [Group L] [Finite L]
    (hL : IsSmallUnitary 3 L) (TL : Sylow 3 L) (T' : Sylow 3 KC) {E : Subgroup KC}
    (hET : E ≤ T') (hE : Nonempty (↥E ≃* ↥(TL : Subgroup L))) : False := by
  obtain ⟨e⟩ := he
  obtain ⟨φ⟩ := hE
  exact Core.false_of_lin_unitaryThree kFactUnitarySylowStructure hn hd e hL TL T' hET φ

theorem even_of_lin_altSix {KC : Type} [Group KC] [Finite KC] {n : ℕ}
    {d : TauCeti.ValidLieTypeIndex} (hn : 1 ≤ n) (hd : IsLinTwoIndex 3 n d)
    (he : Nonempty (KC ≃* CatGroup d)) {W : Subgroup KC} {L : Type} [Group L] [Finite L]
    (hL : IsAltTwoP 3 L) (f : ↥W →* L) (hf : Function.Surjective f) : Even n := by
  obtain ⟨e⟩ := he
  exact Core.even_of_lin_altSix hd e hL f hf

theorem even_of_unitary_altSix {KC : Type} [Group KC] [Finite KC]
    {d : TauCeti.ValidLieTypeIndex} (hd : IsUnitaryIndex 3 d)
    (he : Nonempty (KC ≃* CatGroup d)) {W : Subgroup KC} {L : Type} [Group L] [Finite L]
    (hL : IsAltTwoP 3 L) (f : ↥W →* L) (hf : Function.Surjective f) :
    Even d.1.fieldExponent := by
  obtain ⟨e⟩ := he
  exact Core.unitary_alt_case kFactUnitaryOrder hd e hL f hf

theorem center_le_of_unitary_unitaryThree {KC : Type} [Group KC] [Finite KC]
    {d : TauCeti.ValidLieTypeIndex} (hd : IsUnitaryIndex 3 d)
    (he : Nonempty (KC ≃* CatGroup d)) {L : Type} [Group L] [Finite L]
    (hL : IsSmallUnitary 3 L) (TL : Sylow 3 L) (T' : Sylow 3 KC) {E : Subgroup KC}
    (hET : E ≤ T') (hE : Nonempty (↥E ≃* ↥(TL : Subgroup L))) :
    E ⊓ Subgroup.centralizer (E : Set KC) ≤
      (T' : Subgroup KC) ⊓ Subgroup.centralizer ((T' : Subgroup KC) : Set KC) := by
  obtain ⟨e⟩ := he
  obtain ⟨φ⟩ := hE
  exact Core.center_le_of_unitary_unitaryThree kFactUnitarySylowStructure hd e hL TL T' hET φ

end CFSG.HardMathSupport.Foote.SPLScalar

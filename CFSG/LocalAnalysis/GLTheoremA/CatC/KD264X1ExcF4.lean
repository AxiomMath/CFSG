module

public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieRowX1Parts

public section

namespace CFSG.LocalAnalysis.GLTheoremA.KD264Lie

@[expose] def KD264X1ExcF4 : Prop :=
  ∀ (d : TauCeti.ValidLieTypeIndex) (q : TauCeti.PrimePower), d.1 = .F4 q →
    ∀ [Finite (TauCeti.CFSGIndex.lie d).Group], KD264X1At d

@[expose] def KD264X1ExcE678 : Prop :=
  ∀ (d : TauCeti.ValidLieTypeIndex) (q : TauCeti.PrimePower),
    (d.1 = .E6 q ∨ d.1 = .E7 q ∨ d.1 = .E8 q) →
    ∀ [Finite (TauCeti.CFSGIndex.lie d).Group], KD264X1At d

theorem kd264X1ExcPart_of_f4_e678 (hF4 : KD264X1ExcF4) (hE : KD264X1ExcE678) :
    KD264X1ExcPart := by
  intro d q hd _
  rcases hd with h | h | h | h
  · exact hE d q (Or.inl h)
  · exact hE d q (Or.inr (Or.inl h))
  · exact hE d q (Or.inr (Or.inr h))
  · exact hF4 d q h

end CFSG.LocalAnalysis.GLTheoremA.KD264Lie

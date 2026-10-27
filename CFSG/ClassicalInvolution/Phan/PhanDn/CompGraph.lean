module

public import CFSG.ClassicalInvolution.Phan.PhanDn.FlagGeom
public import CFSG.ClassicalInvolution.Phan.PhanDn.PointGraph

public section

namespace CFSG.ClassicalInvolution.PhanDn

variable {K : Type} [Field K] {σ : K ≃+* K}

variable (σ) in
@[expose] def CompVert : Type :=
  {U : FlagVert σ 3 // Module.finrank K U.1 ≠ 2}

variable (σ) in
@[expose] def compGraph : SimpleGraph (CompVert σ) where
  Adj U W := (flagGraph σ 3).Adj U.1 W.1 ∨
    (IsFlipflopPt σ U.1.1 ∧ IsFlipflopPt σ W.1.1 ∧ FlipColl σ U.1.1 W.1.1)
  symm := ⟨fun U W h => by
    rcases h with h | ⟨hU, hW, hne, h⟩
    · exact Or.inl h.symm
    · exact Or.inr ⟨hW, hU, Ne.symm hne, by rwa [sup_comm]⟩⟩
  loopless := ⟨fun U h => by
    rcases h with h | ⟨-, -, hne, -⟩
    · exact (flagGraph σ 3).loopless.irrefl _ h
    · exact hne rfl⟩

theorem compGraph_adj {U W : CompVert σ} :
    (compGraph σ).Adj U W ↔ (flagGraph σ 3).Adj U.1 W.1 ∨
      (IsFlipflopPt σ U.1.1 ∧ IsFlipflopPt σ W.1.1 ∧ FlipColl σ U.1.1 W.1.1) :=
  Iff.rfl

end CFSG.ClassicalInvolution.PhanDn

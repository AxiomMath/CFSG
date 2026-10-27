module

public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneBInputs
public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneUModel

public noncomputable section

namespace CFSG.ComponentClassification.Burgoyne

open CFSG Subgroup CFSG.Blueprint CFSG.ComponentClassification.TBLit CFSG.Assembly.LowTwoRank
open CFSG.ComponentClassification.UnbalancingLocal CFSG.LocalAnalysis.ComponentInitial
open scoped MatrixGroups

@[expose] def BurgoynePropBSU4CoverInput : Prop :=
  ∀ (p f : ℕ) (F : Type) [Field F], UnitaryFieldData p f F → p ≠ 2 →
    ∀ (L : Type) [Group L] [Finite L] (α : StatedSU 4 (p ^ f) F →* L), Function.Surjective α →
      ∀ c : L, PropBHypII L c →
        ∀ g : StatedSU 4 (p ^ f) F, ((g : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) = -1 →
          c = α g

@[expose] def BurgoynePropBSU4ExcInput : Prop :=
  ∀ (J : Type) [Group J] [Finite J] (K : Subgroup J) [K.Normal] (t : J) (Y : Subgroup J)
    (c : K ⧸ pPrimeCore 2 K), PropBHyp J K t Y c →
    ∀ (p f : ℕ) (F : Type) [Field F] (h : UnitaryFieldData p f F), p ≠ 2 →
    ∀ θ : GeneralizedFitting.subgroup (conjQuotAction K (centralPreimage (pPrimeCore 2 K))).range
      ≃* StatedProj (StatedSU 4 (p ^ f) F),
    ∀ A : U.uU h 4,
      socleAction θ ((conjQuotAction K (centralPreimage (pPrimeCore 2 K))).rangeRestrict t) =
        U.uConjAut h (by norm_num) A →
    ∀ (H : U.uU h 4) (J₀ : Finset (Fin 4)) (l : F), l ≠ 0 → Odd J₀.card →
      (((H : GL (Fin 4) F)⁻¹ : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) *
        ((A : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) *
        ((H : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) = l • PSL.signMat F J₀ → False

end CFSG.ComponentClassification.Burgoyne

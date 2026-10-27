module

public import CFSG.GH74.QTGen4.Finite4
public import CFSG.Quasithin.H13.A6Inputs13_3
public import CFSG.Quasithin.H13.L32ANotation

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique
open scoped IsMulCommutative

@[expose] def Lemma14_5_8Sym_F4 : Prop :=
  ∀ (G : Type) [Group G] [CFSG.GH74.QTGen4.Finite4 G] (T L V V₂ Y K : Subgroup G), Hyp147 G T L V →
    A6.IsV2 T V V₂ → oTwoUpper Y = Y → Y ≤ A6.g1 T V → T ≤ Subgroup.normalizer (Y : Set G) →
    quasithinO2QuotientIso (Y ⊔ T) (Equiv.Perm (Fin 3)) →
    ¬ Y ≤ Subgroup.normalizer (L : Set G) →
    pCoreOf 2 (L₁Of L V₂ ⊔ Y ⊔ T) ≠ ⊥ →
    K ∈ cComp (L₁Of L V₂ ⊔ Y ⊔ T) → quasithinIsFaithfulLocal T K →
    L₁Of L V₂ ⊔ Y ⊔ T = K ⊔ T →
    quasithinO2QuotientIso K (Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)) →
    pCoreOf 2 K =
      K ⊓ Subgroup.centralizer (conjClosure (fsuV1 T V) (L₁Of L V₂ ⊔ Y ⊔ T) : Set G) →
    V₂ ≤ conjClosure (fsuV1 T V) (L₁Of L V₂ ⊔ Y ⊔ T) →
    conjClosure (fsuV1 T V) (L₁Of L V₂ ⊔ Y ⊔ T) = conjClosure V₂ Y →
    (∃ _ : IsMulCommutative ↥(conjClosure (fsuV1 T V) (L₁Of L V₂ ⊔ Y ⊔ T)),
      BinaryNaturalSL (V := ↥(conjClosure (fsuV1 T V) (L₁Of L V₂ ⊔ Y ⊔ T)))
        (autOn K (conjClosure (fsuV1 T V) (L₁Of L V₂ ⊔ Y ⊔ T))) ⊤ ⊥ 3 1) →
    False

end CFSG.Quasithin.H13

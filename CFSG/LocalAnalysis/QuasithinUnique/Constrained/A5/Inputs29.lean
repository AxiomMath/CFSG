module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.Statements
public import CFSG.LocalAnalysis.QuasithinUnique.GammaFamiliesExtraComponents
public import CFSG.Open.StatedDefs
public import Mathlib.LinearAlgebra.Matrix.ProjectiveSpecialLinearGroup
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.AppCCases
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.DoubleA3.L2_4_27

public section

namespace CFSG.QuasithinUnique.A5

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.QuasithinUnique.DoubleA3
open scoped MatrixGroups

@[expose] def K9Type (X : Type) [Group X] : Prop :=
  Nonempty (X ≃* alternatingGroup (Fin 6)) ∨ Nonempty (X ≃* PSL(2, ZMod 7)) ∨
    StatedClassicalModel X .PSL 2 17 1

@[expose] def Lemma2_4_29_9_K : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T M H S L : Subgroup G), A5Cfg G T M H S L →
    ∀ z u : G, A5Step7 T M H S L z u → oddCoreIn (centralizerElem u) = ⊥ →
      ∀ K : Subgroup G, IsComponentIn K (centralizerElem u) →
        z ∈ Subgroup.normalizer (K : Set G) → ⁅K, Subgroup.zpowers z⁆ = K → ¬ K ≤ M →
        ((¬ CentralQuotientAlt K 6 ∧ ¬ CentralQuotientAlt K 7) → Ch1.InducesInner z K) →
        IsListedComponent M (T ⊓ centralizerElem u) K z →
        K9Type ↥K ∧ u * z ∈ K

end CFSG.QuasithinUnique.A5

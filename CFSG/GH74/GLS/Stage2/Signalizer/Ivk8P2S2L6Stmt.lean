module

public import CFSG.GH74.GLS.Stage2.Final.Thm4.Defs18

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Ivk8.P2S2

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.Stage2.Local
  CFSG.GH74.GLS.Stage2.Final.Thm4 CFSG.GH74.GLS.Bg

@[expose] def Lemma17_6W : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (z : G) (k : Kind) (S M : Subgroup G), Fail17 G z k S M →
    M = Cen z → Em M ≠ ⊥ → pLayerOf 2 M = Em M → G2Three z S →
      O22Of (O2Of M) = pPrimeCoreOf 2 (O22Of (O2Of M)) ⊔ (S ⊓ O22Of (O2Of M)) ∧
      Nonempty (↥(S ⊓ O22Of (O2Of M)) ≃* QuaternionGroup 2) ∧
      S ⊓ O22Of (O2Of M) ⊓ centralizer (pPrimeCoreOf 2 (O22Of (O2Of M)) : Set G) = zpowers z

end CFSG.GH74.GLS.Stage2.Signalizer.Ivk8.P2S2

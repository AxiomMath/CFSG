module

public import CFSG.GH74.Generic.S1.RQ3
public import CFSG.GH74.Generic.S1.RQ3Sys
public import CFSG.GH74.Generic.S45.PumpC1

public section

namespace CFSG.GH74.Generic.S1

open CFSG CFSG.GH74 CFSG.GH74.L5U5 CFSG.Blueprint CFSG.Assembly.LowTwoRank Subgroup CFSG.GH74.Generic
  CFSG.ClassicalInvolution.WeakCT CFSG.ClassicalInvolution.Phan CFSG.LocalCores

@[expose] def S1LeafCompBarHigh : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (x : G) (K : Subgroup (CentralizerBar x)), S1Setup G x K →
    S1Front G x K → S1LargeModel K → ∀ (u : Fin 4 → G) (hu : ∀ i, u i ∈ centralizer ({x} : Set G)),
      S1Frame x K u hu → S1SymFrame x u →
        ∀ c ∈ symJ (symX x u) 3, orderOf c = 2 → (∀ a ∈ symJ (symX x u) 3, a * c = c * a) →
          (S45.barSub c (symJ (symX x u) 0 ⊔ symJ (symX x u) 1)).IsSubnormal

@[expose] def S1LeafCompBar3 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (x : G) (K : Subgroup (CentralizerBar x)), S1Setup G x K →
    S1Front G x K → ∀ (u : Fin 4 → G) (hu : ∀ i, u i ∈ centralizer ({x} : Set G)),
      S1Frame x K u hu → ∀ (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = 3 →
        S1SymFrameLin x u F → S1FrameOddFree x u →
          ∀ c ∈ symJ3 (symX x u) 3, orderOf c = 2 → (∀ a ∈ symJ3 (symX x u) 3, a * c = c * a) →
            (S45.barSub c (symJ3 (symX x u) 0 ⊔ symJ3 (symX x u) 1)).IsSubnormal

@[expose] def S1LeafCompBar : Prop := S1LeafCompBarHigh ∧ S1LeafCompBar3

end CFSG.GH74.Generic.S1

module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.CGT.PushingUpLit.Transport
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.Quasithin.Background.G11Defs
public import CFSG.RankThree.PartTwo.NotationBlocks

public section

namespace CFSG.CGT.Foote82

open CFSG.Open CFSG.Quasithin.G11 CFSG.RankThree.PartTwo Matrix

namespace L13Aux

@[expose] def H1Zero (X M : Type) [Group X] [AddCommGroup M] (act : X → M → M) : Prop :=
  ∀ F : X → M, (∀ x y : X, F (x * y) = F x + act x (F y)) → ∃ a : M, ∀ x : X, F x = act x a - a

end L13Aux

@[expose] def H1OmegaMinusSix : Prop :=
  L13Aux.H1Zero ↥(omegaMinusTwo 2) (Fin 2 ⊕ Fin 2 ⊕ Fin 2 → ZMod 2) fun g a =>
    ((g : GL (Fin 2 ⊕ Fin 2 ⊕ Fin 2) (ZMod 2)) :
      Matrix (Fin 2 ⊕ Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2 ⊕ Fin 2) (ZMod 2)) *ᵥ a

@[expose] def H1OmegaMinusEight : Prop :=
  L13Aux.H1Zero ↥(omegaMinusTwo 3) (Fin 3 ⊕ Fin 3 ⊕ Fin 2 → ZMod 2) fun g a =>
    ((g : GL (Fin 3 ⊕ Fin 3 ⊕ Fin 2) (ZMod 2)) :
      Matrix (Fin 3 ⊕ Fin 3 ⊕ Fin 2) (Fin 3 ⊕ Fin 3 ⊕ Fin 2) (ZMod 2)) *ᵥ a

@[expose] def H1AltSevenFour : Prop :=
  ∀ (N : Type) [AddCommGroup N] [Module (ZMod 2) N] [Finite N],
    Module.finrank (ZMod 2) N = 4 → ∀ Y : Subgroup (GLV N),
      (∃ α : ↥Y →* alternatingGroup (Fin 7), Function.Surjective α) →
        L13Aux.H1Zero ↥Y N fun y a => (y : GLV N) a

@[expose] def H1ThreeAltSix : Prop :=
  ∀ (N : Type) [AddCommGroup N] [Module (ZMod 2) N] [Finite N],
    Module.finrank (ZMod 2) N = 6 → ∀ Y : Subgroup (GLV N), ⁅Y, Y⁆ = Y → IsIrr Y ⊤ →
      (∃ α : ↥Y →* alternatingGroup (Fin 6), Function.Surjective α ∧
        α.ker ≤ Subgroup.center ↥Y) →
        L13Aux.H1Zero ↥Y N fun y a => (y : GLV N) a

end CFSG.CGT.Foote82

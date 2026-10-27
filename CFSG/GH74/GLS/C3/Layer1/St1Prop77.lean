module

public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.GH74.GLS.C3.Layer1.St1Defs
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge

public section

namespace CFSG.GH74.GLS

open Subgroup CFSG.ABGLocalTools

@[expose] def B_st1_lemma75 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (S : Subgroup G), IsSylowOf 2 S ⊤ →
    ∀ (x y : G) (K : Subgroup G), IsTerminallyUnbalancing x y K →
      ∃ g : G, IsTerminallyUnbalancing (g⁻¹ * x * g) (g⁻¹ * y * g) (CFSG.conjugate K g) ∧
        IsSylowOf 2 (S ⊓ centralizer ({g⁻¹ * x * g} : Set G)) (centralizer ({g⁻¹ * x * g} : Set G)) ∧
        g⁻¹ * y * g ∈ S

end CFSG.GH74.GLS

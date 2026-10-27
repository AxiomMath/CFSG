module

public import CFSG.GH74.GLS.C3.Layer1.P34Final
public import CFSG.GH74.GLS.C3.Layer1.P34PShape
public import CFSG.GH74.GLS.C3.Layer1.Defs

public section

namespace CFSG.GH74.GLS.C3.Layer1.P34

open Subgroup CFSG.ABGLocalTools

@[expose] def IsFAutL2A7 (K : Type) [Group K] (α : MulAut K) : Prop :=
  α ≠ 1 ∧
    ((∃ (F : Type) (_ : Field F) (_ : Finite F) (e : K ≃* IVK.L2 F),
        Odd (Nat.card F) ∧ α ∈ IVK.fieldAutSub e) ∨
      (Nonempty (K ≃* alternatingGroup (Fin 7)) ∧ α ∉ IVK.innAut K))

@[expose] def InducesFAutL2A7 {X : Type} [Group X] (f : X) (K : Subgroup X) : Prop :=
  ∃ hf : f ∈ normalizer (K : Set X),
    IsFAutL2A7 (kBar K) (inducedQuotAut K (pPrimeCore 2 ↥K) ⟨f, hf⟩)

structure Prop34Hyp (X : Type) [Group X] (x : X) (K : Subgroup X) : Prop where
  simple : IsSimpleGroup X
  nonab : ∃ a b : X, a * b ≠ b * a
  central : IsCentralInvolution x
  comp : IsPCompIn 2 (centralizer ({x} : Set X)) K
  unique : ∀ K' : Subgroup X, IsPCompIn 2 (centralizer ({x} : Set X)) K' → K' = K
  shape : HasL2Model (kBar K) Odd ∨ Nonempty (kBar K ≃* alternatingGroup (Fin 7))
  sylowQ : ∃ Q : Subgroup X, IsSylowOf 2 Q (CMK (centralizer ({x} : Set X)) K) ∧
    (IsCyclic ↥Q ∨ IsMaximalClassTwoGroup ↥Q)

@[expose] def S_prop34 : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (x : X) (K : Subgroup X), Prop34Hyp X x K →
    ∀ f : X, f ∈ centralizer ({x} : Set X) → orderOf f = 2 → ¬ InducesFAutL2A7 f K

@[expose] def B_prop34_realize : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (x : X) (K : Subgroup X), Prop34Hyp X x K →
    ∀ f : X, f ∈ centralizer ({x} : Set X) → orderOf f = 2 → InducesFAutL2A7 f K →
      ∃ (T P Q : Subgroup X) (z h : X), Cfg34 X T P Q x z f h

theorem prop34_core_all {X : Type} [Group X] [Finite X] {T P Q : Subgroup X} {x z f h : X}
    (c : Cfg34 X T P Q x z f h) : False :=
  prop34_core_of_dihedral c dihedralShapeFacts dihedralMaxFacts

theorem s_prop34_of_realize (hR : B_prop34_realize) : S_prop34 := by
  intro X _ _ x K hK f hf hfo hind
  obtain ⟨T, P, Q, z, h, c⟩ := hR X x K hK f hf hfo hind
  exact prop34_core_all c

end CFSG.GH74.GLS.C3.Layer1.P34

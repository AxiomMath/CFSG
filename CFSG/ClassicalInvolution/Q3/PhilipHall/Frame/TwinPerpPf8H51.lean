module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinLayer
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpPf5Ih
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpPf5M0
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpPfCore

public section

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q8P.P24

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Balance.Bootstrap
  CFSG.ClassicalInvolution.Q8P.Asc77
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinLayer (tqMembers exactCore)
open CFSG CFSG.ClassicalInvolution.Q3

@[expose] def Hyp51TwinInnerAt {G : Type} [Group G] [Finite G] (Ω : Set (Subgroup G)) : Prop :=
  ∀ {K₀ : Subgroup G},
    AscStand Ω K₀ → CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThmE.EIHAll (Nat.card G) →
      (∀ M ∈ Ω, IsPGroup 2 (↥M ⧸ classicalInvolutionOddCore ↥M)) → ∀ {K K' : Subgroup G} {b d c : G}, K ∈ Ω →
      K' ∈ Ω → K' ≠ K → IsUniqueInvolution K b → IsUniqueInvolution K' b → K ∈ tqMembers Ω c →
      K' ∈ tqMembers Ω c → ∀ {B : Subgroup G}, IsElemAbelian 2 B → b ∈ B → d ∈ B →
        c ∈ B → B = Subgroup.closure ({b, d, c} : Set G) → c ≠ 1 → b ≠ c → d ≠ 1 → d ≠ b →
        d * d = 1 → d ∈ exactCore c K ⊔ exactCore c K' → Hyp51At B c

@[expose] def Hyp51TwinInnerPerp (n : ℕ) : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (R : Subgroup Y) (S : Sylow 2 R) (t : Y),
    CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp.PerpHypS n Y R S t →
      Hyp51TwinInnerAt (CoreAssembly.conjClass (tightCore R))

end CFSG.ClassicalInvolution.Q8P.P24

module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinSetBase

public section

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
  CFSG.ClassicalInvolution.Q3

structure TwinCoreHyp (n : ℕ) (Y : Type) [Group Y] [Finite Y] (R : Subgroup Y) (S : Sylow 2 R)
    (t : Y) : Prop where
  card : Nat.card Y = n
  simple : IsSimpleGroup ↥(genFittingFStar Y)
  nonab : ∃ a b : ↥(genFittingFStar Y), a * b ≠ b * a
  below : CIT3Below n
  tbelow : TightBelow n
  twinBelow : Thm1RTwinHasLiftBelow n
  datum : QuaternionBridge.Q8TwinDatum R S t
  q8 : Nonempty (↥(S : Subgroup R) ≃* QuaternionGroup 2)
  gen : TightSelfGen R
  oddFree : TightOddFree Y
  hyp : HypOmegaGen (CoreAssembly.conjClass (tightCore R))
  aEmpty : AEmpty (CoreAssembly.conjClass (tightCore R)) (tightCore R)
  twin : ∃ K' ∈ twinSet (CoreAssembly.conjClass (tightCore R)) (tightCore R), K' ≠ tightCore R

@[expose] def TwinCoreDiscPerp (n : ℕ) : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (R : Subgroup Y) (S : Sylow 2 R) (t : Y),
    TwinCoreHyp n Y R S t → ¬ Disconnected.DConnected (CoreAssembly.conjClass (tightCore R)) →
      KPerp (CoreAssembly.conjClass (tightCore R)) (tightCore R) ≠
        twinSet (CoreAssembly.conjClass (tightCore R)) (tightCore R) → False

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame

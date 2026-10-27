module

public import CFSG.Blueprint.SourceClassicalTransport
public import CFSG.CGT.PushingUpLit.SolKNA.R4.TwinPerp23Main
public import CFSG.CGT.PushingUpLit.SolKNA.R4.TwinPerp23TwoAlg

public section

set_option linter.unusedSectionVars false

namespace CFSG.CGT.PushingUpLit.SolKNA.R4

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.PhilipHall.QuaternionBridge
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
open CFSG.ClassicalInvolution.Balance
open CFSG.ClassicalInvolution.Balance.Bootstrap (trivialOnQuot)
open scoped commutatorElement

namespace Perp23

namespace Three

section Data


variable {r n : ℕ} {Y : Type} [Group Y] [Finite Y] {R : Subgroup Y} {S : Sylow 2 R} {t : Y}

structure Data (r n : ℕ) (Y : Type) [Group Y] [Finite Y] (R : Subgroup Y) (S : Sylow 2 R) (t : Y) where
  h : PerpHypR r n Y R S t
  h2 : TwinPerp.TwoTwins R
  W : Subgroup Y
  hW : W ∈ WSet (CoreAssembly.conjClass (tightCore R))
  htW : t ∈ W
  hS4 : MuIsoS4 (CoreAssembly.conjClass (tightCore R)) W
  K' : Subgroup Y
  hK' : K' ∈ twinSet (CoreAssembly.conjClass (tightCore R)) (tightCore R)
  hne : K' ≠ tightCore R
  D : Two.TwoFrame (CoreAssembly.conjClass (tightCore R)) W (tightCore R) K' t

namespace Data

variable (d : Data r n Y R S t)

include d

theorem hΩ : HypOmegaGen (CoreAssembly.conjClass (tightCore R)) := d.h.core.hyp

theorem hKΩ : tightCore R ∈ CoreAssembly.conjClass (tightCore R) :=
  CoreAssembly.mem_conjClass_self _

theorem hK'Ω : d.K' ∈ CoreAssembly.conjClass (tightCore R) := d.hK'.1

theorem hc : ∀ x ∈ d.W, ∀ y ∈ d.W, x * y = y * x := WTool.comm_of_mem_wSet d.hΩ d.hW

theorem ctx : Q3CL.Thompson.Ctx (CoreAssembly.conjClass (tightCore R)) d.W :=
  Q3CL.T8.ctxOf d.h.partIHypG d.hW

theorem hz : IsUniqueInvolution (tightCore R) t := d.D.hzK

theorem hz' : IsUniqueInvolution d.K' t := d.D.hzK'

theorem hpair : twinSet (CoreAssembly.conjClass (tightCore R)) (tightCore R) = {tightCore R, d.K'} :=
  TwinPerp.twinSet_eq_pair d.h2 d.hK' d.hne

theorem hW2 : IsPGroup 2 d.W := Sec7.isPGroup_of_mem_WSet d.hW

theorem R_le_normalizer : d.D.F.ρ.R ≤ Subgroup.normalizer (d.W : Set Y) := d.D.F.ρ.hR.2

theorem R'_le_normalizer : d.D.F.ρ'.R ≤ Subgroup.normalizer (d.W : Set Y) := d.D.F.ρ'.hR.2

theorem hRK : IsSylow2In d.D.F.ρ.R (tightCore R) := by
  have := d.D.F.ρ.hRK
  rwa [d.D.hρK] at this

theorem hRK' : IsSylow2In d.D.F.ρ'.R d.K' := by
  have := d.D.F.ρ'.hRK
  rwa [d.D.hρ'K] at this

theorem h2all : ∀ M ∈ CoreAssembly.conjClass (tightCore R),
    IsPGroup 2 (↥M ⧸ classicalInvolutionOddCore ↥M) := fun _ hM =>
  Perp23.isPGroup_quot_of_member d.h hM

end Data

end Data

end Three

end Perp23

end CFSG.CGT.PushingUpLit.SolKNA.R4

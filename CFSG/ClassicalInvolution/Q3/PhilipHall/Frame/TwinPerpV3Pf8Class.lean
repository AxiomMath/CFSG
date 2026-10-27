module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinExitPf6Pull
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.PairNormal
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDiscData
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpWz
public import CFSG.ClassicalInvolution.SmallCases.A7T22Hyp
public import CFSG.ClassicalInvolution.SmallCases.A7T22ZStar

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
  CFSG.ClassicalInvolution.Balance CFSG.ClassicalInvolution.Q3
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDisc CFSG.ClassicalInvolution.Uniform
  CFSG.ClassicalInvolution.Q3.Q3NL
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinExitPf6

open CFSG.ClassicalInvolution.Balance.Bootstrap (trivialOnQuot)

section Class

section Std

variable {n : ℕ} {Y : Type} [Group Y] [Finite Y] {R : Subgroup Y} {S : Sylow 2 R} {t : Y}
  {K K' K₃ : Subgroup Y} {u₁ u₂ u₃ : Y}

theorem tq_of_hyp22G (d : A7T22.Hyp22G (CoreAssembly.conjClass (tightCore R)) K K' K₃ t u₁ u₂ u₃) :
    K₃ ∈ tqMembers3 (CoreAssembly.conjClass (tightCore R)) (u₁ * u₂) := by
  refine ⟨d.hK₃.1, ?_⟩
  have t13 : u₁ ∈ trivialOnQuot K₃ :=
    A7T22.le_trivialOnQuot_of_twin d.hyp d.mem d.hK₃.1 d.hK₃K.symm d.hz d.hzK₃ d.hu₁.1
  have t23 : u₂ ∈ trivialOnQuot K₃ :=
    A7T22.le_trivialOnQuot_of_twin d.hyp d.hK'.1 d.hK₃.1 d.hK₃K'.symm d.hzK' d.hzK₃ d.hu₂.1
  exact (trivialOnQuot K₃).mul_mem t13 t23

end Std

end Class

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3

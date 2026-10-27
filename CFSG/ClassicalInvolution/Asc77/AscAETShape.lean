module

public import CFSG.ClassicalInvolution.Asc77.WP3FrameBootTwinFrame
import CFSG.ClassicalInvolution.Asc77.AscT7AHyp51
import CFSG.ClassicalInvolution.Asc77.AscE187Img
import CFSG.ClassicalInvolution.Asc77.ModOApi
import CFSG.ClassicalInvolution.ModelFacts.ClauseZero
import CFSG.ClassicalInvolution.Balance.PassTwoModelFacts
import CFSG.ClassicalInvolution.Asc77.AscE187Basic
import CFSG.ClassicalInvolution.Asc77.AscE187Cop
import CFSG.ClassicalInvolution.Asc77.AscThmABasic

public section

namespace CFSG.ClassicalInvolution.Asc77.AscAET

open CFSG CFSG.Open CFSG.ComponentClassification CFSG.ClassicalInvolution
  CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Generic.DeltaClosure
  CFSG.ClassicalInvolution.Generic.CoreAssembly
  CFSG.ClassicalInvolution.Balance CFSG.ClassicalInvolution.Balance.Bootstrap
  CFSG.ClassicalInvolution.Asc77.ExactLayer CFSG.ClassicalInvolution.RouteD
open CFSG.Assembly.LowTwoRank

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G]

theorem exists_omegaOfSet_nonempty_of_twinExactShape (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f)
    {K : Subgroup G} {z : G} (hΩ : HypOmegaMod p f (CoreAssembly.conjClass K))
    (hz : IsClassicalMember p f K z) (hshape : TwinExactShape p f K z) :
    ∃ M ∈ CoreAssembly.conjClass K,
      (omegaOfSet (CoreAssembly.conjClass K) (twinSet (CoreAssembly.conjClass K) M)).Nonempty := by
  have hKz : IsUniqueInvolution K z :=
    ConnectedA2.isUniqueInvolution_of_isClassicalMember hp2 hq hz
  obtain ⟨⟨D, hD⟩, T, hT, hcomm, hTz⟩ := hshape
  let X : XCtx p f (CoreAssembly.conjClass K) z :=
    { K := K, hK := CoreAssembly.mem_conjClass_self K, hKz := hKz, hΩ := hΩ, hp := hp2,
      hq := hq, D := D }
  obtain ⟨C, ⟨S⟩⟩ := exists_twinShapeCtx X hD hT hTz hcomm
  obtain ⟨L⟩ := C.exists_lift S
  have fd := L.frameData S
  exact ⟨L.K₁, L.hK₁, L.J, fd.hJ⟩

end CFSG.ClassicalInvolution.Asc77.AscAET

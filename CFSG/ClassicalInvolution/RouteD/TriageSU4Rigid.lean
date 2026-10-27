module

public import CFSG.ClassicalInvolution.RouteD.TriageSU4Main
public import CFSG.ClassicalInvolution.ModelFacts.D4RigidMain

public section

namespace CFSG.ClassicalInvolution.Generic.CoreAssembly

open CFSG.ClassicalInvolution.RouteD (D4FrameRigid)
open CFSG.Assembly.LowTwoRank

variable {p f : ℕ} [Fact p.Prime]

theorem su4LinearLift_of_frame_guarded (hP1 : P1RowSU4 p f)
    (hb : p ≠ 2 → 5 ≤ p ^ f → D4FrameRigid p f .POmegaPlus 4 f) : SU4LinearLiftStmt p f := by
  by_cases h : p ≠ 2 ∧ 5 ≤ p ^ f
  · exact su4LinearLift_of_frame hP1 (hb h.1 h.2)
  · intro G _ _ _ hnab K z S
    exact absurd ⟨S.odd, S.five⟩ h

theorem su4LinearLift_of_P1 (hP1 : P1RowSU4 p f) : SU4LinearLiftStmt p f :=
  su4LinearLift_of_frame_guarded hP1 fun hp2 hq => ModelFacts.D4Rigid.d4FrameRigid hp2 hq

end CFSG.ClassicalInvolution.Generic.CoreAssembly

module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.A6CFrameSim
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.A6CRep

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

variable {V : Type} [AddCommGroup V] [Module (ZMod 3) V] [FiniteDimensional (ZMod 3) V]
  {Q : QuadraticForm (ZMod 3) V} {n : ℕ} {c : ZMod 3}

theorem a6c_model_of_frame (fr : NFrame Q (Fin n) c) (hc : c ≠ 0) :
    ∃ m : A6CModel n (ProjSim Q), ∀ J : Finset (Fin n),
      m.ofMat (Matrix.diagonal fun i => if i ∈ J then (-1 : ZMod 3) else 1) =
        QuotientGroup.mk (orthToSim Q (fr.signChange J)) := by
  obtain ⟨m, hm⟩ := a6c_model_of_rep (piSim Q) (a6cFrameRep fr) (a6cFrameRep_sim fr hc)
    (fun _ hM => a6cFrameRep_surj fr hc hM) (a6cFrameRep_injective fr)
    (a6cFrameRep_mem_piSim fr)
  exact ⟨m, fun J => by rw [← a6cFrameRep_signChange fr J]; exact hm _⟩

end CFSG.OddStandard.SmallF3.Omega

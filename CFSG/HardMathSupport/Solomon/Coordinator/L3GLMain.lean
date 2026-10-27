module

public import CFSG.HardMathSupport.Solomon.Coordinator.L3GJDefs
public import CFSG.HardMathSupport.Solomon.Coordinator.L3GLBranchA

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.HardMathSupport.Solomon.LocalBalance

theorem lemma510iiLift_of_inputs (h31 : Lemma31) (h59 : Lemma59)
    (h191 : Lemma54Ns.Input19_1_2) : Lemma510iiLift := by
  intro G _ _ m hS hC B hB b hb hb1 L hL hty y hy hyB hy1
  obtain ⟨hLC, hdisj⟩ := hL
  rcases hdisj with ⟨hΛ, hψ⟩ | ⟨D, hD, hDnc⟩
  · exact l3gl_hasOrderThreeLift_branchA h31 h59 hS hC hB hb hb1 hLC hΛ hψ hty hy hyB hy1
  · exact l3gl_hasOrderThreeLift_branchB h191 hS hB.1.1 hb hb1 hLC hty hD hDnc hy hyB hy1

end CFSG.HardMathSupport.Solomon.Coordinator

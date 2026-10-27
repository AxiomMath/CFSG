module

public import CFSG.Certificates.Kernel.Trace6091.XReduce

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.KC.Trace6091

open CFSG.Monster CFSG.Monster.B CFSG.Monster.Existence CFSG.Monster.AxisCount Finset

@[expose] noncomputable def xBlk (arr : Array ℕ) : ℤ :=
  (∑ q ∈ range 276,
      (xTerm arr 0 (Model.thetaN 0 ^^^ pairD q) + xTerm arr 63 (Model.thetaN 63 ^^^ pairD q))) +
    (∑ t ∈ range 2048, ∑ i ∈ range 24,
      xTerm arr (Model.oddCode (2 * t) i) (Model.dualN (2 ^ i))) +
    (∑ o ∈ range 759, ∑ m ∈ range 64,
      xTerm arr (Native.octCodeG (KDense.octT o) (KDense.evenT m))
        (Model.dualN (Native.spreadG (Model.wordN (KDense.octT o)) (KDense.evenT m))))

@[expose] noncomputable def trK (arr : Array ℕ) : ℤ :=
  latTr (Native.GD.ofGen (Native.mkCtx ()) (.perm arr)) ^ 2 +
    latTr2 (Native.GD.ofGen (Native.mkCtx ()) (.perm arr)) + 2 * xBlk arr +
    2 * (wTr (Native.GD.ofGen (Native.mkCtx ()) (.perm arr)) *
      latTr (Native.GD.ofGen (Native.mkCtx ()) (.perm arr)))


theorem permTraceCheck_of_K (arr : Array ℕ) (hv : Native.permValid arr = true) {T : ℤ}
    (h : trK arr = 2 * T) : permTraceCheck arr T = true := by
  unfold permTraceCheck
  refine decide_eq_true ?_
  unfold traceVal
  rw [xTrC_perm_blocks arr hv, ← h, trK, xBlk]

end CFSG.KC.Trace6091

end

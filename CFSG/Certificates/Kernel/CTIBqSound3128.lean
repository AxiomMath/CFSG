module

public import Certificates.Data.Kernel.CTIBqBind
public import CFSG.Certificates.Kernel.CTIBqCore
public import CFSG.LocalAnalysis.EvenSmallLie.TwoE6.NativeFactsInputs
public import CFSG.Monster.B.CTIB.HOuter
public import CFSG.Monster.B.GSide.HInnerFusion
public import CFSG.LocalAnalysis.EvenSmallLie.FoursGroup

public section

namespace CFSG.KC.CTIBq

open CFSG.EvenSmallLie.TwoE6 CFSG.Monster.B.CTIB.Native

@[expose] def fgPairG (G : Array Nat) (a6 : List Nat) (v a : Nat) : Bool :=
  qmul G a 4456968 == qmul G 4456968 a &&
    qmul G 10541 a == qmul G (qmul G (autApply G a6.toArray a) 10541) v &&
    qmul G 10541 v == qmul G (autApply G a6.toArray v) 10541 &&
    qmul G v 4456968 == qmul G 4456968 v && qmul G v v == 0

@[expose] def fgG (G : Array Nat) (a6 : List Nat) : Bool :=
  fgPairG G a6 5131954 3138877 && fgPairG G a6 6537621 2916759 && fgPairG G a6 7180071 7635562 &&
    qmul G 5131954 6537621 == 7180071 && qmul G 6537621 5131954 == 7180071

theorem sound3128 (gL a6 a8 q1 q2 : List Nat) (GR A6 A8 Q1 Q2 : Nat)
    (hb : bindsL GR gL A6 a6 A8 a8 Q1 q1 Q2 q2 = true) (hk : fgK GR A6 = true) :
    fgG gL.toArray a6 = true := by
  obtain ⟨⟨hg, hGR⟩, ⟨ha6, hA6⟩, -⟩ := bindsL_spec hb
  have q : ∀ a b, a < 2 ^ 23 → b < 2 ^ 23 → qmulK (tbOf GR) a b = qmul gL.toArray a b :=
    fun a b ha hb => qmulK_eq hg hGR ha hb
  have ap : ∀ n, n < 2 ^ 23 → autApplyK (tbOf GR) A6 n = autApply gL.toArray a6.toArray n :=
    fun n hn => autApplyK_eq hg ha6 hGR hA6 hn
  simp only [fgK, Aux.strictB_eq, fgPairK, Aux.andB_eq, Bool.and_eq_true, Nat.beq_eq, and_assoc] at hk
  simp (disch := first | decide | exact autApply_lt _ | exact qmul_lt _ _) only [ap, q] at hk
  simp only [fgG, fgPairG, Bool.and_eq_true, beq_iff_eq, and_assoc]
  exact hk

end CFSG.KC.CTIBq

end

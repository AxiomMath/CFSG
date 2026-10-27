module

public import Certificates.Data.Kernel.CTIBqBind
public import CFSG.Certificates.Kernel.CTIBqCore
public import CFSG.LocalAnalysis.EvenSmallLie.TwoE6.Stroth22DihedralInputs
public import CFSG.LocalAnalysis.EvenSmallLie.TwoE6.Stroth22Native
public import CFSG.Monster.B.GSide.HInnerFusionY3

public section

namespace CFSG.KC.CTIBq

open CFSG.EvenSmallLie.TwoE6 CFSG.Monster.B.CTIB.Native

@[expose] def d8G (G : Array Nat) (a8 : List Nat) : Bool :=
  qmul G 2 2 == 0 && qmul G 32 32 == 0 && qmul G 2 1 == qmul G 1 2 &&
    qmul G 32 1 == qmul G 1 32 &&
    qmul G (qmul G 2 32) (qmul G 2 32) == 2 ^ 22 &&
    qmul G (qmul G 1 2) (qmul G 1 2) == 0 &&
    qmul G (qmul G 1 32) (qmul G 1 32) == 0 &&
    qmul G 9 9 == 0 && qmul G 3162 3162 == 0 &&
    qmul G 3162 128 == qmul G 128 3162 &&
    qmul G (sqCode 8) (qmul G (autApply G a8.toArray 3162) 3162) == 5449715 &&
    qmul G 2 1255411 == qmul G (qmul G 1255411 2) (2 ^ 22) &&
    qmul G (qmul G 128 2) (qmul G 128 2) == 0 &&
    qmul G (qmul G 128 9) (qmul G 128 9) == 0 &&
    qmul G (qmul G 128 3162) (qmul G 128 3162) == 0 &&
    qmul G 1255411 (2 ^ 22) == 5449715

theorem sound3140 (gL a6 a8 q1 q2 : List Nat) (GR A6 A8 Q1 Q2 : Nat)
    (hb : bindsL GR gL A6 a6 A8 a8 Q1 q1 Q2 q2 = true) (hk : d8K GR A8 = true) :
    d8G gL.toArray a8 = true := by
  obtain ⟨⟨hg, hGR⟩, -, ⟨ha8, hA8⟩, -⟩ := bindsL_spec hb
  have q : ∀ a b, a < 2 ^ 23 → b < 2 ^ 23 → qmulK (tbOf GR) a b = qmul gL.toArray a b :=
    fun a b ha hb => qmulK_eq hg hGR ha hb
  have ap : ∀ n, n < 2 ^ 23 → autApplyK (tbOf GR) A8 n = autApply gL.toArray a8.toArray n :=
    fun n hn => autApplyK_eq hg ha8 hGR hA8 hn
  have sq : sqCode 8 = 0 := by decide
  simp only [d8K, Aux.strictB_eq, Aux.andB_eq, Bool.and_eq_true, Nat.beq_eq, and_assoc] at hk
  simp (disch := first | decide | exact autApply_lt _ | exact qmul_lt _ _) only [ap, q] at hk
  simp only [d8G, sq, Bool.and_eq_true, beq_iff_eq, and_assoc]
  exact hk

end CFSG.KC.CTIBq

end

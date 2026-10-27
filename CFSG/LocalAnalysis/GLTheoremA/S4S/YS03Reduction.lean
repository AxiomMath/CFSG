module

public import CFSG.LocalAnalysis.GLTheoremA.S4S.Prop415Step10

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.HardMathSupport.Solomon.UniquenessMaximal

structure S4SInputs (G : Type) [Group G] [Finite G] (p : ℕ) : Prop where
  lBalance : LBalanceAt G p
  input18_3_4 : Input18_3_4
  i1810 : I1810UsedAt G p
  input14_5 : Input14_5Print
  i1912 : I1912At
  i1933 : I1933At G p
  i1913 : I1913At
  i2027 : I2027At
  i264 : I264At G p
  i91 : I91At G
  i147 : I147At G
  i1016 : I1016At G
  i71m12 : I71M12At G
  i1426 : I1426At G p

variable {G : Type} [Group G] [Finite G]

theorem stage4_of_inputs {m : ℕ} (hctx : ThmACtx G m) {p : ℕ} (hp : p ∈ Mu G m)
    (hS3 : Stage3 G p) (hS4o : Stage4Order G p) (hin : S4SInputs G p) : Stage4 G p := by
  have h413 : Lemma413At G p := lemma413 hctx hp hin.lBalance hin.i1810 (i145UsedAt_of hin.input14_5 p)
  have h414 : Lemma414At G p := lemma414 hctx hp hS3 hS4o hin.i1912 hin.i1933
  exact ⟨prop415 hctx hp hS3 hS4o h413 h414 hin.input18_3_4 hin.i1810
      (i145UsedAt_of hin.input14_5 p) hin.i264 hin.i91 hin.i147 hin.i1016 hin.i71m12 hin.i1426
      hin.i1912 hin.i1913 hin.i2027, h413, h414⟩

theorem ys03_of_inputs (hin : ∀ (G : Type) [Group G] [Finite G] (m : ℕ), ThmACtx G m →
    ∀ p ∈ Mu G m, S4SInputs G p) : YS03 :=
  fun G _ _ m hctx p hp hS3 hS4o => stage4_of_inputs hctx hp hS3 hS4o (hin G m hctx p hp)

end CFSG.LocalAnalysis.GLTheoremA

module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.Lemma37.QuasisimpleCoreC3Words
public import Mathlib.Data.Finset.Attr
public import Mathlib.Tactic.SetLike

public section

namespace CFSG.ProperTwoGeneratedCore.Lemma37.QuasisimpleCore

@[expose] def c3GenW (v : Fin 64) : Prop :=
  v.val % 4 = 0 ∧ v.val / 16 % 4 ≠ 0 ∧ v.val / 4 % 4 ≠ 0

instance : DecidablePred c3GenW := fun v => by unfold c3GenW; infer_instance

theorem c3Mul_forty_comm : ∀ w : Fin 64, c3Mul 40 w = c3Mul w 40 := by decide

theorem c3Mul_forty_forty : c3Mul 40 40 = 0 := by decide

theorem c3_thirtytwo : c3Mul 32 32 = 0 ∧ ¬ c3GenW 32 := by decide

end CFSG.ProperTwoGeneratedCore.Lemma37.QuasisimpleCore

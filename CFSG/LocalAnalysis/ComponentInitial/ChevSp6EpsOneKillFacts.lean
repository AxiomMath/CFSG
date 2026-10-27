module

public import CFSG.LocalAnalysis.ComponentInitial.ChevSp6EpsOneOqDataKill

public section

namespace CFSG.LocalAnalysis.ComponentInitial.ChevSp6EpsOne

theorem beta_radical : ∀ u : Bool, ∀ v, v < 64 → v ≠ 0 → ∃ w, w < 64 ∧ betaOf u v w ≠ 0 := by
  decide +kernel

theorem sing_ker : ∀ u : Bool, ∀ v, v < 64 → v ≠ 0 → qOf u v = 0 →
    4 ≤ ((List.range 64).filter fun w => betaOf u v w == 0).length := by
  decide +kernel

theorem nl_sing : ∀ v, v < 64 → wpart v = 0 → qOf false v = 0 := by decide +kernel

theorem nr_sing : ∀ v, v < 64 → wpart v = xpart v → qOf false v = 0 := by decide +kernel

theorem nl_nr_span :
    ∀ v, v < 64 → ∃ a, a < 64 ∧ wpart a = 0 ∧ wpart (a ^^^ v) = xpart (a ^^^ v) := by
  decide +kernel

theorem aniso : ∀ v, v < 64 → qOf true v = 0 → v = 0 := by decide +kernel

theorem wpart_xor : ∀ v, v < 64 → ∀ w, w < 64 → wpart (v ^^^ w) = wpart v ^^^ wpart w := by
  decide +kernel

theorem xpart_xor : ∀ v, v < 64 → ∀ w, w < 64 → xpart (v ^^^ w) = xpart v ^^^ xpart w := by
  decide +kernel

theorem omT_order : compT omT (compT omT omT) = idT ∧ omT ≠ idT := by decide +kernel

end CFSG.LocalAnalysis.ComponentInitial.ChevSp6EpsOne

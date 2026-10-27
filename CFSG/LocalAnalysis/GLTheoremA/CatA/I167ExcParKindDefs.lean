module

public import CFSG.Blueprint.Chevalley
public import CFSG.Open.LocalVocabulary

public section

namespace CFSG.LocalAnalysis.GLTheoremA.I167

open CFSG.Blueprint.Chevalley

@[expose] def excToQ {τ : Tag} (x : Fin τ.rank → ℤ) : Fin τ.rank → ℚ := fun i => (x i : ℚ)

@[simp] theorem excToQ_apply {τ : Tag} (x : Fin τ.rank → ℤ) (i : Fin τ.rank) :
    excToQ x i = (x i : ℚ) := rfl

@[simp] theorem excToQ_zero {τ : Tag} : excToQ (0 : Fin τ.rank → ℤ) = 0 := by
  funext i
  simp

theorem excToQ_add {τ : Tag} (x y : Fin τ.rank → ℤ) : excToQ (x + y) = excToQ x + excToQ y := by
  funext i
  simp

theorem excToQ_neg {τ : Tag} (x : Fin τ.rank → ℤ) : excToQ (-x) = -excToQ x := by
  funext i
  simp

theorem excToQ_sub {τ : Tag} (x y : Fin τ.rank → ℤ) : excToQ (x - y) = excToQ x - excToQ y := by
  funext i
  simp

theorem excToQ_zsmul {τ : Tag} (c : ℤ) (x : Fin τ.rank → ℤ) :
    excToQ (c • x) = (c : ℚ) • excToQ x := by
  funext i
  simp

theorem excToQ_single {τ : Tag} (i : Fin τ.rank) :
    excToQ (Pi.single i 1 : Fin τ.rank → ℤ) = (Pi.single i 1 : Fin τ.rank → ℚ) := by
  funext j
  by_cases h : j = i
  · subst h
    simp
  · simp [Pi.single_eq_of_ne h]

end CFSG.LocalAnalysis.GLTheoremA.I167

end

module

public import CFSG.HardMathSupport.Timmesfeld.LangTorus.ExcKacCount
public import CFSG.LieType.Steinberg.Adjoint.Pairs

public section

namespace CFSG.LocalAnalysis.GLTheoremA.I167

open CFSG.Blueprint.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.HardMathSupport.Timmesfeld.LangTorus

@[expose] def exc3core_extVec {r : ℕ} (θ : Fin r → ℤ) : Option (Fin r) → Fin r → ℤ
  | none => -θ
  | some j => Pi.single j 1

@[expose] def exc3core_extAdj (τ : Tag) (θ : Fin τ.rank → ℤ) (x y : Option (Fin τ.rank)) : Prop :=
  x ≠ y ∧ iform (exc3core_extVec θ x) (exc3core_extVec θ y) ≠ 0

instance (τ : Tag) (θ : Fin τ.rank → ℤ) (x y : Option (Fin τ.rank)) :
    Decidable (exc3core_extAdj τ θ x y) := by
  unfold exc3core_extAdj
  infer_instance

@[expose] def exc3core_noIso (τ : Tag) (θ : Fin τ.rank → ℤ) (C : Finset (Option (Fin τ.rank))) :
    Prop :=
  ∀ y ∈ C, C = {y} ∨ ∃ z ∈ C, exc3core_extAdj τ θ y z

instance (τ : Tag) (θ : Fin τ.rank → ℤ) (C : Finset (Option (Fin τ.rank))) :
    Decidable (exc3core_noIso τ θ C) := by
  unfold exc3core_noIso
  infer_instance

@[expose] def exc3core_thF4 : Fin Tag.F4.rank → ℤ := ![2, 3, 4, 2]

@[expose] def exc3core_thE6 : Fin Tag.E6.rank → ℤ := ![1, 2, 2, 3, 2, 1]

@[expose] def exc3core_thE7 : Fin Tag.E7.rank → ℤ := ![2, 2, 3, 4, 3, 2, 1]

@[expose] def exc3core_thE8 : Fin Tag.E8.rank → ℤ := ![2, 3, 4, 6, 5, 4, 3, 2]

@[expose] def exc3core_rankTabF4 (N r : ℕ) : Prop := (N = 6 → r = 2) ∧ (N = 18 → r = 3)

@[expose] def exc3core_rankTabE6 (N r : ℕ) : Prop :=
  (N = 2 → r = 1) ∧ (N = 6 → r = 2) ∧ (N = 20 → r = 4) ∧ (N = 24 → r = 4) ∧ (N = 30 → r = 5) ∧
    (N = 40 → r = 5)

@[expose] def exc3core_rankTabE7 (N r : ℕ) : Prop :=
  (N = 2 → r = 1) ∧ (N = 6 → r = 2) ∧ (N = 30 → r = 5) ∧ (N = 40 → r = 5) ∧ (N = 42 → r = 6) ∧
    (N = 60 → r = 6) ∧ (N = 72 → r = 6)

@[expose] def exc3core_rankTabE8 (N r : ℕ) : Prop :=
  (N = 6 → r = 2) ∧ (N = 72 → r = 6 ∨ r = 8) ∧ (N = 84 → r = 7) ∧ (N = 126 → r = 7)

instance (N r : ℕ) : Decidable (exc3core_rankTabF4 N r) := by
  unfold exc3core_rankTabF4
  infer_instance

instance (N r : ℕ) : Decidable (exc3core_rankTabE6 N r) := by
  unfold exc3core_rankTabE6
  infer_instance

instance (N r : ℕ) : Decidable (exc3core_rankTabE7 N r) := by
  unfold exc3core_rankTabE7
  infer_instance

instance (N r : ℕ) : Decidable (exc3core_rankTabE8 N r) := by
  unfold exc3core_rankTabE8
  infer_instance

end CFSG.LocalAnalysis.GLTheoremA.I167

end

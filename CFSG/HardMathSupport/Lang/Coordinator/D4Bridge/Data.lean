module

public import CFSG.Adapters.TauCetiExceptional.TwistedD4Data

public section

namespace CFSG.HardMathSupport.Lang.Coordinator.D4Bridge

open CFSG.Blueprint.Chevalley CFSG.LieType.Steinberg.Minuscule CFSG.TauCetiBridge.Twisted

abbrev Coord : Type := Fin 4 ⊕ Fin 4

@[expose] def natIdx : Coord → Fin 24
  | .inl i => ![0, 3, 6, 9] i
  | .inr i => ![21, 18, 15, 10] i

@[expose] def natSgn : Coord → ℤ
  | .inl _ => 1
  | .inr i => ![-1, 1, -1, 1] i

@[expose] def dualC : Coord → Coord
  | .inl i => .inr i
  | .inr i => .inl i

@[expose] def cIdx : Coord → Fin 4
  | .inl i => i
  | .inr i => i

@[expose] def opDig (k a : ℕ) : ℕ := dig (d4tData.op k) a

@[expose] def rootData : Fin 24 → Coord × Coord × ℤ :=
  ![(.inl 0, .inr 1, -1), (.inl 2, .inr 3, -1), (.inl 1, .inr 2, -1), (.inl 2, .inl 3, -1),
    (.inl 1, .inr 0, -1), (.inl 0, .inr 2, 1), (.inl 3, .inr 2, -1), (.inl 1, .inr 3, -1),
    (.inl 2, .inr 1, -1), (.inl 1, .inl 3, 1), (.inr 3, .inr 2, -1), (.inl 2, .inr 0, 1),
    (.inl 0, .inr 3, -1), (.inl 0, .inl 3, -1), (.inl 3, .inr 1, -1), (.inl 1, .inl 2, -1),
    (.inr 3, .inr 1, 1), (.inl 3, .inr 0, -1), (.inr 3, .inr 0, -1), (.inl 0, .inl 2, -1),
    (.inr 2, .inr 1, -1), (.inr 2, .inr 0, -1), (.inl 0, .inl 1, -1), (.inr 1, .inr 0, -1)]

abbrev rU (k : Fin 24) : Coord := (rootData k).1

abbrev rW (k : Fin 24) : Coord := (rootData k).2.1

abbrev rS (k : Fin 24) : ℤ := (rootData k).2.2

@[expose] def RootCond (k : Fin 24) (x : Coord) : Prop :=
  if x = dualC (rU k) then
    2 ≤ opDig k (natIdx x) ∧ ((natIdx (rW k) : ℕ) = opDig k (natIdx x) / 2 - 1) ∧
      natSgn x * (-1) ^ opDig k (natIdx x) * natSgn (rW k) = rS k
  else if x = dualC (rW k) then
    2 ≤ opDig k (natIdx x) ∧ ((natIdx (rU k) : ℕ) = opDig k (natIdx x) / 2 - 1) ∧
      natSgn x * (-1) ^ opDig k (natIdx x) * natSgn (rU k) = -rS k
  else opDig k (natIdx x) = 0

instance (k : Fin 24) (x : Coord) : Decidable (RootCond k x) := by
  unfold RootCond
  infer_instance

theorem rootCond_all : ∀ (k : Fin 24) (x : Coord), RootCond k x := by
  decide +kernel

theorem rootData_spec : ∀ k : Fin 24,
    cIdx (rU k) ≠ cIdx (rW k) ∧ (rS k = 1 ∨ rS k = -1) := by
  decide +kernel

theorem rootData_cover : ∀ u w : Coord, cIdx u ≠ cIdx w →
    ∃ k : Fin 24, (rU k = u ∧ rW k = w) ∨ (rU k = w ∧ rW k = u) := by
  decide +kernel

theorem natIdx_injective : Function.Injective natIdx := by
  decide +kernel

theorem natSgn_mul_self : ∀ x : Coord, natSgn x * natSgn x = 1 := by
  decide +kernel

theorem rootCertificate_length : Tag.D4.rootCertificate.roots.length = 24 := by
  decide +kernel

end CFSG.HardMathSupport.Lang.Coordinator.D4Bridge

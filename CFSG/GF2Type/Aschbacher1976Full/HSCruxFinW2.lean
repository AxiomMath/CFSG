module

public import Mathlib.Data.Nat.Notation

public section

namespace CFSG.GF2Type.Aschbacher1976Full.HS.FinW

structure Tup where
  i0 : ℕ
  i1 : ℕ
  i2 : ℕ
  i3 : ℕ

@[expose] def bf (x y : ℕ) : ℕ :=
  ((x % 2) * (y / 4 % 2) + (x / 4 % 2) * (y % 2) + (x / 2 % 2) * (y / 8 % 2) +
    (x / 8 % 2) * (y / 2 % 2)) % 2

@[expose] def ap (t : Tup) (x : ℕ) : ℕ :=
  (if x % 2 = 1 then t.i0 else 0) ^^^ (if x / 2 % 2 = 1 then t.i1 else 0) ^^^
    (if x / 4 % 2 = 1 then t.i2 else 0) ^^^ (if x / 8 % 2 = 1 then t.i3 else 0)

@[expose] def apN (t : Tup) : ℕ → ℕ → ℕ
  | 0, x => x
  | k + 1, x => ap t (apN t k x)

@[expose] def sq (t : Tup) : Tup := ⟨apN t 2 1, apN t 2 2, apN t 2 4, apN t 2 8⟩

@[expose] def keyT (t : Tup) : ℕ := t.i0 + 16 * t.i1 + 256 * t.i2 + 4096 * t.i3

@[expose] def L : List Tup :=
  (List.range 16).flatMap fun t0 =>
    ((List.range 16).filter fun t2 => bf t0 t2 == 1).flatMap fun t2 =>
      ((List.range 16).filter fun t1 => bf t0 t1 == 0 && bf t2 t1 == 0).flatMap fun t1 =>
        ((List.range 16).filter fun t3 =>
            bf t0 t3 == 0 && bf t2 t3 == 0 && bf t1 t3 == 1).map fun t3 => ⟨t0, t1, t2, t3⟩

@[expose] def Ord3 (t : Tup) : Prop := (∀ x < 16, apN t 3 x = x) ∧ ∃ x < 16, ap t x ≠ x

instance (t : Tup) : Decidable (Ord3 t) := by unfold Ord3; infer_instance

@[expose] def L3 : List Tup := L.filter fun t => decide (Ord3 t)

@[expose] def PairHyp (a c : Tup) : Prop :=
  keyT a ≤ keyT (sq a) ∧ keyT c ≤ keyT (sq c) ∧ keyT a ≤ keyT c ∧
    (∀ x < 16, ap a (ap c x) = ap c (ap a x)) ∧ (∃ x < 16, ap c x ≠ ap a x) ∧
      ∃ x < 16, ap c x ≠ apN a 2 x

instance (a c : Tup) : Decidable (PairHyp a c) := by unfold PairHyp; infer_instance

@[expose] def prodAp (a c : Tup) (p x : ℕ) : ℕ := apN a (p / 3) (apN c (p % 3) x)

@[expose] def FreeC (a c : Tup) (x : ℕ) : Prop := ∀ p < 9, p ≠ 0 → prodAp a c p x ≠ x

instance (a c : Tup) (x : ℕ) : Decidable (FreeC a c x) := by unfold FreeC; infer_instance

@[expose] def Qc (a c : Tup) (x : ℕ) : ℕ := if x = 0 ∨ FreeC a c x then 0 else 1

@[expose] def QuadTab (qt : List ℕ) : Prop :=
  ∀ x < 16, ∀ y < 16, qt.getD (x ^^^ y) 0 = (qt.getD x 0 + qt.getD y 0 + bf x y) % 2

instance (qt : List ℕ) : Decidable (QuadTab qt) := by unfold QuadTab; infer_instance

@[expose] def Differ (a c : Tup) (p p' : ℕ) : Prop := ∃ x < 16, prodAp a c p x ≠ prodAp a c p' x

instance (a c : Tup) (p p' : ℕ) : Decidable (Differ a c p p') := by unfold Differ; infer_instance

@[expose] def Distinct9 (a c : Tup) : Prop := ∀ p < 9, ∀ p' < 9, p ≠ p' → Differ a c p p'

instance (a c : Tup) : Decidable (Distinct9 a c) := by unfold Distinct9; infer_instance

@[expose] def PairOk (a c : Tup) : Prop :=
  Distinct9 a c ∧ QuadTab ((List.range 16).map (Qc a c))

instance (a c : Tup) : Decidable (PairOk a c) := by unfold PairOk; infer_instance

theorem exp_three : ∀ t ∈ L, (∀ x < 16, apN t 9 x = x) → ∀ x < 16, apN t 3 x = x := by
  decide +kernel

theorem pairs_ok : ∀ a ∈ L3, ∀ c ∈ L3, PairHyp a c → PairOk a c := by
  decide +kernel

end CFSG.GF2Type.Aschbacher1976Full.HS.FinW

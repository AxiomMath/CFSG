module

public import Mathlib.Data.Fintype.Prod
public import Mathlib.Data.ZMod.Defs
public import Mathlib.Tactic.Ring.RingNF

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33.S4B

@[expose] abbrev S3M2 : Type := ZMod 4 × ZMod 4 × ZMod 4 × ZMod 4

@[expose] def s3mul (x y : S3M2) : S3M2 :=
  (x.1 * y.1 + x.2.1 * y.2.2.1, x.1 * y.2.1 + x.2.1 * y.2.2.2,
   x.2.2.1 * y.1 + x.2.2.2 * y.2.2.1, x.2.2.1 * y.2.1 + x.2.2.2 * y.2.2.2)

@[expose] def s3one : S3M2 := (1, 0, 0, 1)

@[expose] def s3neg : S3M2 := (3, 0, 0, 3)

@[expose] def s3vec (x : S3M2) (v : ZMod 4 × ZMod 4) : ZMod 4 × ZMod 4 :=
  (x.1 * v.1 + x.2.1 * v.2, x.2.2.1 * v.1 + x.2.2.2 * v.2)

@[expose] def S3RValid (R : S3M2) : Prop :=
  s3mul (s3mul R R) R = s3one ∧ ∀ v : ZMod 4 × ZMod 4, s3vec R v = v → v = (0, 0)

instance : DecidablePred S3RValid := fun R => by unfold S3RValid; infer_instance

@[expose] def s3det (P : S3M2) : ZMod 4 := P.1 * P.2.2.2 - P.2.1 * P.2.2.1

@[expose] def S3DetUnit (P : S3M2) : Prop := s3det P * s3det P = 1

instance : DecidablePred S3DetUnit := fun P => by unfold S3DetUnit; infer_instance

@[expose] def S3Inverts (R C : S3M2) : Prop := s3mul C R = s3mul (s3mul R R) C

instance (R C : S3M2) : Decidable (S3Inverts R C) := by unfold S3Inverts; infer_instance

@[expose] def S3Comm (R C P : S3M2) : Prop := s3mul P R = s3mul R P ∧ s3mul P C = s3mul C P

instance (R C P : S3M2) : Decidable (S3Comm R C P) := by unfold S3Comm; infer_instance

@[expose] def S3PmOne (P : S3M2) : Prop := P = s3one ∨ P = s3neg

instance (P : S3M2) : Decidable (S3PmOne P) := by unfold S3PmOne; infer_instance

@[expose] def S3Inner (R C : S3M2) : Prop := ∀ P : S3M2, S3Comm R C P → S3DetUnit P → S3PmOne P

instance (R C : S3M2) : Decidable (S3Inner R C) := by unfold S3Inner; infer_instance

@[expose] def S3Mid (R : S3M2) : Prop :=
  ∀ C : S3M2, S3Inverts R C → S3DetUnit C → S3Inner R C

instance (R : S3M2) : Decidable (S3Mid R) := by unfold S3Mid; infer_instance

theorem s3_matrix_core : ∀ R : S3M2, S3RValid R → S3Mid R := by
  decide +kernel

theorem s3_matrix {R C P : S3M2} (hR : S3RValid R) (hC : S3Inverts R C) (hCu : S3DetUnit C)
    (hP : S3Comm R C P) (hPu : S3DetUnit P) : S3PmOne P :=
  s3_matrix_core R hR C hC hCu P hP hPu

theorem s3det_mul (X Y : S3M2) : s3det (s3mul X Y) = s3det X * s3det Y := by
  simp only [s3det, s3mul]
  ring

theorem s3_detUnit_of_mul {X Y : S3M2} (h : s3mul X Y = s3one) : S3DetUnit X := by
  have h1 := congrArg s3det h
  rw [s3det_mul] at h1
  have h2 : s3det s3one = 1 := by decide
  rw [h2] at h1
  have key : ∀ d e : ZMod 4, d * e = 1 → d * d = 1 := by decide
  exact key _ _ h1

end CFSG.OddStandard.SmallF3.HarrisU33.S4B

module

public import Mathlib.Algebra.Field.Defs
public import Mathlib.Data.Finset.Attr
public import Mathlib.Data.Fintype.Defs

public section

namespace CFSG.LieType.SeitzGeneration.HeisSmall

@[ext] structure M3 (R : Type) where
  a00 : R
  a01 : R
  a02 : R
  a10 : R
  a11 : R
  a12 : R
  a20 : R
  a21 : R
  a22 : R
deriving DecidableEq

namespace M3

variable {R S : Type} [CommRing R]

instance : One (M3 R) := ⟨⟨1, 0, 0, 0, 1, 0, 0, 0, 1⟩⟩

instance : Mul (M3 R) :=
  ⟨fun A B =>
    ⟨A.a00 * B.a00 + A.a01 * B.a10 + A.a02 * B.a20, A.a00 * B.a01 + A.a01 * B.a11 + A.a02 * B.a21,
      A.a00 * B.a02 + A.a01 * B.a12 + A.a02 * B.a22,
      A.a10 * B.a00 + A.a11 * B.a10 + A.a12 * B.a20, A.a10 * B.a01 + A.a11 * B.a11 + A.a12 * B.a21,
      A.a10 * B.a02 + A.a11 * B.a12 + A.a12 * B.a22,
      A.a20 * B.a00 + A.a21 * B.a10 + A.a22 * B.a20, A.a20 * B.a01 + A.a21 * B.a11 + A.a22 * B.a21,
      A.a20 * B.a02 + A.a21 * B.a12 + A.a22 * B.a22⟩⟩

theorem mul_def (A B : M3 R) :
    A * B = ⟨A.a00 * B.a00 + A.a01 * B.a10 + A.a02 * B.a20,
      A.a00 * B.a01 + A.a01 * B.a11 + A.a02 * B.a21, A.a00 * B.a02 + A.a01 * B.a12 + A.a02 * B.a22,
      A.a10 * B.a00 + A.a11 * B.a10 + A.a12 * B.a20, A.a10 * B.a01 + A.a11 * B.a11 + A.a12 * B.a21,
      A.a10 * B.a02 + A.a11 * B.a12 + A.a12 * B.a22,
      A.a20 * B.a00 + A.a21 * B.a10 + A.a22 * B.a20, A.a20 * B.a01 + A.a21 * B.a11 + A.a22 * B.a21,
      A.a20 * B.a02 + A.a21 * B.a12 + A.a22 * B.a22⟩ := rfl

@[expose] def smul (c : R) (A : M3 R) : M3 R :=
  ⟨c * A.a00, c * A.a01, c * A.a02, c * A.a10, c * A.a11, c * A.a12, c * A.a20, c * A.a21,
    c * A.a22⟩

@[expose] def det (A : M3 R) : R :=
  A.a00 * A.a11 * A.a22 - A.a00 * A.a12 * A.a21 - A.a01 * A.a10 * A.a22 +
    A.a01 * A.a12 * A.a20 + A.a02 * A.a10 * A.a21 - A.a02 * A.a11 * A.a20

@[expose] def map (g : R → S) (A : M3 R) : M3 S :=
  ⟨g A.a00, g A.a01, g A.a02, g A.a10, g A.a11, g A.a12, g A.a20, g A.a21, g A.a22⟩

@[expose] def transpose (A : M3 R) : M3 R :=
  ⟨A.a00, A.a10, A.a20, A.a01, A.a11, A.a21, A.a02, A.a12, A.a22⟩

end M3

variable {L : Type} [Field L] [DecidableEq L] [Fintype L]

@[expose] def dM3 (ω : L) : M3 L := ⟨1, 0, 0, 0, ω, 0, 0, 0, ω ^ 2⟩

@[expose] def sM3 : M3 L := ⟨0, 0, 1, 1, 0, 0, 0, 1, 0⟩

@[expose] def lineList (ω : L) : List (M3 L) :=
  [dM3 ω, sM3, dM3 ω * sM3, dM3 ω * sM3 * sM3]

@[expose] def GenOk (q : ℕ) (ω : L) (G : M3 L) : Prop :=
  G.det = 1 ∧ (G.map (· ^ q)).transpose * G = 1 ∧
    ∃ M ∈ lineList ω, ∃ c : L, G * M = M3.smul c (M * G)

instance (q : ℕ) (ω : L) (G : M3 L) : Decidable (GenOk q ω G) := by
  unfold GenOk
  infer_instance

@[expose] def evalW (letters : List (M3 L)) : List ℕ → M3 L
  | [] => 1
  | i :: w => letters.getD i 1 * evalW letters w

@[expose] def blockM3 (q : ℕ) (a b : L) : M3 L := ⟨a, b, 0, -(b ^ q), a ^ q, 0, 0, 0, 1⟩

@[expose] def CoverOk (q : ℕ) (vals : List (M3 L)) : Prop :=
  ∀ a b : L, a * a ^ q + b * b ^ q = 1 → blockM3 q a b ∈ vals

instance (q : ℕ) (vals : List (M3 L)) : Decidable (CoverOk q vals) := by
  unfold CoverOk
  infer_instance

@[expose] def coverBool (q : ℕ) (vals : List (M3 L)) : Bool := decide (CoverOk q vals)

@[expose] def heisCheck (q : ℕ) (ω : L) (gens : List (M3 L)) (ws₁ ws₂ : List (List ℕ)) : Bool :=
  gens.all (fun G => decide (GenOk q ω G)) &&
    coverBool q (ws₂.map (evalW (ws₁.map (evalW gens))))

@[expose] def decodeWords (s : String) : List (List ℕ) :=
  (s.splitOn ",").map fun w => w.toList.map fun c => c.toNat - 48

end CFSG.LieType.SeitzGeneration.HeisSmall

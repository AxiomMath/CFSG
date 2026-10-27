module

public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.RankThree.Chevalley.SteinbergCEF4PlaneAssembly
public import CFSG.RankThree.PartOne.KE.OrdinaryEPointwise
public import CFSG.RankThree.PartOne.KE6.E8T3SevenInputs

public noncomputable section

namespace CFSG.LocalAnalysis.GLTheoremA.Y10F.ExcE8Three

open Matrix CFSG CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.RankThree.Chevalley CFSG.RankThree.Lattice CFSG.RankThree.PartOne
  CFSG.RankThree.PartOne.KE CFSG.RankThree.PartOne.KE6
open CFSG.RankThree.E6 (charVal)


section Certs


@[expose]
def e8T3XColumn {p : ℕ} (ε : ℤ) (q : ZMod p) : Fin Tag.E8.rank → ZMod p :=
  Pi.single (3 : Fin Tag.E8.rank) 1 +
  Pi.single (4 : Fin Tag.E8.rank) (-2 - (ε : ZMod p) * q) +
  Pi.single (5 : Fin Tag.E8.rank) (1 + (ε : ZMod p) * q)

@[expose]
def e8T3ZColumn {p : ℕ} (ε : ℤ) (q : ZMod p) : Fin Tag.E8.rank → ZMod p :=
  Pi.single (2 : Fin Tag.E8.rank) 1 +
  Pi.single (4 : Fin Tag.E8.rank) (-2 - (ε : ZMod p) * q) +
  Pi.single (5 : Fin Tag.E8.rank) 1 +
  Pi.single (6 : Fin Tag.E8.rank) (1 + (ε : ZMod p) * q) +
  Pi.single (7 : Fin Tag.E8.rank) ((ε : ZMod p) * q)

@[expose]
def e8T3XA (α : Fin Tag.E8.rank → ℤ) : ℤ := α 3 - 2 * α 4 + α 5

@[expose]
def e8T3XD (α : Fin Tag.E8.rank → ℤ) : ℤ := -α 4 + α 5

@[expose]
def e8T3ZA (α : Fin Tag.E8.rank → ℤ) : ℤ := α 2 - 2 * α 4 + α 5 + α 6

@[expose]
def e8T3ZD (α : Fin Tag.E8.rank → ℤ) : ℤ := -α 4 + α 6 + α 7

@[expose]
def e8T3XKernel : Set (Fin Tag.E8.rank → ℤ) :=
  {α | IsRoot Tag.E8 α ∧ α 3 = α 4 ∧ α 4 = α 5}

@[expose]
def e8T3ZKernel : Set (Fin Tag.E8.rank → ℤ) :=
  {α | IsRoot Tag.E8 α ∧ α 2 - 2 * α 4 + α 5 + α 6 = 0 ∧ -α 4 + α 6 + α 7 = 0}

theorem charVal_column_add {τ : Tag} {p : ℕ} (z z' : Fin τ.rank → ZMod p)
    (α : Fin τ.rank → ℤ) :
    charVal (z + z') α = charVal z α + charVal z' α := by
  simp [charVal, Pi.add_apply, mul_add, Finset.sum_add_distrib]

theorem charVal_piSingle {τ : Tag} {p : ℕ} (c : ZMod p) (α : Fin τ.rank → ℤ)
    (j : Fin τ.rank) :
    charVal (Pi.single j c) α = c * (α j : ZMod p) := by
  simp only [charVal, Pi.single_apply]
  rw [Finset.sum_eq_single j]
  · simp [mul_comm]
  · intro b _ hb; simp [hb]
  · intro hj; exact absurd (Finset.mem_univ j) hj

theorem charVal_e8T3XColumn {p : ℕ} {ε : ℤ} {q : ZMod p}
    (α : Fin Tag.E8.rank → ℤ) :
    charVal (e8T3XColumn ε q) α =
      (e8T3XA α : ZMod p) + (ε : ZMod p) * q * (e8T3XD α : ZMod p) := by
  simp only [e8T3XColumn, charVal_column_add, charVal_piSingle]
  simp [e8T3XA, e8T3XD]
  ring

theorem charVal_e8T3ZColumn {p : ℕ} {ε : ℤ} {q : ZMod p}
    (α : Fin Tag.E8.rank → ℤ) :
    charVal (e8T3ZColumn ε q) α =
      (e8T3ZA α : ZMod p) + (ε : ZMod p) * q * (e8T3ZD α : ZMod p) := by
  simp only [e8T3ZColumn, charVal_column_add, charVal_piSingle]
  simp [e8T3ZA, e8T3ZD]
  ring

theorem e8T3XA_norm_mem (l : List ℤ) (hl : l ∈ Tag.E8.artifactRoots) :
    let α := toVec Tag.E8.rank l
    e8T3XA α * e8T3XA α - e8T3XA α * e8T3XD α + e8T3XD α * e8T3XD α ∈
      ({0, 1, 3} : Finset ℤ) := by
  revert l
  decide +kernel

theorem e8T3ZA_norm_mem (l : List ℤ) (hl : l ∈ Tag.E8.artifactRoots) :
    let α := toVec Tag.E8.rank l
    e8T3ZA α * e8T3ZA α - e8T3ZA α * e8T3ZD α + e8T3ZD α * e8T3ZD α ∈
      ({0, 1, 3, 4} : Finset ℤ) := by
  revert l
  decide +kernel

theorem e8T3_norm_identity {p : ℕ} {ε : ℤ} (hε : ε = 1 ∨ ε = -1) {q : ZMod p}
    (hq : q ^ 2 + (ε : ZMod p) * q + 1 = 0) (A D : ℤ) :
    ((A : ZMod p) + (ε : ZMod p) * q * (D : ZMod p)) *
      ((A : ZMod p) + (ε : ZMod p) * (-(ε : ZMod p) - q) * (D : ZMod p)) =
    ((A * A - A * D + D * D : ℤ) : ZMod p) := by
  have hε2 : (ε : ZMod p) * (ε : ZMod p) = 1 := by rcases hε with rfl | rfl <;> norm_num
  have hε2p : (ε : ZMod p) ^ 2 = 1 := by rw [sq, hε2]
  have hneg : (ε : ZMod p) * (-(ε : ZMod p)) = -1 := by linear_combination -hε2
  have hqq : q * (-(ε : ZMod p) - q) = 1 := by
    calc q * (-(ε : ZMod p) - q) = -(q ^ 2 + (ε : ZMod p) * q) := by ring
      _ = 1 := by linear_combination -hq
  have hsum : q + (-(ε : ZMod p) - q) = -(ε : ZMod p) := by ring
  have hmain : ((A : ZMod p) + (ε : ZMod p) * q * (D : ZMod p)) *
      ((A : ZMod p) + (ε : ZMod p) * (-(ε : ZMod p) - q) * (D : ZMod p)) =
      (A : ZMod p) ^ 2 - (A : ZMod p) * (D : ZMod p) + (D : ZMod p) ^ 2 := by
    calc
      ((A : ZMod p) + (ε : ZMod p) * q * (D : ZMod p)) *
          ((A : ZMod p) + (ε : ZMod p) * (-(ε : ZMod p) - q) * (D : ZMod p))
          = (A : ZMod p) ^ 2 + (ε : ZMod p) * (q + (-(ε : ZMod p) - q)) *
              ((A : ZMod p) * (D : ZMod p)) +
              ((ε : ZMod p) * (ε : ZMod p)) * (q * (-(ε : ZMod p) - q)) *
                (D : ZMod p) ^ 2 := by ring
      _ = (A : ZMod p) ^ 2 - (A : ZMod p) * (D : ZMod p) + (D : ZMod p) ^ 2 := by
        simp only [hsum, hqq, hneg, hε2]
        ring
  rw [hmain]
  push_cast
  ring

end Certs

end CFSG.LocalAnalysis.GLTheoremA.Y10F.ExcE8Three

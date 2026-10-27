
module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34FactsUnitaryLiftBase

@[expose] public section

namespace CFSG.ComponentClassification.GrSLit.L34Facts.Real

open CFSG Subgroup CFSG.PSL3Four CFSG.PSL3Four.Native CFSG.ComponentClassification.PSL3Four
open CFSG.LieType.Multipliers CFSG.LieType.Multipliers.L34 CFSG.CosetTable
open CFSG.ComponentClassification.GrSLit.L34Facts

variable {E : Type*} [Group E] {q : E →* Equiv.Perm (Fin 42)} {l : Cover →* E}

noncomputable abbrev zz (l : Cover →* E) (i j : ZMod 4) : E :=
  psi l (Multiplicative.ofAdd i, Multiplicative.ofAdd j)

noncomputable abbrev nf (l : Cover →* E) (k : ℕ) (i j : ZMod 4) :
    E :=
  l (cv (tw k)) * zz l i j

section Basic

theorem zz_mul (i j i' j' : ZMod 4) : zz l i j * zz l i' j' = zz l (i + i') (j + j') := by
  rw [zz, zz, zz, ← map_mul]
  rfl

theorem zz_zero : zz l 0 0 = 1 := map_one _

theorem zz_pow (i j : ZMod 4) (n : ℕ) : zz l i j ^ n = zz l (n * i) (n * j) := by
  rw [zz, zz, ← map_pow]
  congr 1
  refine Prod.ext ?_ ?_ <;> simp [← ofAdd_nsmul, nsmul_eq_mul]

theorem zz_inv (i j : ZMod 4) : (zz l i j)⁻¹ = zz l (-i) (-j) := by
  rw [zz, zz, ← map_inv]
  rfl

theorem zz_ofNat (a b : ℕ) : zz l a b = l z₁ ^ a * l z₂ ^ b := psi_ofAdd l a b

theorem nf_zero : nf l 0 0 0 = 1 := by
  rw [nf, zz_zero, mul_one]
  have : tw 0 = [] := by decide
  rw [this]
  exact map_one l

end Basic

@[expose] def kGens : List (ZMod 4 × ZMod 4) := [(1, 0), (0, 1), (1, 1), (1, 2), (2, 1), (1, 3)]

@[expose] def inK (κ : ZMod 4 × ZMod 4) (i j : ZMod 4) : Prop :=
  ∃ m : ZMod 4, m * κ.1 = i ∧ m * κ.2 = j

instance (κ : ZMod 4 × ZMod 4) (i j : ZMod 4) : Decidable (inK κ i j) := by
  unfold inK
  infer_instance

theorem kGens_spec : ∀ a b : ZMod 4, (a.val % 2 = 1 ∨ b.val % 2 = 1) →
    ∃ κ ∈ kGens, ∀ i j : ZMod 4, a * i + b * j = 0 ↔ inK κ i j := by
  decide

end CFSG.ComponentClassification.GrSLit.L34Facts.Real

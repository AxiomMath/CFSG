module

public import CFSG.Open.StatedDefs
public import Mathlib.GroupTheory.Commutator.Basic

public section

namespace CFSG.HardMathSupport.Timmesfeld.LieRank.O7

open Matrix
open scoped commutatorElement

abbrev K : Type := ZMod 3

abbrev M7 : Type := Matrix (Fin 7) (Fin 7) K

@[expose] def Q7 (v : Fin 7 → K) : K := v 0 * v 3 + v 1 * v 4 + v 2 * v 5 + v 6 ^ 2

@[expose] def Gm : M7 :=
  !![0, 0, 0, 1, 0, 0, 0;
    0, 0, 0, 0, 1, 0, 0;
    0, 0, 0, 0, 0, 1, 0;
    1, 0, 0, 0, 0, 0, 0;
    0, 1, 0, 0, 0, 0, 0;
    0, 0, 1, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 2]

theorem Q7_eq : ∀ v : Fin 7 → K, Q7 v = 2 * (v ⬝ᵥ Gm *ᵥ v) := by decide +kernel

theorem isom_of_gram {M : M7} (h : Mᵀ * Gm * M = Gm) (v : Fin 7 → K) :
    Q7 (M *ᵥ v) = Q7 v := by
  have h1 := Q7_eq (M *ᵥ v)
  have h2 := Q7_eq v
  have : (M *ᵥ v) ⬝ᵥ Gm *ᵥ (M *ᵥ v) = v ⬝ᵥ (Mᵀ * Gm * M) *ᵥ v := by
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
    conv_rhs => rw [Matrix.dotProduct_mulVec, Matrix.vecMul_transpose]
  rw [h1, h2, this, h]

@[expose] def isoSet : Set (GL (Fin 7) K) := {g | ∀ v, Q7 ((g : M7) *ᵥ v) = Q7 v}

@[expose] def Om7 : Subgroup (GL (Fin 7) K) :=
  ⁅Subgroup.closure isoSet, Subgroup.closure isoSet⁆

theorem mem_isoSet {g : GL (Fin 7) K} (h : (g : M7)ᵀ * Gm * (g : M7) = Gm) : g ∈ isoSet :=
  fun v => isom_of_gram h v

@[expose] def mk3 (M : M7) (h : M * M * M = 1) : GL (Fin 7) K :=
  ⟨M, M * M, by rw [← mul_assoc]; exact h, h⟩

@[expose] def mk2 (M : M7) (h : M * M = 1) : GL (Fin 7) K := ⟨M, M, h, h⟩

theorem mem_om_of_inv {t a : GL (Fin 7) K} (ht : t ∈ isoSet) (ha : a ∈ isoSet) (h3 : a ^ 3 = 1)
    (hinv : t * a * t⁻¹ = a⁻¹) : a ∈ Om7 := by
  have h : ⁅t, a⁆ = a := by
    rw [commutatorElement_def, hinv]
    have : a⁻¹ = a ^ 2 := by
      rw [inv_eq_iff_mul_eq_one, ← pow_succ', h3]
    rw [this, ← pow_add, show 2 + 2 = 3 + 1 by norm_num, pow_add, h3, one_mul, pow_one]
  rw [← h]
  exact Subgroup.commutator_mem_commutator (Subgroup.subset_closure ht) (Subgroup.subset_closure ha)

@[expose] def eA0 : M7 :=
  !![1, 0, 0, 0, 2, 0, 0;
  0, 1, 0, 1, 0, 0, 0;
  0, 0, 1, 0, 0, 0, 0;
  0, 0, 0, 1, 0, 0, 0;
  0, 0, 0, 0, 1, 0, 0;
  0, 0, 0, 0, 0, 1, 0;
  0, 0, 0, 0, 0, 0, 1]

@[expose] def eA1 : M7 :=
  !![1, 0, 0, 0, 0, 2, 0;
  0, 1, 0, 0, 0, 0, 0;
  0, 0, 1, 1, 0, 0, 0;
  0, 0, 0, 1, 0, 0, 0;
  0, 0, 0, 0, 1, 0, 0;
  0, 0, 0, 0, 0, 1, 0;
  0, 0, 0, 0, 0, 0, 1]

@[expose] def eA2 : M7 :=
  !![1, 2, 0, 0, 0, 0, 0;
  0, 1, 0, 0, 0, 0, 0;
  0, 0, 1, 0, 0, 0, 0;
  0, 0, 0, 1, 0, 0, 0;
  0, 0, 0, 1, 1, 0, 0;
  0, 0, 0, 0, 0, 1, 0;
  0, 0, 0, 0, 0, 0, 1]

@[expose] def eA3 : M7 :=
  !![1, 0, 2, 0, 0, 0, 0;
  0, 1, 0, 0, 0, 0, 0;
  0, 0, 1, 0, 0, 0, 0;
  0, 0, 0, 1, 0, 0, 0;
  0, 0, 0, 0, 1, 0, 0;
  0, 0, 0, 1, 0, 1, 0;
  0, 0, 0, 0, 0, 0, 1]

@[expose] def eA4 : M7 :=
  !![1, 0, 0, 2, 0, 0, 1;
  0, 1, 0, 0, 0, 0, 0;
  0, 0, 1, 0, 0, 0, 0;
  0, 0, 0, 1, 0, 0, 0;
  0, 0, 0, 0, 1, 0, 0;
  0, 0, 0, 0, 0, 1, 0;
  0, 0, 0, 1, 0, 0, 1]

@[expose] def eQ0 : M7 :=
  !![1, 0, 0, 0, 0, 0, 0;
  0, 1, 0, 0, 0, 2, 0;
  0, 0, 1, 0, 1, 0, 0;
  0, 0, 0, 1, 0, 0, 0;
  0, 0, 0, 0, 1, 0, 0;
  0, 0, 0, 0, 0, 1, 0;
  0, 0, 0, 0, 0, 0, 1]

@[expose] def eQ1 : M7 :=
  !![1, 0, 0, 0, 0, 0, 0;
  0, 1, 2, 0, 0, 0, 0;
  0, 0, 1, 0, 0, 0, 0;
  0, 0, 0, 1, 0, 0, 0;
  0, 0, 0, 0, 1, 0, 0;
  0, 0, 0, 0, 1, 1, 0;
  0, 0, 0, 0, 0, 0, 1]

@[expose] def eQ2 : M7 :=
  !![1, 0, 0, 0, 0, 0, 0;
  0, 1, 0, 0, 2, 0, 1;
  0, 0, 1, 0, 0, 0, 0;
  0, 0, 0, 1, 0, 0, 0;
  0, 0, 0, 0, 1, 0, 0;
  0, 0, 0, 0, 0, 1, 0;
  0, 0, 0, 0, 1, 0, 1]

@[expose] def eQ3 : M7 :=
  !![1, 0, 0, 0, 0, 0, 0;
  0, 1, 0, 0, 0, 0, 0;
  0, 0, 1, 0, 0, 2, 1;
  0, 0, 0, 1, 0, 0, 0;
  0, 0, 0, 0, 1, 0, 0;
  0, 0, 0, 0, 0, 1, 0;
  0, 0, 0, 0, 0, 1, 1]

@[expose] def eT0 : M7 :=
  !![1, 0, 0, 0, 0, 0, 0;
  0, 2, 0, 0, 0, 0, 0;
  0, 0, 1, 0, 0, 0, 0;
  0, 0, 0, 1, 0, 0, 0;
  0, 0, 0, 0, 2, 0, 0;
  0, 0, 0, 0, 0, 1, 0;
  0, 0, 0, 0, 0, 0, 1]

@[expose] def eT1 : M7 :=
  !![1, 0, 0, 0, 0, 0, 0;
  0, 1, 0, 0, 0, 0, 0;
  0, 0, 2, 0, 0, 0, 0;
  0, 0, 0, 1, 0, 0, 0;
  0, 0, 0, 0, 1, 0, 0;
  0, 0, 0, 0, 0, 2, 0;
  0, 0, 0, 0, 0, 0, 1]

@[expose] def eT2 : M7 :=
  !![1, 0, 0, 0, 0, 0, 0;
  0, 1, 0, 0, 0, 0, 0;
  0, 0, 1, 0, 0, 0, 0;
  0, 0, 0, 1, 0, 0, 0;
  0, 0, 0, 0, 1, 0, 0;
  0, 0, 0, 0, 0, 1, 0;
  0, 0, 0, 0, 0, 0, 2]

@[expose] def eR0 : M7 :=
  !![1, 0, 0, 0, 0, 0, 0;
  0, 1, 0, 0, 0, 0, 0;
  0, 0, 1, 0, 0, 0, 0;
  0, 0, 0, 1, 0, 0, 0;
  0, 0, 0, 0, 1, 0, 0;
  0, 0, 0, 0, 0, 1, 0;
  0, 0, 0, 0, 0, 0, 2]

@[expose] def eR1 : M7 :=
  !![1, 0, 0, 0, 0, 0, 0;
  0, 1, 0, 0, 0, 0, 0;
  0, 0, 1, 0, 0, 0, 0;
  0, 0, 0, 1, 0, 0, 0;
  0, 0, 0, 0, 1, 0, 0;
  0, 0, 2, 0, 0, 1, 1;
  0, 0, 2, 0, 0, 0, 2]

@[expose] def eR2 : M7 :=
  !![1, 0, 0, 0, 0, 0, 0;
  0, 1, 0, 0, 0, 0, 0;
  0, 0, 1, 0, 0, 0, 0;
  0, 0, 0, 1, 0, 0, 0;
  0, 0, 0, 0, 1, 0, 0;
  0, 0, 0, 0, 0, 1, 0;
  0, 0, 0, 0, 0, 0, 2]

@[expose] def eR3 : M7 :=
  !![1, 0, 0, 0, 0, 0, 0;
  0, 1, 0, 0, 0, 0, 0;
  0, 0, 1, 0, 0, 0, 0;
  0, 0, 0, 1, 0, 0, 0;
  0, 2, 0, 0, 1, 0, 1;
  0, 0, 0, 0, 0, 1, 0;
  0, 2, 0, 0, 0, 0, 2]

@[expose] def eR4 : M7 :=
  !![1, 0, 0, 0, 0, 0, 0;
  0, 1, 0, 0, 0, 0, 0;
  0, 0, 1, 0, 0, 2, 1;
  0, 0, 0, 1, 0, 0, 0;
  0, 0, 0, 0, 1, 0, 0;
  0, 0, 0, 0, 0, 1, 0;
  0, 0, 0, 0, 0, 2, 2]

@[expose] def eR5 : M7 :=
  !![1, 0, 0, 0, 0, 0, 0;
  0, 1, 0, 0, 2, 0, 1;
  0, 0, 1, 0, 0, 0, 0;
  0, 0, 0, 1, 0, 0, 0;
  0, 0, 0, 0, 1, 0, 0;
  0, 0, 0, 0, 0, 1, 0;
  0, 0, 0, 0, 2, 0, 2]

@[expose] def gA0 : GL (Fin 7) K := mk3 eA0 (by decide +kernel)

@[expose] def gA1 : GL (Fin 7) K := mk3 eA1 (by decide +kernel)

@[expose] def gA2 : GL (Fin 7) K := mk3 eA2 (by decide +kernel)

@[expose] def gA3 : GL (Fin 7) K := mk3 eA3 (by decide +kernel)

@[expose] def gA4 : GL (Fin 7) K := mk3 eA4 (by decide +kernel)

@[expose] def gQ0 : GL (Fin 7) K := mk3 eQ0 (by decide +kernel)

@[expose] def gQ1 : GL (Fin 7) K := mk3 eQ1 (by decide +kernel)

@[expose] def gQ2 : GL (Fin 7) K := mk3 eQ2 (by decide +kernel)

@[expose] def gQ3 : GL (Fin 7) K := mk3 eQ3 (by decide +kernel)

@[expose] def gT0 : GL (Fin 7) K := mk2 eT0 (by decide +kernel)

@[expose] def gT1 : GL (Fin 7) K := mk2 eT1 (by decide +kernel)

@[expose] def gT2 : GL (Fin 7) K := mk2 eT2 (by decide +kernel)

@[expose] def gR0 : GL (Fin 7) K := mk2 eR0 (by decide +kernel)

@[expose] def gR1 : GL (Fin 7) K := mk2 eR1 (by decide +kernel)

@[expose] def gR2 : GL (Fin 7) K := mk2 eR2 (by decide +kernel)

@[expose] def gR3 : GL (Fin 7) K := mk2 eR3 (by decide +kernel)

@[expose] def gR4 : GL (Fin 7) K := mk2 eR4 (by decide +kernel)

@[expose] def gR5 : GL (Fin 7) K := mk2 eR5 (by decide +kernel)

theorem gA0_iso : gA0 ∈ isoSet := mem_isoSet (by decide +kernel)

theorem gA1_iso : gA1 ∈ isoSet := mem_isoSet (by decide +kernel)

theorem gA2_iso : gA2 ∈ isoSet := mem_isoSet (by decide +kernel)

theorem gA3_iso : gA3 ∈ isoSet := mem_isoSet (by decide +kernel)

theorem gA4_iso : gA4 ∈ isoSet := mem_isoSet (by decide +kernel)

theorem gQ0_iso : gQ0 ∈ isoSet := mem_isoSet (by decide +kernel)

theorem gQ1_iso : gQ1 ∈ isoSet := mem_isoSet (by decide +kernel)

theorem gQ2_iso : gQ2 ∈ isoSet := mem_isoSet (by decide +kernel)

theorem gQ3_iso : gQ3 ∈ isoSet := mem_isoSet (by decide +kernel)

theorem gT0_iso : gT0 ∈ isoSet := mem_isoSet (by decide +kernel)

theorem gT1_iso : gT1 ∈ isoSet := mem_isoSet (by decide +kernel)

theorem gT2_iso : gT2 ∈ isoSet := mem_isoSet (by decide +kernel)

theorem gR0_iso : gR0 ∈ isoSet := mem_isoSet (by decide +kernel)

theorem gR1_iso : gR1 ∈ isoSet := mem_isoSet (by decide +kernel)

theorem gR2_iso : gR2 ∈ isoSet := mem_isoSet (by decide +kernel)

theorem gR3_iso : gR3 ∈ isoSet := mem_isoSet (by decide +kernel)

theorem gR4_iso : gR4 ∈ isoSet := mem_isoSet (by decide +kernel)

theorem gR5_iso : gR5 ∈ isoSet := mem_isoSet (by decide +kernel)

theorem gA0_mem : gA0 ∈ Om7 :=
  mem_om_of_inv gT0_iso gA0_iso (by decide +kernel) (by decide +kernel)

theorem gA1_mem : gA1 ∈ Om7 :=
  mem_om_of_inv gT1_iso gA1_iso (by decide +kernel) (by decide +kernel)

theorem gA2_mem : gA2 ∈ Om7 :=
  mem_om_of_inv gT0_iso gA2_iso (by decide +kernel) (by decide +kernel)

theorem gA3_mem : gA3 ∈ Om7 :=
  mem_om_of_inv gT1_iso gA3_iso (by decide +kernel) (by decide +kernel)

theorem gA4_mem : gA4 ∈ Om7 :=
  mem_om_of_inv gT2_iso gA4_iso (by decide +kernel) (by decide +kernel)

theorem gQ0_mem : gQ0 ∈ Om7 :=
  mem_om_of_inv gT1_iso gQ0_iso (by decide +kernel) (by decide +kernel)

theorem gQ1_mem : gQ1 ∈ Om7 :=
  mem_om_of_inv gT1_iso gQ1_iso (by decide +kernel) (by decide +kernel)

theorem gQ2_mem : gQ2 ∈ Om7 :=
  mem_om_of_inv gT2_iso gQ2_iso (by decide +kernel) (by decide +kernel)

theorem gQ3_mem : gQ3 ∈ Om7 :=
  mem_om_of_inv gT2_iso gQ3_iso (by decide +kernel) (by decide +kernel)

theorem gG0_mem : ⁅gR0, gR1⁆ ∈ Om7 :=
  Subgroup.commutator_mem_commutator (Subgroup.subset_closure gR0_iso)
    (Subgroup.subset_closure gR1_iso)

theorem gG1_mem : ⁅gR2, gR3⁆ ∈ Om7 :=
  Subgroup.commutator_mem_commutator (Subgroup.subset_closure gR2_iso)
    (Subgroup.subset_closure gR3_iso)

theorem gG2_mem : ⁅gR4, gR5⁆ ∈ Om7 :=
  Subgroup.commutator_mem_commutator (Subgroup.subset_closure gR4_iso)
    (Subgroup.subset_closure gR5_iso)

@[expose] def aE : Fin 5 → Om7 :=
  ![⟨gA0, gA0_mem⟩, ⟨gA1, gA1_mem⟩, ⟨gA2, gA2_mem⟩, ⟨gA3, gA3_mem⟩, ⟨gA4, gA4_mem⟩]

@[expose] def qE : Fin 4 → Om7 :=
  ![⟨gQ0, gQ0_mem⟩, ⟨gQ1, gQ1_mem⟩, ⟨gQ2, gQ2_mem⟩, ⟨gQ3, gQ3_mem⟩]

@[expose] def gE : Fin 3 → Om7 :=
  ![⟨⁅gR0, gR1⁆, gG0_mem⟩, ⟨⁅gR2, gR3⁆, gG1_mem⟩, ⟨⁅gR4, gR5⁆, gG2_mem⟩]

end CFSG.HardMathSupport.Timmesfeld.LieRank.O7

module

public import CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.GroupA10Perm
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor

namespace A10Perm

open Equiv Equiv.Perm Subgroup

def L1 : Subgroup A10 where
  carrier := {σ | ∀ i : Fin 10, 5 ≤ (i : ℕ) → (σ : Perm (Fin 10)) i = i}
  mul_mem' := by
    intro a b ha hb i hi
    show (a : Perm (Fin 10)) ((b : Perm (Fin 10)) i) = i
    rw [hb i hi, ha i hi]
  one_mem' := fun i _ => rfl
  inv_mem' := by
    intro a ha i hi
    show ((a : Perm (Fin 10))⁻¹) i = i
    rw [Equiv.Perm.inv_eq_iff_eq]
    exact (ha i hi).symm

def L2 : Subgroup A10 where
  carrier := {σ | ∀ i : Fin 10, (i : ℕ) < 5 → (σ : Perm (Fin 10)) i = i}
  mul_mem' := by
    intro a b ha hb i hi
    show (a : Perm (Fin 10)) ((b : Perm (Fin 10)) i) = i
    rw [hb i hi, ha i hi]
  one_mem' := fun i _ => rfl
  inv_mem' := by
    intro a ha i hi
    show ((a : Perm (Fin 10))⁻¹) i = i
    rw [Equiv.Perm.inv_eq_iff_eq]
    exact (ha i hi).symm

end A10Perm

end CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor

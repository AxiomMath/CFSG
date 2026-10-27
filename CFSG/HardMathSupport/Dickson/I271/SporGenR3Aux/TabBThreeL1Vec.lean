module

public import CFSG.LieType.Chevalley.C2E6UnitaryFourDefs
import all CFSG.Fischer.F4
public import CFSG.Monster.B.Classical.E6AdjointTable

public section

namespace CFSG.HardMathSupport.Dickson.I271.TabBThreeL1

open CFSG.Monster.B.Classical.E6Adjoint CFSG.Blueprint.Chevalley CFSG.Fischer
open CFSG.LieType.Chevalley.C2E6Overlap (K)

@[expose] def toK (c : F4) : K := c

theorem toK_zero : toK 0 = 0 := rfl

theorem toK_one : toK 1 = 1 := rfl

theorem F4_cases (c : F4) : c = 0 ∨ c = 1 ∨ c = F4.ω ∨ c = F4.ω * F4.ω := by
  revert c
  decide

theorem lab_injective : Function.Injective lab := by
  intro i j h
  by_cases hi : (i : ℕ) < 6 <;> by_cases hj : (j : ℕ) < 6
  · rw [lab_of_lt hi, lab_of_lt hj] at h
    exact Fin.ext (Fin.mk.inj (Sum.inl_injective h))
  · rw [lab_of_lt hi, lab_of_ge hj] at h
    exact absurd h Sum.inl_ne_inr
  · rw [lab_of_ge hi, lab_of_lt hj] at h
    exact absurd h Sum.inr_ne_inl
  · rw [lab_of_ge hi, lab_of_ge hj] at h
    have h' := congrArg Subtype.val (Sum.inr_injective h)
    have hnd := e6Certificate_checkNodup
    simp only [RootCertificate.checkNodup, decide_eq_true_eq, e6Certificate_length] at hnd
    have := List.inj_on_of_nodup_map hnd (List.mem_range.2 (by omega : (i : ℕ) - 6 < 72))
      (List.mem_range.2 (by omega : (j : ℕ) - 6 < 72)) (congrArg List.ofFn h')
    exact Fin.ext (by omega)

theorem rootVec_lab {a : Fin 78} (ha : 6 ≤ (a : ℕ)) :
    rootVec Tag.E6 K (e6Certificate.root ((a : ℕ) - 6)) = Finsupp.single (lab a) 1 := by
  rw [rootVec_eq_single (isRoot_certRoot (by omega)), lab_of_ge (by omega)]

end CFSG.HardMathSupport.Dickson.I271.TabBThreeL1

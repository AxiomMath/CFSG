module

public import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4P1SL23
public import CFSG.Sporadic.SmallOddCore.Assembly
public import Certificates.Data.CFSGNative.SmallOddCore.Check

public section

namespace CFSG.ComponentClassification.HarrisLit.P1

open CFSG Subgroup CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.Sporadic.SmallOddCore
  CFSG.Sporadic.SmallOddCore.Native CFSG.Sporadic.Schreier

variable {n : ℕ}

@[expose] noncomputable def pairHom (n : ℕ) :
    Equiv.Perm (Fin n) × Equiv.Perm (Fin 6) →* Equiv.Perm (Fin (n + 6)) :=
  (Equiv.permCongrHom finSumFinEquiv).toMonoidHom.comp (Equiv.Perm.sumCongrHom (Fin n) (Fin 6))

theorem pairHom_injective : Function.Injective (pairHom n) :=
  (Equiv.permCongrHom finSumFinEquiv).injective.comp Equiv.Perm.sumCongrHom_injective

theorem mem_alternatingGroup_of_odd {g : Equiv.Perm (Fin 6)} (h : Odd (orderOf g)) :
    g ∈ alternatingGroup (Fin 6) := by
  rw [Equiv.Perm.mem_alternatingGroup]
  obtain ⟨k, hk⟩ := h
  have h1 : Equiv.Perm.sign g ^ orderOf g = 1 := by
    rw [← map_pow, pow_orderOf_eq_one, map_one]
  rw [hk, pow_succ, pow_mul, Int.units_sq, one_pow, one_mul] at h1
  exact h1

end CFSG.ComponentClassification.HarrisLit.P1

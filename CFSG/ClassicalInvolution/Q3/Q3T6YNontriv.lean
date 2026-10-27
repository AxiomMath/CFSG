module

public import CFSG.ClassicalInvolution.Q3.Q3T6YXSide
public import CFSG.ClassicalInvolution.Q3.Q3T6YStmt

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3T6Y

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Hat2A7
  CFSG.ClassicalInvolution.Uniform.U4 CFSG.ClassicalInvolution.Q3.Q3T6B
  CFSG.ClassicalInvolution.Q3.Q3T6X
open scoped commutatorElement

variable {F : Type} [Group F] [Finite F]

theorem diagInputNontrivOn (S : Set F) : DiagInputNontrivOn F S := by
  classical
  intro Q r u hQ _ _ hu2 hur hne I hI hrI hnt q hq hq2 hqc
  have hs : Swap Q r u := ⟨hQ, hu2, hur, fun he => hne he.symm⟩
  set K : Subgroup F := deltaStar Q u with hKdef
  have hKle : K ≤ swapFix Q u := oddClosure_le _
  have htK : ∀ k ∈ K, k * u = u * k := fun k hk =>
    Subgroup.mem_centralizer_singleton_iff.mp (hKle hk).2
  have hzK : ∀ k ∈ K, k * r = r * k := fun k hk =>
    Subgroup.mem_centralizer_singleton_iff.mp (deltaStar_le_Cz hs hk)
  rcases abstract_dichotomy' (K := K) hI hQ.mul_self hrI hnt htK hzK
      (oddClosure_le_closure_odd _) (isSubnormal_deltaStar hs) with hI1 | ⟨d, hdK, hd1, hd2, hdA⟩
  · exact (hI1 _ (diag_mem_deltaStar hs hq hqc)).1
  · have hIK : I ∈ twinClass K I := ⟨1, K.one_mem, (conjSub_one I).symm⟩
    have hq4 : q ^ 4 = 1 := hQ.pow_four_of_isPGroup hq hq2
    have hsq : q * q = 1 ∨ q * q = r := by
      have h1 : (q * q) * (q * q) = 1 := by
        rw [← hq4, show (4 : ℕ) = 2 + 2 from rfl, pow_add, pow_two]
      exact hQ.isUniqueInvolution.unique (q * q) (Q.mul_mem hq hq) h1
    rcases hsq with h1 | h1
    · have hd1' : q * (u * q * u⁻¹) = 1 := by
        rcases hQ.isUniqueInvolution.unique q hq h1 with h2 | h2
        · rw [h2]
          group
        · rw [h2]
          have : u * r * u⁻¹ = r := by rw [hur]; group
          rw [this, hQ.mul_self]
      rw [hd1']
      exact (Subgroup.normalizer (I : Set F)).one_mem
    · obtain ⟨c, hcK, k, hkK, hck⟩ := exists_conj_diag_involution hs hdK hd2 hd1 hq h1 hqc
      have hKA : K ≤ Subgroup.normalizer
          ((twinProd K I ⊓ Subgroup.centralizer ({r} : Set F) : Subgroup F) : Set F) :=
        le_normalizer_twinProd_inf_centralizer hzK
      have hkd : k * d * k⁻¹ ∈ twinProd K I ⊓ Subgroup.centralizer ({r} : Set F) :=
        (Subgroup.mem_normalizer_iff.mp (hKA hkK) d).mp hdA
      have hmem : q * (u * q * u⁻¹) ∈ twinProd K I ⊓ Subgroup.centralizer ({r} : Set F) := by
        rw [hck]
        have := (Subgroup.mem_normalizer_iff.mp (hKA hcK) (k * d * k⁻¹)).mp hkd
        simpa [mul_assoc] using this
      exact twinProd_le_normalizer hI htK hIK hmem.1

end CFSG.ClassicalInvolution.Q3.Q3T6Y

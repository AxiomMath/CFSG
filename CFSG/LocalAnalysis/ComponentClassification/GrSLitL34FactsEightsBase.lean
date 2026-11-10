
module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34FactsUnitaryLiftBase

@[expose] public section

namespace CFSG.ComponentClassification.GrSLit.L34Facts

open CFSG Subgroup CFSG.PSL3Four CFSG.PSL3Four.Native CFSG.ComponentClassification.PSL3Four
open CFSG.LieType.Multipliers CFSG.LieType.Multipliers.L34

noncomputable def ilift {E : Type*} [Group E]
    (l : Cover →* E) (d : ℕ × ℕ × ℕ × ℕ) : E :=
  l (cv (tw d.1)) * psi l (Multiplicative.ofAdd (-(d.2.1 : ZMod 4)),
    Multiplicative.ofAdd (-(d.2.2.1 : ZMod 4)))

theorem psi_sq_cancel {E : Type*} [Group E] (l : Cover →* E)
    (a b : ℕ) :
    psi l (Multiplicative.ofAdd ((2 * a : ℕ) : ZMod 4),
        Multiplicative.ofAdd ((2 * b : ℕ) : ZMod 4)) *
      (psi l (Multiplicative.ofAdd (-(a : ZMod 4)), Multiplicative.ofAdd (-(b : ZMod 4))) *
        psi l (Multiplicative.ofAdd (-(a : ZMod 4)), Multiplicative.ofAdd (-(b : ZMod 4)))) =
      1 := by
  rw [← map_mul, ← map_mul]
  convert map_one (psi l) using 2
  refine Prod.ext ?_ ?_
  · simp only [Prod.fst_mul, Prod.fst_one]
    rw [← ofAdd_add, ← ofAdd_add, ← ofAdd_zero]
    congr 1
    push_cast
    ring
  · simp only [Prod.snd_mul, Prod.snd_one]
    rw [← ofAdd_add, ← ofAdd_add, ← ofAdd_zero]
    congr 1
    push_cast
    ring

theorem map_mem_zpowers {E F : Type*} [Group E] [Group F] (f : E →* F) {a x : E}
    (hx : x ∈ zpowers a) : f x ∈ zpowers (f a) := by
  obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hx
  exact ⟨k, (map_zpow f a k).symm⟩

theorem not_mem_of_le_comap {E : Type*} [Group E] {q : E →* Equiv.Perm (Fin 42)}
    {H : Subgroup E} {K : Subgroup (Equiv.Perm (Fin 42))}
    (hH : H ≤ K.comap q) {x : E} (hx : q x ∉ K) : x ∉ H := fun hxH => hx (hH hxH)

end CFSG.ComponentClassification.GrSLit.L34Facts

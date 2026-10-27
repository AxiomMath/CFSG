module

public import CFSG.LocalAnalysis.OddStandard.Solomon75Sec4Pairing

public section

namespace CFSG.OddStandard.Solomon75

open Equiv Equiv.Perm Subgroup CFSG CFSG.GH74.GLS

section PermLevel

variable {n : ℕ}

theorem involution_apply_apply {σ : Perm (Fin n)} (hσ : σ * σ = 1) (x : Fin n) :
    σ (σ x) = x := by
  have := congrArg (fun p : Perm (Fin n) => p x) hσ
  simpa using this

end PermLevel

namespace AhatData

variable {n : ℕ} {K : Type} [Group K]

theorem CoverSetup.Induces.dblSwap_mem_map_fixSub {C : CoverSetup n K} {α : MulAut K}
    {σ : Perm (Fin n)} (h : C.Induces α σ) (hσ : σ * σ = 1) (a c : Fin n) (ha : σ a ≠ a)
    (hc : σ c ≠ c) (hca : c ≠ a) (hcb : c ≠ σ a) :
    swap a (σ a) * swap c (σ c) ∈ (fixSub α).map C.ρ := by
  have hinv := involution_apply_apply hσ
  have hab : a ≠ σ a := ha.symm
  have hcd : c ≠ σ c := hc.symm
  have had : a ≠ σ c := fun e => hcb (by rw [e, hinv])
  have hbd : σ a ≠ σ c := fun e => hca (σ.injective e).symm
  have hsign : sign (swap a (σ a) * swap c (σ c)) = 1 := by
    rw [Perm.sign_mul, Perm.sign_swap hab, Perm.sign_swap hcd]
    decide
  obtain ⟨x, hx⟩ := C.exists_ρ_eq hsign
  exact ⟨x, mem_fixSub.2 (h.apply_eq_of_dbl_swapped hab hca.symm had hcb.symm hbd hcd rfl
    (hinv a) rfl (hinv c) hx), hx⟩

end AhatData

end CFSG.OddStandard.Solomon75

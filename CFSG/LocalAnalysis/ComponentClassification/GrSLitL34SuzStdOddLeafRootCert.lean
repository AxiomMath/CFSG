module

public import Certificates.Certificate786002

public section

namespace CFSG.ComponentClassification.GrSLit.L34Sec5S

open CFSG Subgroup CFSG.Sporadic.SuzOddCore CFSG.EvenSporadicStandard.Solomon78
  CFSG.PSL3Four.Native CFSG.ComponentClassification.PSL3Four

private theorem suzRootWords_lt
    (j : ℕ) : ∀ k ∈ suzRootWords.getD j [], k < dGens.size := by
  rw [dGens_size]
  intro k hk
  have h : ∀ w ∈ suzRootWords, ∀ k ∈ w, k < 5 := by decide
  rw [List.getD_eq_getElem?_getD] at hk
  cases hh : suzRootWords[j]? with
  | none => simp [hh] at hk
  | some w => rw [hh, Option.getD_some] at hk; exact h w (List.mem_of_getElem? hh) k hk

theorem suzRootPerm_mem
    (j : ℕ) : suzRootPerm j ∈ suzD := by
  change ((suzRootWords.getD j []).map dperm).prod ∈ suzD
  refine suzD.list_prod_mem fun x hx => ?_
  obtain ⟨k, hk, rfl⟩ := List.mem_map.1 hx
  have hk' := suzRootWords_lt j k hk
  rw [dGens_size] at hk'
  exact Subgroup.subset_closure ⟨k, hk', rfl⟩

theorem suzRootPerm_comm
    {j : ℕ} (hj : j < 2) :
    suzRootPerm j * repPerm 6 = repPerm 6 * suzRootPerm j :=
  (Certificates.certificate786002.1 j hj).1

theorem suzRootPerm_pow_four
    {j : ℕ} (hj : j < 2) : suzRootPerm j ^ 4 = 1 :=
  (Certificates.certificate786002.1 j hj).2

theorem exists_mem_invE_zero_and_rho0_mem_suzD
    {τ : Equiv.Perm (Fin 1782)}
    (hτ : τ ∈ suzT ⊓ centralizer ({suzInv 0} : Set (Equiv.Perm (Fin 1782))))
    (hc : ∀ j < 2, rhoHat ⟨τ, hτ⟩ * suzRootPerm j = suzRootPerm j * rhoHat ⟨τ, hτ⟩) :
    ∃ hτE : τ ∈ invE 0, rho0 ⟨τ, hτE⟩ ∈ suzD :=
  Certificates.certificate786002.2 τ hτ hc

end CFSG.ComponentClassification.GrSLit.L34Sec5S

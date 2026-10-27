module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.Delta5Fin
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.AppCS5

public section

namespace CFSG.QuasithinUnique.AppCS2

open CFSG.QuasithinUnique CFSG.QuasithinUnique.AppC CFSG.QuasithinUnique.A5.Delta5 Equiv

theorem centralizer_Eset : ∀ g : Perm (Fin 5), (∀ σ ∈ Eset, g * σ = σ * g) → g ∈ Eset := by
  decide +kernel

theorem Eset_subset_Dset : ∀ σ ∈ Eset, σ ∈ Dset := by decide +kernel

@[expose] def sig0 : Perm (Fin 5) := swap 0 2 * swap 1 3

theorem sig0_mem : sig0 ∈ Dset := by decide +kernel

theorem sig0_conj01 : sig0 * swap 0 1 * sig0⁻¹ = swap 2 3 := by decide +kernel

theorem sig0_conj23 : sig0 * swap 2 3 * sig0⁻¹ = swap 0 1 := by decide +kernel

theorem swap23_ne_one : swap (2 : Fin 5) 3 ≠ 1 := by decide +kernel

theorem swap01_ne_one : swap (0 : Fin 5) 1 ≠ 1 := by decide +kernel

theorem swap23_ne_swap01 : swap (2 : Fin 5) 3 ≠ swap 0 1 := by decide +kernel

theorem swap01_ne_swap23 : swap (0 : Fin 5) 1 ≠ swap 2 3 := by decide +kernel

end CFSG.QuasithinUnique.AppCS2

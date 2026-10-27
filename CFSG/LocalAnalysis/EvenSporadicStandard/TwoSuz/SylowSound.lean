module

public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.Assembly.LowTwoRankDefs
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoSuz.Mat
public import CFSG.Sporadic.Suz.Simple

public section

namespace CFSG.EvenSporadicStandard.TwoSuz

open Subgroup

abbrev vm (u : GL12) : Matrix (Fin 12) (Fin 12) (ZMod 3) := (u : Matrix (Fin 12) (Fin 12) (ZMod 3))

theorem vm_mul (a b : GL12) : vm (a * b) = vm a * vm b := Units.val_mul a b

theorem vm_inj {a b : GL12} (h : vm a = vm b) : a = b := Units.ext h

section Tree

variable {gens E : Array Mt} {par : Array (ℕ × ℕ)}

variable {gU : ℕ → GL12}

abbrev genSub (gU : ℕ → GL12) (n : ℕ) : Subgroup GL12 := Subgroup.closure (gU '' Set.Iio n)

theorem mem_genSub {n k : ℕ} (hk : k < n) : gU k ∈ genSub gU n :=
  Subgroup.subset_closure ⟨k, hk, rfl⟩

end Tree

end CFSG.EvenSporadicStandard.TwoSuz

module

public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.A6FactsCore2

public section

namespace CFSG.QuasithinUnique.DoubleA3

open CFSG.QuasithinUnique.A6Facts

@[expose] def conjC (c v : List Nat) : List Nat := Core.cmul (Core.cmul c v) (Core.cmul c c)

@[expose] def tauList : List (List Nat) := Core.cpslList Core.tFrobC

@[expose] def V0l : List (List Nat) :=
  tauList.filter fun v => Core.cmul v v == Core.cid && v != Core.cid &&
    tauList.any fun c => Core.cmul (Core.cmul c c) c == Core.cid && c != Core.cid &&
      conjC c v != v && Core.cmul (conjC c v) v == Core.cmul v (conjC c v)

set_option synthInstance.maxSize 1024 in
theorem V0l_conj : ∀ c ∈ tauList, ∀ v ∈ tauList,
    (Core.cmul (Core.cmul c c) c = Core.cid ∧ c ≠ Core.cid ∧ Core.cmul v v = Core.cid ∧
      v ≠ Core.cid ∧ conjC c v ≠ v ∧ Core.cmul (conjC c v) v = Core.cmul v (conjC c v)) →
    (v ∈ V0l ∧ conjC c v ∈ V0l ∧ conjC c (conjC c v) ∈ V0l ∧ conjC c v ≠ v ∧
      conjC c (conjC c v) ≠ conjC c v ∧ conjC c (conjC c v) ≠ v) := by
  decide +kernel

set_option synthInstance.maxSize 1024 in
theorem V0l_three : ∀ a ∈ V0l, ∀ b ∈ V0l, ∀ d ∈ V0l, a ≠ b → b ≠ d → a ≠ d →
    ∀ y ∈ V0l, y = a ∨ y = b ∨ y = d := by
  decide +kernel

@[expose] def cinvC (c : List Nat) : List Nat := (List.range c.length).map fun j => c.idxOf j

@[expose] def conjb (b w : List Nat) : List Nat := Core.cmul (Core.cmul b w) (cinvC b)

theorem klein_conj_check : ∀ y ∈ Core.pslLit, (∀ w ∈ V0l, conjb y w ∈ tauList) →
    ∀ w ∈ V0l, conjb y w ∈ V0l := by
  decide +kernel

end CFSG.QuasithinUnique.DoubleA3

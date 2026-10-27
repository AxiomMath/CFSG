
module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Sporadic.J4.QTProof

@[expose] public section

namespace CFSG.QuasithinUnique.A5

open CFSG.Sporadic.J4 CFSG.Sporadic.J4.QT CFSG.Sporadic.J4.QT2

section EtaSpan

@[expose] def cmb (m0 m1 m2 m3 t : ℕ) : ℕ :=
  (if t.testBit 0 then m0 else 0) ^^^ (if t.testBit 1 then m1 else 0) ^^^
    (if t.testBit 2 then m2 else 0) ^^^ (if t.testBit 3 then m3 else 0)

theorem closure_eta_le_E (ms : List ℕ) :
    Subgroup.closure {x | x ∈ ms.map (eta uJ 11)} ≤ Eg uJ 11 := by
  rw [Subgroup.closure_le]
  intro x hx
  obtain ⟨m, -, rfl⟩ := List.mem_map.1 hx
  exact eta_mem_Eg 11 le_rfl m

end EtaSpan

end CFSG.QuasithinUnique.A5

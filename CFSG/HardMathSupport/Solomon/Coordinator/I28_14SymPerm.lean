module

public import CFSG.HardMathSupport.Solomon.Coordinator.I28_14SymOrbit
public import CFSG.HardMathSupport.Solomon.Coordinator.I28_14SymConstr

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.HardMathSupport.Solomon.Coordinator

open CFSG.Open

theorem i28_14_symPerm_fixTwo {m : ℕ} {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {A : Subgroup (Equiv.Perm (Fin m))} (hA : IsElemAbelian p A)
    (hmax : ∀ B : Subgroup (Equiv.Perm (Fin m)), IsElemAbelian p B → Nat.card B ≤ Nat.card A)
    (hA2 : p ^ 2 ≤ Nat.card A) :
    ∃ i j : Fin m, i ≠ j ∧ ∃ E ≤ A, Nat.card A ≤ p * Nat.card E ∧
      ∀ e ∈ E, e i = i ∧ e j = j := by
  obtain ⟨A₀, hA₀, hcard⟩ := i28_14_symConstr_exists hp (Fin m)
  have hbig : p ^ (Nat.card (Fin m) / p) ≤ Nat.card A := by
    rw [Nat.card_eq_fintype_card (α := Fin m), ← hcard]
    exact hmax A₀ hA₀
  obtain ⟨x, hx⟩ := i28_14_symOrbit_exists hp hp2 hA hbig hA2
  have hmul : Nat.card (MulAction.orbit A x) * Nat.card (MulAction.stabilizer A x) =
      Nat.card A := by
    rw [← Nat.card_prod, Nat.card_congr (MulAction.orbitProdStabilizerEquivGroup A x)]
  obtain ⟨a, ha⟩ : ∃ a : A, a • x ≠ x := by
    by_contra hall
    push Not at hall
    have : MulAction.orbit A x = {x} := by
      ext y
      constructor
      · rintro ⟨a, rfl⟩
        exact hall a
      · rintro rfl
        exact MulAction.mem_orbit_self _
    rw [this, Nat.card_unique] at hx
    exact hp.one_lt.ne hx
  refine ⟨x, a • x, ha.symm, (MulAction.stabilizer A x).map A.subtype,
    Subgroup.map_subtype_le _, ?_, ?_⟩
  · rw [Subgroup.card_map_of_injective A.subtype_injective, ← hmul, hx]
  · rintro _ ⟨s, hs, rfl⟩
    have hsx : s • x = x := hs
    refine ⟨hsx, ?_⟩
    change (s : Equiv.Perm (Fin m)) (a • x) = a • x
    have : s • a • x = a • s • x := by
      rw [← mul_smul, ← mul_smul, hA.1.is_comm.comm]
    rw [hsx] at this
    exact this

end CFSG.HardMathSupport.Solomon.Coordinator

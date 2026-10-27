module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.Delta5Fin

public section

namespace CFSG.QuasithinUnique.A5.Delta5

open CFSG.QuasithinUnique Equiv

@[expose] def A4set : Finset (Perm (Fin 5)) :=
  Finset.univ.filter fun σ => σ 4 = 4 ∧ Perm.sign σ = 1

theorem A4_one : (1 : Perm (Fin 5)) ∈ A4set := by decide +kernel

theorem A4_mul : ∀ a ∈ A4set, ∀ b ∈ A4set, a * b ∈ A4set := by decide +kernel

theorem A4_inv : ∀ a ∈ A4set, a⁻¹ ∈ A4set := by decide +kernel

@[expose] def A4std : Subgroup (Perm (Fin 5)) := mkSub A4set A4_one A4_mul A4_inv

theorem mem_A4std (σ : Perm (Fin 5)) : σ ∈ A4std ↔ σ ∈ A4set := Iff.rfl

theorem mem_A4set (σ : Perm (Fin 5)) : σ ∈ A4set ↔ σ 4 = 4 ∧ Perm.sign σ = 1 := by
  simp [A4set]

@[expose] def Vset : Finset (Perm (Fin 5)) :=
  {1, swap 0 1 * swap 2 3, swap 0 2 * swap 1 3, swap 0 3 * swap 1 2}

theorem V_one : (1 : Perm (Fin 5)) ∈ Vset := by decide +kernel

theorem V_mul : ∀ a ∈ Vset, ∀ b ∈ Vset, a * b ∈ Vset := by decide +kernel

theorem V_inv : ∀ a ∈ Vset, a⁻¹ ∈ Vset := by decide +kernel

@[expose] def Vstd : Subgroup (Perm (Fin 5)) := mkSub Vset V_one V_mul V_inv

theorem mem_Vstd (σ : Perm (Fin 5)) : σ ∈ Vstd ↔ σ ∈ Vset := Iff.rfl

theorem Vset_sub_A4 : ∀ σ ∈ Vset, σ ∈ A4set := by decide +kernel

theorem Vset_sub_Dset : ∀ σ ∈ Vset, σ ∈ Dset := by decide +kernel

theorem Vset_sq : ∀ σ ∈ Vset, σ * σ = 1 := by decide +kernel

theorem A4_conj_V : ∀ a ∈ A4set, ∀ v ∈ Vset, a * v * a⁻¹ ∈ Vset := by decide +kernel

theorem A4_not_V : ∀ a ∈ A4set, a ∉ Vset → a ^ 3 = 1 ∧ a ≠ 1 := by decide +kernel

theorem A4_gen3 : ∀ a ∈ A4set, ∃ τ₁ ∈ A4set, ∃ τ₂ ∈ A4set, τ₁ ^ 3 = 1 ∧ τ₂ ^ 3 = 1 ∧
    a = τ₁ * τ₂ := by decide +kernel

theorem D_eq_VE : ∀ τ ∈ Dset, ∃ v ∈ Vset, ∃ e ∈ Eset, τ = v * e := by decide +kernel

theorem D_sq_V : ∀ τ ∈ Dset, τ * τ ∈ Vset := by decide +kernel

theorem D_comm_V : ∀ τ ∈ Dset, ∀ τ' ∈ Dset, τ * τ' * τ⁻¹ * τ'⁻¹ ∈ Vset := by decide +kernel

theorem D_fix4 : ∀ τ ∈ Dset, τ 4 = 4 := Dset_le_S4

@[expose] def isE8 (v : Fin 5 → ZMod 2) : Prop := isEven v ∧ v 4 = 0

instance : DecidablePred isE8 := fun v => by unfold isE8; infer_instance

theorem E8_fixed_V : ∀ v : Fin 5 → ZMod 2, isE8 v → (∀ σ ∈ Vset, pact σ v = v) →
    v = 0 ∨ v = z0 := by decide +kernel

theorem V_faithful_E8 : ∀ σ ∈ Vset, (∀ v : Fin 5 → ZMod 2, isE8 v → pact σ v = v) → σ = 1 := by
  decide +kernel

@[expose] def g1 : Fin 5 → ZMod 2 := ![1, 1, 0, 0, 0]

@[expose] def g2 : Fin 5 → ZMod 2 := ![1, 0, 1, 0, 0]

@[expose] def g3 : Fin 5 → ZMod 2 := ![1, 0, 0, 1, 0]

theorem E8_gen : ∀ v : Fin 5 → ZMod 2, isE8 v →
    v = (if v 1 = 1 then g1 else 0) + (if v 2 = 1 then g2 else 0) + (if v 3 = 1 then g3 else 0) := by
  decide +kernel

@[expose] def w04 : Fin 5 → ZMod 2 := ![1, 0, 0, 0, 1]

theorem w04_even : isEven w04 := by decide +kernel

theorem w04_comm : ∀ c ∈ A4set, ∀ j : Fin 5, c 0 = j →
    w04 + pact c w04 = (Pi.single 0 1 : Fin 5 → ZMod 2) + Pi.single j 1 := by
  decide +kernel

theorem exists_c3 : ∀ j ∈ ({1, 2, 3} : Finset (Fin 5)), ∃ c ∈ A4set, c 0 = j := by
  decide +kernel

theorem g1_eq : (Pi.single 0 1 : Fin 5 → ZMod 2) + Pi.single 1 1 = g1 := by decide +kernel

theorem g2_eq : (Pi.single 0 1 : Fin 5 → ZMod 2) + Pi.single 2 1 = g2 := by decide +kernel

theorem g3_eq : (Pi.single 0 1 : Fin 5 → ZMod 2) + Pi.single 3 1 = g3 := by decide +kernel

theorem g1_even : isEven g1 := by decide +kernel

theorem g2_even : isEven g2 := by decide +kernel

theorem g3_even : isEven g3 := by decide +kernel

end CFSG.QuasithinUnique.A5.Delta5

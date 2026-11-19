
module

public import CFSG.LocalAnalysis.ComponentInitial.ChevSp6EpsOneSylowGroup
public import CFSG.LocalAnalysis.ComponentInitial.ChevSp6EpsOneOqDataCheck
public import Mathlib.GroupTheory.PGroup

@[expose] public section

namespace CFSG.LocalAnalysis.ComponentInitial.ChevSp6EpsOne

theorem fn_one {v : ℕ} (hv : v < 64) : fn 1 v = v := by
  rw [fn, dite_eq_left hv]
  rfl

theorem tupleOf_one : tupleOf 1 = idT := by
  simp only [tupleOf, List.range_succ, List.range_zero, List.nil_append, List.map_append,
    List.map_cons, List.map_nil]
  rw [fn_one (by norm_num), fn_one (by norm_num), fn_one (by norm_num), fn_one (by norm_num),
    fn_one (by norm_num), fn_one (by norm_num)]
  rfl

theorem mem_Gq_add {u : Bool} {σ : Equiv.Perm (Fin 64)} (hσ : σ ∈ Gq u) :
    ∀ v w, σ (fx v w) = fx (σ v) (σ w) := hσ.1

section P

theorem pCheck_spec (u : Bool) :
    (pList u).length = 128 ∧ ((pList u).map codeT).Nodup ∧ idT ∈ pList u ∧
      (∀ l ∈ pList u, validT u l = true) ∧ ∀ a ∈ pList u, ∀ b ∈ pList u, compT a b ∈ pList u := by
  have h := (sylowChecks u).1
  simp only [pCheck, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, List.contains_iff_mem,
    List.all_eq_true] at h
  obtain ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩ := h
  exact ⟨h1, h2, h3, h4, h5⟩

theorem Pcarrier_mul {u : Bool} {σ τ : Equiv.Perm (Fin 64)}
    (hσ : σ ∈ Gq u ∧ tupleOf σ ∈ pList u) (hτ : τ ∈ Gq u ∧ tupleOf τ ∈ pList u) :
    σ * τ ∈ Gq u ∧ tupleOf (σ * τ) ∈ pList u :=
  ⟨mul_mem hσ.1 hτ.1, by
    rw [tupleOf_mul (mem_Gq_add hσ.1)]
    exact (pCheck_spec u).2.2.2.2 _ hσ.2 _ hτ.2⟩

theorem Pcarrier_pow {u : Bool} {σ : Equiv.Perm (Fin 64)} (hσ : σ ∈ Gq u ∧ tupleOf σ ∈ pList u) :
    ∀ k : ℕ, σ ^ k ∈ Gq u ∧ tupleOf (σ ^ k) ∈ pList u := by
  intro k
  induction k with
  | zero => exact ⟨one_mem _, by rw [pow_zero, tupleOf_one]; exact (pCheck_spec u).2.2.1⟩
  | succ k ih => rw [pow_succ]; exact Pcarrier_mul ih hσ

def Psub (u : Bool) : Subgroup (Equiv.Perm (Fin 64)) where
  carrier := {σ | σ ∈ Gq u ∧ tupleOf σ ∈ pList u}
  mul_mem' := Pcarrier_mul
  one_mem' := ⟨one_mem _, by rw [tupleOf_one]; exact (pCheck_spec u).2.2.1⟩
  inv_mem' := by
    intro σ hσ
    have hn := orderOf_pos σ
    have e : σ⁻¹ = σ ^ (orderOf σ - 1) := by
      apply inv_eq_of_mul_eq_one_right
      rw [← pow_succ', Nat.sub_add_cancel hn, pow_orderOf_eq_one]
    rw [e]
    exact Pcarrier_pow hσ _

theorem Psub_le (u : Bool) : Psub u ≤ Gq u := fun _ h => h.1

theorem card_Psub (u : Bool) : Nat.card (Psub u) = 128 := by
  have hbij : Function.Bijective (fun σ : Psub u => (⟨tupleOf σ, σ.2.2⟩ :
      {l : List ℕ // l ∈ pList u})) := by
    refine ⟨fun σ σ' h => Subtype.ext (tupleOf_injective σ.2.1.1 σ'.2.1.1
      (congrArg Subtype.val h)), fun l => ?_⟩
    obtain ⟨σ, hσ, he⟩ := exists_of_validT ((pCheck_spec u).2.2.2.1 _ l.2)
    exact ⟨⟨σ, hσ, he ▸ l.2⟩, Subtype.ext he⟩
  rw [Nat.card_congr (Equiv.ofBijective _ hbij), ← (pCheck_spec u).1,
    ← List.toFinset_card_of_nodup (List.Nodup.of_map codeT (pCheck_spec u).2.1),
    ← Nat.card_eq_finsetCard]
  exact Nat.card_congr (Equiv.subtypeEquivRight fun l => List.mem_toFinset.symm)

theorem card_Psub_subgroupOf (u : Bool) : Nat.card ((Psub u).subgroupOf (Gq u)) = 128 := by
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (Psub_le u)).toEquiv, card_Psub]

theorem isPGroup_Psub (u : Bool) : IsPGroup 2 ((Psub u).subgroupOf (Gq u)) :=
  IsPGroup.of_card (n := 7) (by rw [card_Psub_subgroupOf]; norm_num)

end P

end CFSG.LocalAnalysis.ComponentInitial.ChevSp6EpsOne

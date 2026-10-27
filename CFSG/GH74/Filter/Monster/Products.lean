module

public import CFSG.Assembly.LowTwoRankDefs

public section

namespace CFSG.GH74.Filter.Monster

variable {H : Type*} [Group H]

theorem eq_of_prod_ofFn_eq {n : ℕ} (f₁ f₂ : Fin n → H) (i : Fin n)
    (h : ∀ j, j ≠ i → f₁ j = f₂ j) (hp : (List.ofFn f₁).prod = (List.ofFn f₂).prod) :
    f₁ i = f₂ i := by
  induction n with
  | zero => exact i.elim0
  | succ n ih =>
    rw [List.ofFn_succ, List.ofFn_succ, List.prod_cons, List.prod_cons] at hp
    cases i using Fin.cases with
    | zero =>
      have ht : (List.ofFn fun j => f₁ j.succ) = List.ofFn fun j => f₂ j.succ :=
        congrArg List.ofFn (funext fun j => h j.succ (Fin.succ_ne_zero j))
      rw [ht] at hp
      exact mul_right_cancel hp
    | succ i =>
      have h0 : f₁ 0 = f₂ 0 := h 0 (Fin.succ_ne_zero i).symm
      rw [h0] at hp
      exact ih (fun j => f₁ j.succ) (fun j => f₂ j.succ) i
        (fun j hj => h j.succ (fun e => hj (Fin.succ_injective _ e))) (mul_left_cancel hp)

theorem prod_ofFn_mul_pow {n : ℕ} (f : Fin n → H) (d : H) (a : Fin n → ℕ)
    (hf : ∀ i j, Commute (f i) (f j)) (hfd : ∀ i, Commute (f i) d) :
    (List.ofFn fun i => (f i * d) ^ a i).prod =
      (List.ofFn fun i => f i ^ a i).prod * d ^ ∑ i, a i := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.ofFn_succ, List.ofFn_succ, List.prod_cons, List.prod_cons, Fin.sum_univ_succ,
      ih (fun i => f i.succ) (fun i => a i.succ) (fun i j => hf _ _) (fun i => hfd _),
      (hfd 0).mul_pow, pow_add]
    have hT : Commute (List.ofFn fun i : Fin n => f i.succ ^ a i.succ).prod (d ^ a 0) := by
      refine Commute.pow_right (Commute.list_prod_left _ d fun x hx => ?_) _
      obtain ⟨i, rfl⟩ := List.mem_ofFn.1 hx
      exact (hfd i.succ).pow_left _
    calc f 0 ^ a 0 * d ^ a 0 *
          ((List.ofFn fun i : Fin n => f i.succ ^ a i.succ).prod * d ^ ∑ i : Fin n, a i.succ)
        = f 0 ^ a 0 * ((d ^ a 0 * (List.ofFn fun i : Fin n => f i.succ ^ a i.succ).prod) *
            d ^ ∑ i : Fin n, a i.succ) := by
          simp only [mul_assoc]
      _ = _ := by rw [← hT.eq]; simp only [mul_assoc]

theorem prod_ofFn_cons_parity {n : ℕ} (z : Fin (n + 1) → H) (hz2 : ∀ j, z j ^ 2 = 1)
    (hzc : ∀ i j, Commute (z i) (z j)) (a : Fin n → Fin 2) :
    (List.ofFn fun i : Fin n => (z i.succ * z 0) ^ (a i : ℕ)).prod =
      (List.ofFn fun j : Fin (n + 1) => z j ^
        (Fin.cons (α := fun _ => Fin 2) ⟨(∑ i, (a i : ℕ)) % 2, Nat.mod_lt _ two_pos⟩ a j :
          ℕ)).prod := by
  rw [prod_ofFn_mul_pow (fun i => z i.succ) (z 0) (fun i => (a i : ℕ)) (fun i j => hzc _ _)
    (fun i => hzc _ _), List.ofFn_succ]
  simp only [Fin.cons_zero, Fin.cons_succ, List.prod_cons]
  rw [← pow_eq_pow_mod _ (hz2 0)]
  have hT : Commute (List.ofFn fun i : Fin n => z i.succ ^ (a i : ℕ)).prod
      (z 0 ^ ∑ i, (a i : ℕ)) := by
    refine Commute.pow_right (Commute.list_prod_left _ (z 0) fun x hx => ?_) _
    obtain ⟨i, rfl⟩ := List.mem_ofFn.1 hx
    exact (hzc i.succ 0).pow_left _
  exact hT.eq

end CFSG.GH74.Filter.Monster

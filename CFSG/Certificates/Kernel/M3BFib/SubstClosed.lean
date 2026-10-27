module

public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.MonsterThreeBBridge
public import Mathlib.GroupTheory.Nilpotent
public import Mathlib.Tactic.Basify

public section

namespace CFSG.KC.M3BF

open CFSG.HardMathSupport.Timmesfeld.SporadicBalance.ThreeBNF

variable {n : ℕ} (B : Fin n → Fin n → ZMod 3)

theorem betaC_add_left (a a' b : Fin n → ZMod 3) :
    betaC n B (a + a') b = betaC n B a b + betaC n B a' b := by
  simp only [betaC, ← Finset.sum_add_distrib, Pi.add_apply]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  split_ifs <;> ring

theorem betaC_add_right (a b b' : Fin n → ZMod 3) :
    betaC n B a (b + b') = betaC n B a b + betaC n B a b' := by
  simp only [betaC, ← Finset.sum_add_distrib, Pi.add_apply]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  split_ifs <;> ring

theorem betaC_smul_left (c : ZMod 3) (a b : Fin n → ZMod 3) :
    betaC n B (c • a) b = c * betaC n B a b := by
  simp only [betaC, Finset.mul_sum, Pi.smul_apply, smul_eq_mul]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  split_ifs <;> ring

theorem betaC_smul_right (c : ZMod 3) (a b : Fin n → ZMod 3) :
    betaC n B a (c • b) = c * betaC n B a b := by
  simp only [betaC, Finset.mul_sum, Pi.smul_apply, smul_eq_mul]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  split_ifs <;> ring

theorem betaC_zero_left (b : Fin n → ZMod 3) : betaC n B 0 b = 0 := by
  simp [betaC]

theorem betaC_zero_right (a : Fin n → ZMod 3) : betaC n B a 0 = 0 := by
  simp [betaC]

theorem betaC_sum_right {ι : Type*} (s : Finset ι) (a : Fin n → ZMod 3) (f : ι → Fin n → ZMod 3) :
    betaC n B a (∑ i ∈ s, f i) = ∑ i ∈ s, betaC n B a (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [betaC_zero_right]
  | insert x s hx ih => rw [Finset.sum_insert hx, Finset.sum_insert hx, betaC_add_right, ih]

theorem emul_eq (x y : Elt n) :
    emul B x y = (x.1 + y.1, x.2 + y.2 + betaC n B x.1 y.1) := by
  rw [emul, betaN3_eq]

theorem epow_eq (x : Elt n) : ∀ k : ℕ,
    epow B x k = ((k : ZMod 3) • x.1, (k : ZMod 3) * x.2 + (k.choose 2 : ℕ) * betaC n B x.1 x.1)
  | 0 => by
    rw [epow, eone]
    simp
  | k + 1 => by
    rw [epow, epow_eq x k, emul_eq, betaC_smul_left, Nat.choose_succ_succ', Nat.choose_one_right]
    refine Prod.ext ?_ ?_
    · simp only [Nat.cast_succ, add_smul, one_smul]
    · push_cast
      ring

@[expose] noncomputable def tri : List (Elt n) → ZMod 3
  | [] => 0
  | y :: l => betaC n B y.1 (l.map Prod.fst).sum + tri l

theorem foldl_emul : ∀ (l : List (Elt n)) (a : Elt n),
    l.foldl (emul B) a = (a.1 + (l.map Prod.fst).sum,
      a.2 + (l.map Prod.snd).sum + betaC n B a.1 (l.map Prod.fst).sum + tri B l)
  | [], a => by simp [tri, betaC_zero_right]
  | y :: l, a => by
    rw [List.foldl_cons, foldl_emul l, emul_eq]
    simp only [List.map_cons, List.sum_cons, tri, betaC_add_left, betaC_add_right]
    refine Prod.ext ?_ ?_
    · dsimp only
      abel
    · dsimp only
      ring

theorem tri_ofFn : ∀ (m : ℕ) (g : Fin m → Elt n),
    tri B (List.ofFn g) =
      ∑ j : Fin m, ∑ l : Fin m, if j < l then betaC n B (g j).1 (g l).1 else 0
  | 0, g => by simp [tri]
  | m + 1, g => by
    rw [List.ofFn_succ, tri, tri_ofFn m, Fin.sum_univ_succ, Fin.sum_univ_succ (f := fun l =>
      if (0 : Fin (m + 1)) < l then betaC n B (g 0).1 (g l).1 else 0)]
    simp only [lt_self_iff_false, ite_false, zero_add, Fin.succ_pos, ite_true, List.map_ofFn,
      List.sum_ofFn, Function.comp_def, Fin.succ_lt_succ_iff, Fin.not_lt_zero, betaC_sum_right,
      Fin.sum_univ_succ (n := m)]

@[expose] def ch2Z (a : ZMod 3) : ZMod 3 := ((a.val.choose 2 : ℕ) : ZMod 3)

theorem subst_eq (D : ActD n) (x : Elt n) :
    subst B D x = (∑ j, x.1 j • (D.1 j).1,
      ∑ j, (x.1 j * (D.1 j).2 + ch2Z (x.1 j) * betaC n B (D.1 j).1 (D.1 j).1) +
        ∑ j, ∑ l, (if j < l then x.1 j * x.1 l * betaC n B (D.1 j).1 (D.1 l).1 else 0) +
        D.2 * x.2) := by
  rw [subst, eprod, foldl_emul, emul_eq, tri_ofFn]
  simp only [List.map_ofFn, List.sum_ofFn, Function.comp_def, epow_eq, ZMod.natCast_zmod_val,
    eone, betaC_zero_left, betaC_zero_right, betaC_smul_left, betaC_smul_right, zero_add, add_zero]
  refine Prod.ext rfl ?_
  dsimp only
  congr 2
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun l _ => ?_
  split_ifs <;> ring

end CFSG.KC.M3BF

end

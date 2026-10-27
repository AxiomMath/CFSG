module

public import Certificates.Data.FoxCodes
public import Mathlib.Algebra.Group.Subgroup.Lattice
import Mathlib.Tactic.Abel
public import Mathlib.Algebra.BigOperators.Group.List.Defs
public import Mathlib.Data.Finset.Attr

public section

namespace CFSG.CGT.Foote82.FoxH1

variable {V : Type*} [AddCommGroup V]

structure IsVecCode (N : ℕ) (cvec : ℕ → V) (vcode : V → ℕ) : Prop where
  code_lt : ∀ v, vcode v < N
  vec_code : ∀ v, cvec (vcode v) = v
  code_vec : ∀ n < N, vcode (cvec n) = n
  vec_xor : ∀ n m, cvec (n ^^^ m) = cvec n + cvec m
  xor_lt : ∀ n < N, ∀ m < N, n ^^^ m < N

@[expose] def IsActArr {X : Type*} (act : X → V → V) (N : ℕ) (cvec : ℕ → V) (x : X)
    (t : Array ℕ) : Prop :=
  ∀ k < N, t[k]! < N ∧ act x (cvec k) = cvec t[k]!

variable {N : ℕ} {cvec : ℕ → V} {vcode : V → ℕ}

theorem IsVecCode.zero_lt (hc : IsVecCode N cvec vcode) : 0 < N :=
  lt_of_le_of_lt (Nat.zero_le _) (hc.code_lt 0)

theorem IsVecCode.vec_zero (hc : IsVecCode N cvec vcode) : cvec 0 = 0 := by
  have h := hc.vec_xor 0 0
  rw [Nat.xor_self] at h
  exact left_eq_add.mp h

theorem IsVecCode.add_self (hc : IsVecCode N cvec vcode) (v : V) : v + v = 0 := by
  have h := hc.vec_xor (vcode v) (vcode v)
  rw [Nat.xor_self, hc.vec_code, hc.vec_zero] at h
  exact h.symm

theorem IsVecCode.add_eq_sub (hc : IsVecCode N cvec vcode) (u v : V) : u + v = u - v := by
  rw [sub_eq_add_neg, neg_eq_of_add_eq_zero_right (hc.add_self v)]

section Fox

variable {X : Type*} [Group X] {act : X → V → V}

theorem cocycle_one (hone : ∀ v, act 1 v = v) {F : X → V}
    (hF : ∀ x y, F (x * y) = F x + act x (F y)) : F 1 = 0 := by
  have h := hF 1 1
  rw [mul_one, hone] at h
  exact left_eq_add.mp h

theorem foxW_spec (hone : ∀ v, act 1 v = v) {F : X → V}
    (hF : ∀ x y, F (x * y) = F x + act x (F y)) (hc : IsVecCode N cvec vcode) {s : ℕ → X}
    {gs : Array (Array ℕ)} {vals : Array ℕ} :
    ∀ w : List ℕ, (∀ i ∈ w, IsActArr act N cvec (s i) gs[i]! ∧ vals[i]! = vcode (F (s i))) →
      foxW gs vals w < N ∧ F (w.map s).prod = cvec (foxW gs vals w)
  | [], _ => by
    refine ⟨hc.zero_lt, ?_⟩
    rw [List.map_nil, List.prod_nil, foxW, hc.vec_zero]
    exact cocycle_one hone hF
  | i :: w, hw => by
    obtain ⟨hlt, heq⟩ := foxW_spec hone hF hc w fun j hj => hw j (List.mem_cons_of_mem i hj)
    obtain ⟨hact, hval⟩ := hw i List.mem_cons_self
    obtain ⟨hlt', hact'⟩ := hact _ hlt
    refine ⟨?_, ?_⟩
    · rw [foxW]
      exact hc.xor_lt _ (by rw [hval]; exact hc.code_lt _) _ hlt'
    · rw [List.map_cons, List.prod_cons, hF, heq, hact', foxW, hc.vec_xor, hval, hc.vec_code]

theorem coboundary_of_foxCheck2 (hadd : ∀ x u v, act x (u + v) = act x u + act x v)
    (hmul : ∀ x y v, act (x * y) v = act x (act y v)) (hone : ∀ v, act 1 v = v)
    (hc : IsVecCode N cvec vcode) {s : ℕ → X} {gs : Array (Array ℕ)}
    (hgs : ∀ i < 2, IsActArr act N cvec (s i) gs[i]!)
    (hgen : Subgroup.closure (s '' Set.Iio 2) = ⊤) {rels : List (List ℕ)}
    (hrel : ∀ w ∈ rels, (∀ i ∈ w, i < 2) ∧ (w.map s).prod = 1)
    (hchk : foxCheck2 N gs rels = true) :
    ∀ F : X → V, (∀ x y, F (x * y) = F x + act x (F y)) → ∃ m : V, ∀ x, F x = act x m - m := by
  intro F hF
  have hF1 := cocycle_one hone hF
  have hsub : ∀ x u v, act x (u - v) = act x u - act x v := fun x u v =>
    eq_sub_of_add_eq (by rw [← hadd, sub_add_cancel])
  have hvals : ∀ i < 2, (#[vcode (F (s 0)), vcode (F (s 1))] : Array ℕ)[i]! = vcode (F (s i)) := by
    intro i hi
    rcases (by omega : i = 0 ∨ i = 1) with rfl | rfl <;> rfl
  have hfox : (rels.all fun w => foxW gs #[vcode (F (s 0)), vcode (F (s 1))] w == 0) = true := by
    rw [List.all_eq_true]
    intro w hw
    obtain ⟨hlet, hprod⟩ := hrel w hw
    obtain ⟨hlt, heq⟩ := foxW_spec hone hF hc w fun i hi =>
      ⟨hgs i (hlet i hi), hvals i (hlet i hi)⟩
    rw [hprod, hF1, ← hc.vec_zero] at heq
    rw [beq_iff_eq, ← hc.code_vec _ hlt, ← heq, hc.code_vec 0 hc.zero_lt]
  have hc' := List.all_eq_true.mp (List.all_eq_true.mp hchk (vcode (F (s 0)))
    (List.mem_range.mpr (hc.code_lt _))) (vcode (F (s 1))) (List.mem_range.mpr (hc.code_lt _))
  rw [hfox, Bool.not_true, Bool.false_or, List.any_eq_true] at hc'
  obtain ⟨c, hcN, hcc⟩ := hc'
  rw [Bool.and_eq_true, beq_iff_eq, beq_iff_eq] at hcc
  obtain ⟨h0, h1⟩ := hcc
  have hcN' := List.mem_range.mp hcN
  refine ⟨cvec c, fun x => ?_⟩
  have hgenF : ∀ i < 2, F (s i) = act (s i) (cvec c) - cvec c := by
    intro i hi
    have hi' : vcode (F (s i)) = (gs[i]!)[c]! ^^^ c := by
      rcases (by omega : i = 0 ∨ i = 1) with rfl | rfl
      · exact h0
      · exact h1
    rw [← hc.vec_code (F (s i)), hi', hc.vec_xor, ← ((hgs i hi) c hcN').2, hc.add_eq_sub]
  have hP : ∀ y ∈ Subgroup.closure (s '' Set.Iio 2), F y = act y (cvec c) - cvec c := by
    intro y hy
    induction hy using Subgroup.closure_induction with
    | mem y hy =>
      obtain ⟨i, hi, rfl⟩ := hy
      exact hgenF i hi
    | one => rw [hF1, hone, sub_self]
    | mul y z _ _ hy hz =>
      rw [hF, hy, hz, hsub, hmul]
      abel
    | inv y _ hy =>
      have hinv : ∀ v, act y⁻¹ (act y v) = v := fun v => by rw [← hmul, inv_mul_cancel, hone]
      have h := hF y y⁻¹
      rw [mul_inv_cancel, hF1, hy] at h
      have h' : act y (F y⁻¹) = cvec c - act y (cvec c) := by
        rw [eq_neg_of_add_eq_zero_right h.symm, neg_sub]
      rw [← hinv (F y⁻¹), h', hsub, hinv]
  exact hP x (hgen ▸ Subgroup.mem_top x)

end Fox

end CFSG.CGT.Foote82.FoxH1

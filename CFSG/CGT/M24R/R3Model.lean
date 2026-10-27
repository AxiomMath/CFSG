module

public import CFSG.CGT.M24R.R3Inputs
public import CFSG.Sporadic.Th.TableSpec
public import CFSG.Certificates.CosetTablePresented

public section

namespace CFSG.CGT.M24R.R3

open CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.CosetTable

@[expose] def tabFun (T : Table) (i : Fin 24) : Fin 24 := Fin.ofNat 24 (ap T i.val)

theorem genTab_left : ∀ k : Fin 10, ∀ i : Fin 24,
    tabFun (genTabInv k) (tabFun (genTab k) i) = i := by
  decide +kernel

theorem genTab_right : ∀ k : Fin 10, ∀ i : Fin 24,
    tabFun (genTab k) (tabFun (genTabInv k) i) = i := by
  decide +kernel

theorem genTab_lt : ∀ k : Fin 10, ∀ i < 24, ap (genTab k) i < 24 ∧ ap (genTabInv k) i < 24 := by
  decide +kernel

@[expose] def n0Perm (k : Fin 10) : Equiv.Perm (Fin 24) where
  toFun := tabFun (genTab k)
  invFun := tabFun (genTabInv k)
  left_inv := genTab_left k
  right_inv := genTab_right k

theorem rep_genTab (k : Fin 10) : Rep 24 (genTab k) (n0Perm k) := by
  intro i hi
  rw [idx_of_lt _ hi, Equiv.Perm.smul_def]
  show ap (genTab k) i = (Fin.ofNat 24 (ap (genTab k) i)).val
  rw [Fin.val_ofNat, Nat.mod_eq_of_lt (genTab_lt k i hi).1]

theorem rep_genTabInv (k : Fin 10) : Rep 24 (genTabInv k) (n0Perm k)⁻¹ := by
  intro i hi
  rw [idx_of_lt _ hi, Equiv.Perm.smul_def]
  show ap (genTabInv k) i = (Fin.ofNat 24 (ap (genTabInv k) i)).val
  rw [Fin.val_ofNat, Nat.mod_eq_of_lt (genTab_lt k i hi).2]

theorem genTab_of_ge {k : ℕ} (hk : 10 ≤ k) : genTab k = idT 24 := by
  obtain ⟨n, rfl⟩ : ∃ n, k = n + 10 := ⟨k - 10, by omega⟩
  rfl

theorem genTabInv_of_ge {k : ℕ} (hk : 10 ≤ k) : genTabInv k = idT 24 := by
  obtain ⟨n, rfl⟩ : ∃ n, k = n + 10 := ⟨k - 10, by omega⟩
  rfl

@[expose] def letPerm (z : ℤ) : Equiv.Perm (Fin 24) :=
  if 0 < z then (if h : z.toNat - 1 < 10 then n0Perm ⟨z.toNat - 1, h⟩ else 1)
  else (if h : (-z).toNat - 1 < 10 then (n0Perm ⟨(-z).toNat - 1, h⟩)⁻¹ else 1)

theorem rep_letTab (z : ℤ) : Rep 24 (letTab z) (letPerm z) := by
  unfold letTab letPerm
  split_ifs with h1 h2 h2
  · exact rep_genTab ⟨_, h2⟩
  · rw [genTab_of_ge (by omega)]
    exact Rep.idT (by norm_num)
  · exact rep_genTabInv ⟨_, h2⟩
  · rw [genTabInv_of_ge (by omega)]
    exact Rep.idT (by norm_num)

theorem letPerm_letZ (l : Fin 10 × Bool) :
    letPerm (letZ l) = if l.2 then n0Perm l.1 else (n0Perm l.1)⁻¹ := by
  obtain ⟨i, b⟩ := l
  have hi := i.isLt
  cases b
  · have h0 : ¬ (0 : ℤ) < -((i.val : ℤ) + 1) := by omega
    have h1 : (-(-((i.val : ℤ) + 1))).toNat - 1 = i.val := by omega
    simp only [letPerm, letZ, Bool.false_eq_true, ite_false, h0]
    rw [dite_eq_left (by omega)]
    congr 2
  · have h0 : (0 : ℤ) < (i.val : ℤ) + 1 := by omega
    have h1 : ((i.val : ℤ) + 1).toNat - 1 = i.val := by omega
    simp only [letPerm, letZ, ite_true, h0]
    rw [dite_eq_left (by omega)]
    congr 1

theorem wordG_letPerm (w : N0Word) :
    wordG letPerm (w.map letZ) = FreeGroup.lift n0Perm (FreeGroup.mk w) := by
  induction w with
  | nil => rfl
  | cons l w ih =>
    simp only [wordG, List.map_cons, List.prod_cons] at ih ⊢
    rw [ih, show FreeGroup.mk (l :: w) = FreeGroup.mk [l] * FreeGroup.mk w from rfl, map_mul,
      letPerm_letZ]
    obtain ⟨i, b⟩ := l
    cases b
    · rw [show FreeGroup.mk [(i, false)] = (FreeGroup.of i)⁻¹ from rfl, map_inv,
        FreeGroup.lift_apply_of]
      rfl
    · rw [show FreeGroup.mk [(i, true)] = FreeGroup.of i from rfl, FreeGroup.lift_apply_of]
      rfl

theorem rep_wTab (w : N0Word) : Rep 24 (wTab w) (FreeGroup.lift n0Perm (FreeGroup.mk w)) := by
  rw [← wordG_letPerm]
  exact Rep.wordT (by norm_num) _ fun z _ => rep_letTab z

theorem perm_eq_of_tabEq {T T' : Table} {σ τ : Equiv.Perm (Fin 24)} (hT : Rep 24 T σ)
    (hT' : Rep 24 T' τ) (h : tabEq T T' = true) : σ = τ := by
  refine Equiv.ext fun i => Fin.ext ?_
  have e := allIn_eq_true.1 h i.val (Nat.zero_le _) i.isLt
  rw [beq_iff_eq, hT i.val i.isLt, hT' i.val i.isLt, idx_of_lt σ i.isLt,
    idx_of_lt τ i.isLt] at e
  exact e

theorem tabEq_of_perm_eq {T T' : Table} {σ τ : Equiv.Perm (Fin 24)} (hT : Rep 24 T σ)
    (hT' : Rep 24 T' τ) (h : σ = τ) : tabEq T T' = true := by
  refine allIn_eq_true.2 fun i _ hi => ?_
  rw [beq_iff_eq, hT i hi, hT' i hi, h]

abbrev N0 : Type := PG 10 relsN8Ten

@[expose] def n0 (w : N0Word) : N0 := PresentedGroup.mk _ (FreeGroup.mk w)

theorem n0_nil : n0 [] = 1 := map_one _

theorem n0_append (w w' : N0Word) : n0 (w ++ w') = n0 w * n0 w' := by
  rw [n0, n0, n0, ← map_mul, FreeGroup.mul_mk]

theorem n0_inv10 (w : N0Word) : n0 (inv10 w) = (n0 w)⁻¹ := by
  rw [n0, n0, ← map_inv, FreeGroup.inv_mk, FreeGroup.invRev, inv10, List.map_reverse]

theorem lift_n0Perm_rel (h : relCheck = true) :
    ∀ r ∈ {r : FreeGroup (Fin 10) | r ∈ relsN8Ten.map FreeGroup.mk},
      FreeGroup.lift n0Perm r = 1 := by
  intro r hr
  simp only [Set.mem_ofPred_eq, List.mem_map] at hr
  obtain ⟨w, hw, rfl⟩ := hr
  have hc : nEq w [] = true := by
    simp only [relCheck, List.all_eq_true] at h
    exact h w hw
  exact perm_eq_of_tabEq (rep_wTab w) (rep_wTab []) hc

@[expose] def rho (h : relCheck = true) : N0 →* Equiv.Perm (Fin 24) :=
  PresentedGroup.toGroup (lift_n0Perm_rel h)

theorem rho_n0 (h : relCheck = true) (w : N0Word) :
    rho h (n0 w) = FreeGroup.lift n0Perm (FreeGroup.mk w) := rfl

theorem rho_eq_of_nEq (h : relCheck = true) {w w' : N0Word} (hw : nEq w w' = true) :
    rho h (n0 w) = rho h (n0 w') := by
  rw [rho_n0, rho_n0]
  exact perm_eq_of_tabEq (rep_wTab w) (rep_wTab w') hw

theorem n0_ne_of_nEq (h : relCheck = true) {w w' : N0Word} (hw : nEq w w' = false) :
    n0 w ≠ n0 w' := by
  intro e
  have := tabEq_of_perm_eq (rep_wTab w) (rep_wTab w')
    (by rw [← rho_n0 h, ← rho_n0 h, e])
  rw [nEq] at hw
  rw [hw] at this
  exact Bool.false_ne_true this

end CFSG.CGT.M24R.R3

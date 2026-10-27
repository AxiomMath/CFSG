module

public import CFSG.Certificates.Kernel.Misc.Ree2Det
public import CFSG.Certificates.Kernel.Misc.Ree2Bind

public section

namespace CFSG.KC.Misc.Ree2

open CFSG.KC.Loop CFSG.Walter.Ree.Bombieri

theorem evalList_eq (q1 hf ZT : ℕ) (ρ α : ℕ → ℕ) :
    ∀ l : List PE, evalList q1 hf ZT ρ α l = l.map (evalL q1 hf ZT ρ α)
  | [] => rfl
  | e :: l => by
    change evalL q1 hf ZT ρ α e :: evalList q1 hf ZT ρ α l = _
    rw [evalList_eq q1 hf ZT ρ α l]
    rfl

theorem varsL_eq (q1 z0 z1 z2 z3 y i : ℕ) : varsL q1 z0 z1 z2 z3 y i =
    if i = 0 then z0 else if i = 1 then z1 else if i = 2 then z2 else if i = 3 then z3 else
      if i = 4 then y else q1 := by
  unfold varsL
  simp only [nIf_eq, nbeq, decide_eq_true_eq]

theorem coefAt_eq (q1 : ℕ) (cs : List ℕ) (s : ℕ) :
    coefAt q1 cs s = if s = 0 then q1 else cs.getD (s - 1) q1 := by
  unfold coefAt
  simp only [nIf_eq, nbeq, decide_eq_true_eq, nthL_eq]
  rfl

theorem getD_of_lt {α : Type*} {l : List α} {n : ℕ} (d : α) (h : n < l.length) :
    l.getD n d = l[n] := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h]
  rfl

theorem getD_map_lt {α β : Type*} (f : α → β) {l : List α} {n : ℕ} (d : β) (h : n < l.length) :
    (l.map f).getD n d = f l[n] := by
  rw [getD_of_lt d (by simpa using h), List.getElem_map]

theorem getD_ge {α : Type*} {l : List α} {n : ℕ} (d : α) (h : l.length ≤ n) : l.getD n d = d := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none h]
  rfl

theorem getD_le {l : List ℕ} {q1 d : ℕ} (hl : ∀ x ∈ l, x ≤ q1) (hd : d ≤ q1) (n : ℕ) :
    l.getD n d ≤ q1 := by
  rw [List.getD_eq_getElem?_getD]
  cases h : l[n]? with
  | none => exact hd
  | some a => exact hl a (List.mem_of_getElem? h)

@[expose] def atomsLt (n : ℕ) : PE → Bool
  | PE.var _ => true
  | PE.atom k => decide (k < n)
  | PE.const _ => true
  | PE.add a b => atomsLt n a && atomsLt n b
  | PE.sub a b => atomsLt n a && atomsLt n b
  | PE.mul a b => atomsLt n a && atomsLt n b
  | PE.pow a _ => atomsLt n a
  | PE.neg a => atomsLt n a

theorem eval_congr_atoms {R : Type*} [CommRing R] (ρ : ℕ → R) {α β : ℕ → R} {n : ℕ}
    (h : ∀ k < n, α k = β k) : ∀ e : PE, atomsLt n e = true → PE.eval ρ α e = PE.eval ρ β e
  | PE.var _, _ => rfl
  | PE.atom k, he => by
    simp only [atomsLt, decide_eq_true_eq] at he
    exact h k he
  | PE.const _, _ => rfl
  | PE.add a b, he => by
    simp only [atomsLt, Bool.and_eq_true] at he
    change PE.eval ρ α a + PE.eval ρ α b = PE.eval ρ β a + PE.eval ρ β b
    rw [eval_congr_atoms ρ h a he.1, eval_congr_atoms ρ h b he.2]
  | PE.sub a b, he => by
    simp only [atomsLt, Bool.and_eq_true] at he
    change PE.eval ρ α a - PE.eval ρ α b = PE.eval ρ β a - PE.eval ρ β b
    rw [eval_congr_atoms ρ h a he.1, eval_congr_atoms ρ h b he.2]
  | PE.mul a b, he => by
    simp only [atomsLt, Bool.and_eq_true] at he
    change PE.eval ρ α a * PE.eval ρ α b = PE.eval ρ β a * PE.eval ρ β b
    rw [eval_congr_atoms ρ h a he.1, eval_congr_atoms ρ h b he.2]
  | PE.pow a k, he => by
    simp only [atomsLt] at he
    change PE.eval ρ α a ^ k = PE.eval ρ β a ^ k
    rw [eval_congr_atoms ρ h a he]
  | PE.neg a, he => by
    simp only [atomsLt] at he
    change -PE.eval ρ α a = -PE.eval ρ β a
    rw [eval_congr_atoms ρ h a he]

theorem coefL_atoms : coefL.all (atomsLt 7) = true := by decide

theorem shapeEnt_eq (i j : ℕ) : shapeEnt i j =
    if Nat.land (Nat.shiftRight shapeL (Nat.mul (nat_lit 5) (12 * i + j))) (nat_lit 31) = 0 then 0
    else coefL.getD (Nat.land (Nat.shiftRight shapeL (Nat.mul (nat_lit 5) (12 * i + j)))
      (nat_lit 31) - 1) 0 := by
  have h : Nat.land (Nat.shiftRight shapeL (Nat.mul (nat_lit 5) (12 * i + j))) (nat_lit 31) =
      shapeL >>> (5 * (12 * i + j)) % 32 := by
    change Nat.land (Nat.shiftRight shapeL (5 * (12 * i + j))) (2 ^ 5 - 1) = _
    rw [fld_eq_mod, Nat.shiftRight_eq_div_pow]
    norm_num
  rw [h]
  rfl

section

variable {K : Type*} [Field K] [CharP K 3] {q1 hf ZT : ℕ} {γ : K}

theorem LogEnv.detL_spec (E : LogEnv q1 hf ZT γ) (hq : q1 < 65535) {z0 z1 z2 z3 y : ℕ}
    (h0 : z0 ≤ q1) (h1 : z1 ≤ q1) (h2 : z2 ≤ q1) (h3 : z3 ≤ q1) (hy : y ≤ q1)
    (h : detL q1 hf ZT shapeL atomL coefL z0 z1 z2 z3 y ≠ q1 + 1) :
    detL q1 hf ZT shapeL atomL coefL z0 z1 z2 z3 y ≤ q1 ∧
      phi q1 γ (detL q1 hf ZT shapeL atomL coefL z0 z1 z2 z3 y) =
        (Elim.matOf (Elim.ptVars (phi q1 γ z0) (phi q1 γ z1) (phi q1 γ z2) (phi q1 γ z3)
          (phi q1 γ y))).det := by
  set ρ := varsL q1 z0 z1 z2 z3 y with hρ
  have hρl : ∀ i, ρ i ≤ q1 := by
    intro i
    rw [hρ, varsL_eq]
    split_ifs <;> first | assumption | exact le_rfl
  have hρe : phi q1 γ ∘ ρ =
      Elim.ptVars (phi q1 γ z0) (phi q1 γ z1) (phi q1 γ z2) (phi q1 γ z3) (phi q1 γ y) := by
    funext i
    rcases i with _ | _ | _ | _ | _ | i <;> simp [hρ, varsL_eq, Elim.ptVars, phi_q1]
  set ρ' := Elim.ptVars (phi q1 γ z0) (phi q1 γ z1) (phi q1 γ z2) (phi q1 γ z3) (phi q1 γ y)
  set al := atomL.map (evalL q1 hf ZT ρ (fun _ => q1)) with hal
  have hall : ∀ x ∈ al, x ≤ q1 := by
    intro x hx
    obtain ⟨e, -, rfl⟩ := List.mem_map.mp hx
    exact (E.evalL_spec hρl (fun _ => le_rfl) e).1
  set A := packL al with hA
  have hAk : ∀ k, getP A k = al.getD k 0 :=
    getP_packL fun x hx => (hall x hx).trans_lt (by omega)
  have hAl : ∀ k, getP A k ≤ q1 := fun k => by
    rw [hAk]; exact getD_le hall (Nat.zero_le _) k
  have hAe : ∀ k < 7, phi q1 γ (getP A k) = Elim.atomsOf ρ' k := by
    intro k hk
    have hlen : k < atomL.length := hk
    rw [hAk, hal, getD_map_lt _ _ hlen, ← getD_of_lt 0 hlen, atomL_getD k hk,
      (E.evalL_spec hρl (fun _ => le_rfl) _).2, hρe]
    unfold Elim.atomsOf
    congr 1
    funext _
    exact phi_q1
  set cs := coefL.map (evalL q1 hf ZT ρ (fun k => getP A k)) with hcs
  have hcsl : ∀ x ∈ cs, x ≤ q1 := by
    intro x hx
    obtain ⟨e, -, rfl⟩ := List.mem_map.mp hx
    exact (E.evalL_spec hρl hAl e).1
  have hcse : ∀ n, phi q1 γ (cs.getD n q1) = PE.eval ρ' (Elim.atomsOf ρ') (coefL.getD n 0) := by
    intro n
    rw [hcs]
    by_cases hn : n < coefL.length
    · rw [getD_map_lt _ _ hn, (E.evalL_spec hρl hAl _).2, hρe, getD_of_lt 0 hn]
      refine eval_congr_atoms ρ' (fun k hk => hAe k hk) _ ?_
      have := coefL_atoms
      rw [List.all_eq_true] at this
      exact this _ (List.getElem_mem hn)
    · rw [getD_ge _ (by simpa using hn), phi_q1, getD_ge _ (by omega)]
      exact (PE.eval_zero _ _).symm
  set v : ℕ → ℕ := fun p =>
    coefAt q1 cs (Nat.land (Nat.shiftRight shapeL (Nat.mul (nat_lit 5) p)) (nat_lit 31)) with hv
  have hvl : ∀ p, v p ≤ q1 := by
    intro p
    simp only [hv, coefAt_eq]
    split_ifs
    · exact le_rfl
    · exact getD_le hcsl le_rfl _
  set M := buildM q1 shapeL cs with hM
  have hMv : ∀ i j, i < 12 → j < 12 → entM M i j = v (12 * i + j) := by
    intro i j hi hj
    exact fld_loopN_or (w := 16) (by norm_num) (fun p => (hvl p).trans_lt (by omega))
      (Nat.zero_le _) (by change 12 * i + j < 0 + 144; omega)
  have hBd : BdM q1 M := fun i j hi hj => by rw [hMv i j hi hj]; exact hvl _
  have hMat : matV q1 γ M = Elim.matOf ρ' := by
    ext i j
    simp only [matV, Matrix.of_apply, Elim.matOf]
    rw [hMv i j i.2 j.2, ent_eq, shapeEnt_eq]
    simp only [hv, coefAt_eq]
    split_ifs
    · rw [phi_q1, PE.eval_zero]
    · exact hcse _
  unfold detL
  rw [sN, evalList_eq, evalList_eq, ← hal, ← hA, ← hcs, ← hM]
  rw [← hMat]
  unfold detL at h
  rw [sN, evalList_eq, evalList_eq, ← hal, ← hA, ← hcs, ← hM] at h
  exact E.detM_spec hq hBd h

end

end CFSG.KC.Misc.Ree2

end

module

public import Certificates.Data.Kernel.AlphaGrpK
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.AlphaGrpDefs
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.AlphaWordDefs
public import CFSG.Certificates.Kernel.OpsMcertNSound

public section

namespace CFSG.AGLEmbedding.R3

open CFSG.SectionRank.Native CFSG.RankThree.Asc83Table.Native CFSG.KC.OpsMN CFSG.KC.OpsHom

private theorem fsum_eq_sum (N : Nat) (f : Fin N → Int) : fsum N f = ∑ i, f i :=
  (Fin.sum_univ_def f).symm

private theorem keys_lt_of_incK : ∀ (x : Nat × Nat) (l : List (Nat × Nat)),
    incK (x :: l) = true → ∀ e ∈ l, x.1 < e.1
  | _, [], _, e, he => by simp at he
  | x, y :: l, h, e, he => by
    simp only [incK, Bool.and_eq_true, decide_eq_true_eq] at h
    rcases List.mem_cons.1 he with rfl | he
    · exact h.1
    · exact h.1.trans (keys_lt_of_incK y l h.2 e he)

private theorem incK_tail : ∀ (x : Nat × Nat) (l : List (Nat × Nat)), incK (x :: l) = true →
    incK l = true
  | _, [], _ => rfl
  | _, _ :: _, h => by
    simp only [incK, Bool.and_eq_true] at h
    exact h.2

theorem nodup_of_incK : ∀ l : List (Nat × Nat), incK l = true → (l.map Prod.fst).Nodup
  | [], _ => List.nodup_nil
  | x :: l, h => by
    rw [List.map_cons, List.nodup_cons]
    refine ⟨fun hx => ?_, nodup_of_incK l (incK_tail x l h)⟩
    obtain ⟨e, he, hk⟩ := List.mem_map.1 hx
    exact absurd hk (Nat.ne_of_gt (keys_lt_of_incK x l h e he))

private theorem getD_set (arr : Array Nat) {k : Nat} (hk : k < arr.size) (v i : Nat) :
    (arr.set! k v).getD i 0 = if k = i then v else arr.getD i 0 := by
  simp only [Array.set!_eq_setIfInBounds, Array.getD_eq_getD_getElem?,
    Array.getElem?_setIfInBounds, hk, if_true]
  split <;> rfl

private theorem getD_foldl (sp : List (Nat × Nat)) : ∀ (arr : Array Nat),
    (sp.map Prod.fst).Nodup → (∀ e ∈ sp, e.1 < arr.size) → ∀ i,
    (((sp.foldl (fun a x => a.set! x.1 x.2) arr).getD i 0 : Nat) : Int) =
      (if i ∈ sp.map Prod.fst then 0 else ((arr.getD i 0 : Nat) : Int)) +
        wSum sp (fun k => if k = i then 1 else 0) := by
  induction sp with
  | nil => intro arr _ _ i; simp [wSum]
  | cons x xs ih =>
    rcases x with ⟨k, v⟩
    intro arr hnd hlt i
    rw [List.map_cons, List.nodup_cons] at hnd
    have hsz : (arr.set! k v).size = arr.size := by simp
    rw [List.foldl_cons, ih _ hnd.2 (fun e he => hsz ▸ hlt e (List.mem_cons_of_mem _ he)) i,
      getD_set arr (hlt (k, v) List.mem_cons_self)]
    simp only [wSum, List.map_cons, List.sum_cons, List.mem_cons] at *
    by_cases hx : k = i
    · subst hx
      simp [hnd.1]
    · have : ¬ i = k := fun h => hx h.symm
      simp only [hx, this, if_false, false_or, mul_zero, zero_add]

theorem getD_table {sp : List (Nat × Nat)} {N : Nat} (hinc : incK sp = true)
    (hlt : ∀ e ∈ sp, e.1 < N) (i : Nat) :
    (((sp.foldl (fun a x => a.set! x.1 x.2) (Array.replicate N 0)).getD i 0 : Nat) : Int) =
      wSum sp (fun k => if k = i then 1 else 0) := by
  have h0 : (Array.replicate N 0).getD i 0 = 0 := by
    simp only [Array.getD_eq_getD_getElem?, Array.getElem?_replicate]
    split <;> rfl
  rw [getD_foldl sp _ (nodup_of_incK sp hinc) (fun e he => by simpa using hlt e he) i, h0]
  simp

private theorem sum_ind0 (J B x : Nat) (G : Nat → Int) :
    ∑ j : Fin J, (if B + (j : Nat) = x then G j else 0) =
      if B ≤ x ∧ x < B + J then G (x - B) else 0 := by
  split
  · rename_i h
    rw [Finset.sum_eq_single ⟨x - B, by omega⟩]
    · simp only [if_pos (show B + (x - B) = x by omega)]
    · intro j _ hj
      rw [if_neg]
      intro e
      exact hj (Fin.ext (by simp; omega))
    · simp
  · rename_i h
    refine Finset.sum_eq_zero fun j _ => if_neg fun e => h ⟨by omega, by omega⟩

private theorem eq_mul_add {n q s k : Nat} (hs : s < n) :
    q * n + s = k ↔ q = k / n ∧ s = k % n := by
  have hn : 0 < n := by omega
  constructor
  · rintro rfl
    refine ⟨?_, ?_⟩
    · rw [Nat.add_comm, Nat.add_mul_div_right _ _ hn, Nat.div_eq_of_lt hs, Nat.zero_add]
    · rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hs]
  · rintro ⟨rfl, rfl⟩
    rw [Nat.mul_comm]
    exact Nat.div_add_mod k n

private theorem sum_ind1 {n : Nat} (hn : 0 < n) (q k : Nat) (G : Nat → Int) :
    ∑ s : Fin n, (if q * n + (s : Nat) = k then G s else 0) =
      if q = k / n then G (k % n) else 0 := by
  simp only [eq_mul_add (Fin.isLt _)]
  split
  · rename_i h
    rw [Finset.sum_eq_single ⟨k % n, Nat.mod_lt _ hn⟩]
    · simp [h]
    · intro j _ hj
      rw [if_neg]
      intro e
      exact hj (Fin.ext e.2)
    · simp
  · rename_i h
    exact Finset.sum_eq_zero fun j _ => if_neg fun e => h e.1

private theorem ind_mul (k i : Nat) (F : Int) :
    (if k = i then (1 : Int) else 0) * F = if i = k then F else 0 := by
  by_cases h : k = i
  · simp [h]
  · simp [h, Ne.symm h]

private theorem sum_ind2 {n : Nat} (hn : 0 < n) (Q k : Nat) (H : Nat → Nat → Int) :
    ∑ r : Fin n, ∑ s : Fin n,
      (if k = (Q * n + (r : Nat)) * n + (s : Nat) then (1 : Int) else 0) * H r s =
      if Q = k / n / n then H (k / n % n) (k % n) else 0 := by
  simp only [ind_mul, sum_ind1 hn]
  rw [sum_ind1 hn (G := fun r => H r (k % n))]

private theorem sum_ind3 {n : Nat} (hn : 0 < n) (J B k : Nat) (F : Nat → Nat → Nat → Int) :
    ∑ j : Fin J, ∑ r : Fin n, ∑ s : Fin n,
      (if k = ((B + (j : Nat)) * n + (r : Nat)) * n + (s : Nat) then (1 : Int) else 0) *
        F j r s =
      if B ≤ k / n / n ∧ k / n / n < B + J then
        F (k / n / n - B) (k / n % n) (k % n) else 0 := by
  simp only [sum_ind2 hn (B + _) k (F _)]
  exact sum_ind0 J B (k / n / n) (fun j => F j (k / n % n) (k % n))

private theorem wSum_mul3 (J n : Nat) (I : Nat → Nat → Nat → Nat → Int)
    (F : Nat → Nat → Nat → Int) : ∀ sp : List (Nat × Nat),
    (∑ j : Fin J, ∑ r : Fin n, ∑ s : Fin n, wSum sp (fun k => I k j r s) * F j r s) =
      wSum sp (fun k => ∑ j : Fin J, ∑ r : Fin n, ∑ s : Fin n, I k j r s * F j r s)
  | [] => by simp [wSum]
  | e :: sp => by
    have ih := wSum_mul3 J n I F sp
    unfold wSum at ih ⊢
    simp only [List.map_cons, List.sum_cons, add_mul, Finset.sum_add_distrib, ih,
      Finset.mul_sum, mul_assoc]

private theorem wSum_mul2 (n : Nat) (I : Nat → Nat → Nat → Int) (F : Nat → Nat → Int) :
    ∀ sp : List (Nat × Nat),
    (∑ r : Fin n, ∑ s : Fin n, wSum sp (fun k => I k r s) * F r s) =
      wSum sp (fun k => ∑ r : Fin n, ∑ s : Fin n, I k r s * F r s)
  | [] => by simp [wSum]
  | e :: sp => by
    have ih := wSum_mul2 n I F sp
    unfold wSum at ih ⊢
    simp only [List.map_cons, List.sum_cons, add_mul, Finset.sum_add_distrib, ih,
      Finset.mul_sum, mul_assoc]

private theorem wSum_filter (P : Nat → Prop) [DecidablePred P] (f : Nat → Int) :
    ∀ sp : List (Nat × Nat),
    wSum sp (fun k => if P k then f k else 0) = wSum (sp.filter fun e => decide (P e.1)) f
  | [] => rfl
  | e :: sp => by
    have ih := wSum_filter P f sp
    unfold wSum at ih ⊢
    beta_reduce at ih ⊢
    rw [List.filter_cons]
    by_cases h : P e.1
    · simp only [h, if_true, decide_true, List.map_cons, List.sum_cons, ih]
    · simp only [h, if_false, decide_false, Bool.false_eq_true, List.map_cons, List.sum_cons,
        mul_zero, zero_add, ih]

theorem sum_wSum3 {n : Nat} (hn : 0 < n) (J B : Nat) (F : Nat → Nat → Nat → Int)
    (sp : List (Nat × Nat)) :
    fsum J (fun j => fsum n fun r => fsum n fun s =>
      wSum sp (fun k => if k = ((B + (j : Nat)) * n + (r : Nat)) * n + (s : Nat) then 1 else 0) *
        F j r s) =
      wSum (blkI n B J sp) (fun k => F (k / n / n - B) (k / n % n) (k % n)) := by
  simp only [fsum_eq_sum]
  have k := wSum_mul3 J n (fun k j r s => if k = ((B + j) * n + r) * n + s then 1 else 0) F sp
  beta_reduce at k
  rw [k]
  simp only [sum_ind3 hn]
  exact wSum_filter (fun k => B ≤ k / n / n ∧ k / n / n < B + J) _ sp

theorem sum_wSum2 {n : Nat} (hn : 0 < n) (Q : Nat) (H : Nat → Nat → Int)
    (sp : List (Nat × Nat)) :
    fsum n (fun r => fsum n fun s =>
      wSum sp (fun k => if k = (Q * n + (r : Nat)) * n + (s : Nat) then 1 else 0) * H r s) =
      wSum (blkT n Q sp) (fun k => H (k / n % n) (k % n)) := by
  simp only [fsum_eq_sum]
  have k := wSum_mul2 n (fun k r s => if k = (Q * n + r) * n + s then 1 else 0) H sp
  beta_reduce at k
  rw [k]
  simp only [sum_ind2 hn]
  have e : ∀ k, (Q = k / n / n) = (k / n / n = Q) := fun _ => propext eq_comm
  simp only [e]
  exact wSum_filter (fun k => k / n / n = Q) _ sp

theorem altOK_of_altW {p n J N N' : Nat} {m : NMod} {sp spt : List (Nat × Nat)}
    {ci : Nat → Nat → Nat → Nat → Nat → Int} {ct : Nat → Nat → Nat → Nat → Int}
    {tgt : Nat → Nat → Nat → Nat → Int}
    (hci : ∀ a₀ b₀ j r s, ci a₀ b₀ j r s =
      (((sp.foldl (fun arr x => arr.set! x.1 x.2) (Array.replicate N 0)).getD
        ((((a₀ * n + b₀) * J + j) * n + r) * n + s) 0 : Nat) : Int))
    (hct : ∀ a₀ b₀ r s, ct a₀ b₀ r s =
      (((spt.foldl (fun arr x => arr.set! x.1 x.2) (Array.replicate N' 0)).getD
        (((a₀ * n + b₀) * n + r) * n + s) 0 : Nat) : Int))
    (h : altW p m n J N N' sp spt tgt = true) : m.altOK p ci ct tgt = true := by
  simp only [altW, altCell, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true,
    List.mem_range, beq_iff_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨hn, hJ⟩, hi⟩, hit⟩, hl⟩, hlt⟩, hcell⟩ := h
  subst hn hJ
  have hget : ∀ j : Fin m.acts.length, m.acts.get j = m.acts.getD j default := fun j => by
    rw [List.get_eq_getElem, List.getElem_eq_getD default]
  simp only [NMod.altOK, List.all_eq_true, List.mem_finRange, true_implies, forall_const,
    beq_iff_eq]
  intro a₀ b₀ a b
  have hn : 0 < m.basis.length := Nat.lt_of_le_of_lt (Nat.zero_le _) a₀.isLt
  simp only [hci, hct, getD_table hi hl, getD_table hit hlt, hget]
  have k3 := sum_wSum3 hn m.acts.length ((a₀ * m.basis.length + b₀) * m.acts.length)
    (fun j r s => (m.acts.getD j default).ent m.basis.length a r *
      (m.acts.getD j default).ent m.basis.length b s - kd a r * kd b s) sp
  have k2 := sum_wSum2 hn (a₀ * m.basis.length + b₀)
    (fun r s => kd a r * kd b s + kd a s * kd b r) spt
  beta_reduce at k3 k2
  rw [k3, k2]
  exact hcell a₀ a₀.isLt b₀ b₀.isLt a a.isLt b b.isLt

section Glue

variable {M V₀ V : Type} [Inhabited M] {O₀ : Ops M V₀} {O : Ops Nat V} (H : Hom O₀ O)

theorem modCheckE_of_N {sA sB : String} {A B : Nat} (eA : O₀.decode sA = H.U A)
    (eB : O₀.decode sB = H.U B) (hA : H.P A) (hB : H.P B) {nregs : Nat} {prog : List Op}
    {p : Nat} {m : NMod} {tops : List Pc} {gs : List NGrp} {cf : Nat → Nat → Nat → Int}
    {ci : Nat → Nat → Nat → Nat → Nat → Int} {ct : Nat → Nat → Nat → Nat → Int}
    (hK : mcertN O A B ⟨nregs, prog, m.modFactsE p tops gs⟩ = true) (hwf : m.wf p = true)
    (hpc : pcWf (tops ++ m.basisPc p) = true)
    (hent : m.acts.all (fun g => g.mat.all (· < p)) = true)
    (htop : tops.all (fun q => m.acts.any (·.reg == q.reg)) = true)
    (hgrp : m.grpOK tops gs = true) (hp : p ≤ m.basis.length) (hfun : m.funOK p cf = true)
    (halt : m.altOK p ci ct tgtAlt = true) :
    modCheckE O₀ sA sB nregs prog p m tops gs cf ci ct = true := by
  unfold modCheckE
  rw [mcertCheck_of_N H eA eB hA hB hK, hwf, hpc, hent, htop, hgrp, decide_eq_true hp, hfun,
    halt]
  rfl

theorem modCheckW_of_N {sA sB : String} {A B : Nat} (eA : O₀.decode sA = H.U A)
    (eB : O₀.decode sB = H.U B) (hA : H.P A) (hB : H.P B) {nregs : Nat} {prog : List Op}
    {p : Nat} {m : NMod} {tops : List Pc} {tidx : List Nat} {s : Nat}
    {cf : Nat → Nat → Nat → Int}
    {ci : Nat → Nat → Nat → Nat → Nat → Int} {ct : Nat → Nat → Nat → Nat → Int}
    (hK : mcertN O A B ⟨nregs, prog, m.modFactsW p tops⟩ = true) (hwf : m.wf p = true)
    (hpc : pcWf (tops ++ m.basisPc p) = true)
    (htop : tops.all (fun q => m.acts.any (·.reg == q.reg)) = true)
    (hw : m.wOK p tops tidx s = true) (hp : p ≤ m.basis.length) (hfun : m.funOK p cf = true)
    (halt : m.altOK p ci ct tgtAlt = true) :
    modCheckW O₀ sA sB nregs prog p m tops tidx s cf ci ct = true := by
  unfold modCheckW
  rw [mcertCheck_of_N H eA eB hA hB hK, hwf, hpc, htop, hw, decide_eq_true hp, hfun, halt]
  rfl

end Glue

end CFSG.AGLEmbedding.R3

end

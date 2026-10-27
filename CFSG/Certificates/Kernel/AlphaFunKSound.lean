module

public import Certificates.Data.Kernel.AlphaFunK
public import CFSG.Certificates.Kernel.AlphaGrpKSound

public section

namespace CFSG.AGLEmbedding.R3

private theorem fsum_eq_sumF (N : Nat) (f : Fin N → Int) : fsum N f = ∑ i, f i :=
  (Fin.sum_univ_def f).symm

private theorem eq_mul_addF {n q s k : Nat} (hs : s < n) :
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

private theorem sum_ind1F {n : Nat} (hn : 0 < n) (q k : Nat) (G : Nat → Int) :
    ∑ s : Fin n, (if q * n + (s : Nat) = k then G s else 0) =
      if q = k / n then G (k % n) else 0 := by
  simp only [eq_mul_addF (Fin.isLt _)]
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

private theorem ind_mulF (k i : Nat) (F : Int) :
    (if k = i then (1 : Int) else 0) * F = if i = k then F else 0 := by
  by_cases h : k = i
  · simp [h]
  · simp [h, Ne.symm h]

private theorem sum_ind2F {n J : Nat} (hn : 0 < n) (hJ : 0 < J) (Q k : Nat)
    (F : Nat → Nat → Int) :
    ∑ j : Fin J, ∑ s : Fin n,
      (if k = (Q * J + (j : Nat)) * n + (s : Nat) then (1 : Int) else 0) * F j s =
      if Q = k / n / J then F (k / n % J) (k % n) else 0 := by
  simp only [ind_mulF, sum_ind1F hn]
  rw [sum_ind1F hJ (G := fun j => F j (k % n))]

private theorem wSum_mulF (J n : Nat) (I : Nat → Nat → Nat → Int) (F : Nat → Nat → Int) :
    ∀ sp : List (Nat × Nat),
    (∑ j : Fin J, ∑ s : Fin n, wSum sp (fun k => I k j s) * F j s) =
      wSum sp (fun k => ∑ j : Fin J, ∑ s : Fin n, I k j s * F j s)
  | [] => by simp [wSum]
  | e :: sp => by
    have ih := wSum_mulF J n I F sp
    unfold wSum at ih ⊢
    simp only [List.map_cons, List.sum_cons, add_mul, Finset.sum_add_distrib, ih,
      Finset.mul_sum, mul_assoc]

private theorem wSum_filterF (P : Nat → Prop) [DecidablePred P] (f : Nat → Int) :
    ∀ sp : List (Nat × Nat),
    wSum sp (fun k => if P k then f k else 0) = wSum (sp.filter fun e => decide (P e.1)) f
  | [] => rfl
  | e :: sp => by
    have ih := wSum_filterF P f sp
    unfold wSum at ih ⊢
    beta_reduce at ih ⊢
    rw [List.filter_cons]
    by_cases h : P e.1
    · simp only [h, if_true, decide_true, List.map_cons, List.sum_cons, ih]
    · simp only [h, if_false, decide_false, Bool.false_eq_true, List.map_cons, List.sum_cons,
        mul_zero, zero_add, ih]

theorem sum_wSumF {n J : Nat} (hn : 0 < n) (hJ : 0 < J) (Q : Nat) (F : Nat → Nat → Int)
    (sp : List (Nat × Nat)) :
    fsum J (fun j => fsum n fun s =>
      wSum sp (fun k => if k = (Q * J + (j : Nat)) * n + (s : Nat) then 1 else 0) * F j s) =
      wSum (blkF n J Q sp) (fun k => F (k / n % J) (k % n)) := by
  simp only [fsum_eq_sumF]
  have k := wSum_mulF J n (fun k j s => if k = (Q * J + j) * n + s then 1 else 0) F sp
  beta_reduce at k
  rw [k]
  simp only [sum_ind2F hn hJ]
  have e : ∀ k, (Q = k / n / J) = (k / n / J = Q) := fun _ => propext eq_comm
  simp only [e]
  exact wSum_filterF (fun k => k / n / J = Q) _ sp

theorem funOK_of_funW {p n J N : Nat} {m : NMod} {sp : List (Nat × Nat)}
    {cf : Nat → Nat → Nat → Int}
    (hcf : ∀ r₀ j s, cf r₀ j s =
      (((sp.foldl (fun arr x => arr.set! x.1 x.2) (Array.replicate N 0)).getD
        ((r₀ * J + j) * n + s) 0 : Nat) : Int))
    (h : funW p m n J N sp = true) : m.funOK p cf = true := by
  simp only [funW, funCell, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true,
    List.mem_range, beq_iff_eq] at h
  obtain ⟨⟨⟨⟨⟨hn, hJ⟩, hJ0⟩, hi⟩, hl⟩, hrow⟩ := h
  subst hn hJ
  have hget : ∀ j : Fin m.acts.length, m.acts.get j = m.acts.getD j default := fun j => by
    rw [List.get_eq_getElem, List.getElem_eq_getD default]
  simp only [NMod.funOK, List.all_eq_true, List.mem_finRange, true_implies, forall_const,
    beq_iff_eq]
  intro r₀ r
  have hn : 0 < m.basis.length := Nat.lt_of_le_of_lt (Nat.zero_le _) r₀.isLt
  simp only [hcf, getD_table hi hl, hget]
  have kF := sum_wSumF hn hJ0 r₀
    (fun j s => (m.acts.getD j default).ent m.basis.length r s - kd r s) sp
  beta_reduce at kF
  rw [kF]
  exact hrow r₀ r₀.isLt r r.isLt

end CFSG.AGLEmbedding.R3

end

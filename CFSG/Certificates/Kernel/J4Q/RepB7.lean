module

public import CFSG.Certificates.Kernel.J4Q.RepQT2A
public import Certificates.Data.Kernel.J4Q.VOrb

public section

namespace CFSG.KC.J4Q

open CFSG.KC.LQT.Syl

private theorem andB_true' (a b : Bool) : andB a b = true ↔ a = true ∧ b = true := by
  cases a <;> cases b <;> decide

private theorem dropK_eq' : ∀ (n : Nat) (l : List Nat), dropK n l = l.drop n
  | 0, l => rfl
  | n + 1, l => by
    change List.rec (motive := fun _ => List Nat) List.nil (fun _ t _ => t) (dropK n l) = _
    rw [dropK_eq' n l, ← List.tail_drop]
    cases l.drop n <;> rfl

private theorem headK_drop' (n : Nat) (l : List Nat) : headK (l.drop n) = l.getD n 0 := by
  rw [List.getD_eq_getElem?_getD, ← List.head?_drop]
  cases l.drop n <;> rfl

private theorem vptsK_getD_succ (rm root : Nat) (EN : List Nat) (t : Nat) :
    (vptsK rm root EN).getD (t + 1) 0 = Nat.land (EN.getD t 0) rm := by
  unfold vptsK
  rw [List.getD_cons_succ, List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_map]
  cases EN[t]? with
  | none => exact (Nat.zero_and rm).symm
  | some e => rfl

private theorem vtGo_sound' (rm : Nat) (Rs : List (List Nat)) (P : List Nat) :
    ∀ (ch : List Nat) (ci k : Nat), vtGo rm Rs ch (P.drop ci) ci k = true →
      ∀ j < ch.length, Nat.shiftRight (ch.getD j 0) 114 < k + j ∧
        Nat.land (Nat.shiftRight (ch.getD j 0) 112) 3 < Rs.length ∧
        vecLJ (P.getD (Nat.shiftRight (ch.getD j 0) 114) 0)
          (Rs.getD (Nat.land (Nat.shiftRight (ch.getD j 0) 112) 3) []) = Nat.land (ch.getD j 0) rm
  | [], _, _, _, j, hj => absurd hj (Nat.not_lt_zero _)
  | e :: ch, ci, k, h, j, hj => by
    change andB (Nat.ble ci (Nat.shiftRight e 114)) (andB (Nat.blt (Nat.shiftRight e 114) k)
      (andB (Nat.blt (Nat.land (Nat.shiftRight e 112) 3) Rs.length)
        (andB (Nat.beq (vecLJ (headK (dropK (Nat.shiftRight e 114 - ci) (P.drop ci)))
          (Rs.getD (Nat.land (Nat.shiftRight e 112) 3) [])) (Nat.land e rm))
          (vtGo rm Rs ch (dropK (Nat.shiftRight e 114 - ci) (P.drop ci)) (Nat.shiftRight e 114)
            (k + 1))))) = true at h
    simp only [andB_true', Nat.ble_eq, Nat.blt_eq, Nat.beq_eq] at h
    obtain ⟨h1, h2, h3, h4, h5⟩ := h
    have hd : dropK (Nat.shiftRight e 114 - ci) (P.drop ci) = P.drop (Nat.shiftRight e 114) := by
      rw [dropK_eq', List.drop_drop, Nat.add_sub_cancel' h1]
    rw [hd] at h4 h5
    cases j with
    | zero =>
      refine ⟨by simpa using h2, h3, ?_⟩
      rw [← headK_drop']
      exact h4
    | succ j =>
      obtain ⟨hp, hl, he⟩ := vtGo_sound' rm Rs P ch _ (k + 1) h5 j (by simpa using hj)
      exact ⟨by simp only [List.getD_cons_succ] at hp ⊢; omega, by simpa using hl,
        by simpa using he⟩

private theorem flatten_index' {B : Nat} : ∀ {chs : List (List Nat)},
    (∀ i, i + 1 < chs.length → (chs.getD i []).length = B) →
    ∀ t < chs.flatten.length, ∃ i < chs.length, ∃ j < (chs.getD i []).length,
      t = B * i + j ∧ chs.flatten.getD t 0 = (chs.getD i []).getD j 0
  | [], _, t, ht => by simp at ht
  | c :: cs, hB, t, ht => by
    rw [List.flatten_cons, List.length_append] at ht
    by_cases htc : t < c.length
    · refine ⟨0, by simp, t, by simpa using htc, by simp, ?_⟩
      rw [List.flatten_cons, List.getD_append _ _ _ _ htc]
      rfl
    · have hcs : cs ≠ [] := by
        rintro rfl
        simp at ht
        omega
      have hcB : c.length = B := by
        have := hB 0 (by simpa using List.length_pos_of_ne_nil hcs)
        simpa using this
      obtain ⟨i, hi, j, hj, he, hg⟩ := flatten_index' (chs := cs)
        (fun i hi => by simpa using hB (i + 1) (by simpa using hi)) (t - c.length) (by omega)
      refine ⟨i + 1, by simpa using hi, j, by simpa using hj, ?_, ?_⟩
      · rw [Nat.mul_succ]
        omega
      · rw [List.flatten_cons, List.getD_append_right _ _ _ _ (by omega)]
        simpa using hg

theorem vtChunks_sound {rm root B cap : Nat} {Rs : List (List Nat)} {chs : List (List Nat)}
    {p0s : List Nat} (_hlen : chs.flatten.length + 1 = cap)
    (_hchs : ∀ i, i + 1 < chs.length → (chs.getD i []).length = B)
    (_htree : ∀ i < chs.length, vtChunkK rm Rs (vptsK rm root chs.flatten) (chs.getD i [])
      (p0s.getD i 0) (1 + B * i) = true) :
    ∀ k, 0 < k → k < cap →
      Nat.shiftRight (chs.flatten.getD (k - 1) 0) 114 < k ∧
      Nat.land (Nat.shiftRight (chs.flatten.getD (k - 1) 0) 112) 3 < Rs.length ∧
      vecLJ ((vptsK rm root chs.flatten).getD (Nat.shiftRight (chs.flatten.getD (k - 1) 0) 114) 0)
        (Rs.getD (Nat.land (Nat.shiftRight (chs.flatten.getD (k - 1) 0) 112) 3) []) =
        (vptsK rm root chs.flatten).getD k 0 := by
  intro k hk0 hk
  obtain ⟨t, rfl⟩ : ∃ t, k = t + 1 := ⟨k - 1, by omega⟩
  rw [Nat.add_sub_cancel]
  have htl : t < chs.flatten.length := by omega
  obtain ⟨i, hi, j, hj, htij, hg⟩ := flatten_index' _hchs t htl
  have ht := _htree i hi
  unfold vtChunkK at ht
  rw [dropK_eq'] at ht
  obtain ⟨hpar, hlab, he⟩ := vtGo_sound' rm Rs _ _ _ _ ht j hj
  rw [hg]
  refine ⟨by omega, hlab, ?_⟩
  rw [he, vptsK_getD_succ, hg]

open CFSG.KC.LQT.T2 in
theorem spanLt_perm (x : Nat) (k : List Nat → List Nat → List Nat) : ∀ (ys acc : List Nat),
    ∃ p r, spanLt x ys k acc = k p r ∧ (p ++ r).Perm (acc ++ ys)
  | [], acc => ⟨acc.reverse, [], rfl, by
      rw [List.append_nil, List.append_nil]
      exact List.reverse_perm acc⟩
  | y :: ys', acc => by
    change ∃ p r, Bool.rec (motive := fun _ => List Nat) (k (List.reverse acc) (List.cons y ys'))
      (spanLt x ys' k (List.cons y acc)) (Nat.blt y x) = k p r ∧ (p ++ r).Perm (acc ++ y :: ys')
    cases Nat.blt y x
    · exact ⟨acc.reverse, y :: ys', rfl, (List.reverse_perm acc).append_right _⟩
    · obtain ⟨p, r, e, hp⟩ := spanLt_perm x k ys' (y :: acc)
      exact ⟨p, r, e, hp.trans List.perm_middle.symm⟩

open CFSG.KC.LQT.T2 in
theorem mergeK_perm : ∀ (xs ys : List Nat), (mergeK xs ys).Perm (xs ++ ys)
  | [], ys => List.Perm.refl ys
  | x :: xs, ys => by
    change (spanLt x ys (fun p r => List.append p (List.cons x (mergeK xs r))) []).Perm _
    obtain ⟨p, r, e, hp⟩ := spanLt_perm x (fun p r => List.append p (List.cons x (mergeK xs r))) ys []
    rw [e]
    rw [List.nil_append] at hp
    change (p ++ x :: mergeK xs r).Perm (x :: (xs ++ ys))
    refine (((mergeK_perm xs r).cons x).append_left p).trans (List.perm_middle.trans ?_)
    refine List.Perm.cons x ?_
    rw [← List.append_assoc]
    exact (List.perm_append_comm.append_right r).trans (by rw [List.append_assoc]; exact hp.append_left xs)

open CFSG.KC.LQT.T2 in
@[expose] noncomputable def passGo (rs : List (List Nat)) (o : Option (List Nat)) : List (List Nat) :=
  List.rec (motive := fun _ => Option (List Nat) → List (List Nat))
    (fun o => Option.rec (motive := fun _ => List (List Nat)) [] (fun a => [a]) o)
    (fun r _ ih o => Option.rec (motive := fun _ => List (List Nat)) (ih (some r))
      (fun a => List.cons (mergeK a r) (ih none)) o) rs o

open CFSG.KC.LQT.T2 in
theorem passGo_perm : ∀ (rs : List (List Nat)) (o : Option (List Nat)),
    (passGo rs o).flatten.Perm (o.getD [] ++ rs.flatten)
  | [], none => List.Perm.refl _
  | [], some a => by
    change ([a] : List (List Nat)).flatten.Perm (a ++ [])
    rw [List.flatten_singleton, List.append_nil]
  | r :: rs, none => by
    change (passGo rs (some r)).flatten.Perm ([] ++ (r ++ rs.flatten))
    exact passGo_perm rs (some r)
  | r :: rs, some a => by
    change (mergeK a r ++ (passGo rs none).flatten).Perm (a ++ (r ++ rs.flatten))
    rw [← List.append_assoc]
    exact (mergeK_perm a r).append (passGo_perm rs none)

open CFSG.KC.LQT.T2 in
theorem passK_perm (rs : List (List Nat)) : (passK rs).flatten.Perm rs.flatten :=
  passGo_perm rs none

theorem flatten_singletons : ∀ (l : List Nat), (l.map fun x => [x]).flatten = l
  | [] => rfl
  | x :: l => by
    rw [List.map_cons, List.flatten_cons, flatten_singletons l]
    rfl

open CFSG.KC.LQT.T2 in
theorem sortN_perm' (l : List Nat) : (sortN l).Perm l := by
  have key : ∀ n, (Nat.rec (motive := fun _ => List (List Nat)) (List.map (fun x => [x]) l)
      (fun _ ih => passK ih) n).flatten.Perm l := by
    intro n
    induction n with
    | zero =>
      change (List.map (fun x => [x]) l).flatten.Perm l
      rw [flatten_singletons]
    | succ n ih => exact (passK_perm _).trans ih
  exact key 17

theorem mem_dropLt {x y : Nat} : ∀ {ys : List Nat}, y ∈ dropLt x ys → y ∈ ys
  | [], h => h
  | z :: ys, h => by
    change y ∈ Bool.rec (motive := fun _ => List Nat) (List.cons z ys) (dropLt x ys) (Nat.blt z x) at h
    revert h
    cases Nat.blt z x
    · exact id
    · exact fun h => List.mem_cons_of_mem _ (mem_dropLt h)

theorem diffS_mem : ∀ (xs ys : List Nat) {x : Nat}, x ∈ xs → x ∉ diffS xs ys → x ∈ ys
  | [], _, _, hx, _ => absurd hx List.not_mem_nil
  | z :: xs, ys, x, hx, hn => by
    change x ∉ Bool.rec (motive := fun _ => List Nat) (List.cons z (diffS xs (dropLt z ys)))
      (diffS xs (dropLt z ys))
      (List.rec (motive := fun _ => Bool) false (fun y _ _ => Nat.beq y z) (dropLt z ys)) at hn
    have hz : z ∉ Bool.rec (motive := fun _ => List Nat) (List.cons z (diffS xs (dropLt z ys)))
        (diffS xs (dropLt z ys))
        (List.rec (motive := fun _ => Bool) false (fun y _ _ => Nat.beq y z) (dropLt z ys)) →
        z ∈ ys := by
      intro hz
      cases hd : dropLt z ys with
      | nil =>
        rw [hd] at hz
        exact absurd List.mem_cons_self hz
      | cons y t =>
        rw [hd] at hz
        change z ∉ Bool.rec (motive := fun _ => List Nat) _ _ (Nat.beq y z) at hz
        cases hb : Nat.beq y z
        · rw [hb] at hz
          exact absurd List.mem_cons_self hz
        · have : y ∈ dropLt z ys := by rw [hd]; exact List.mem_cons_self
          rw [Nat.eq_of_beq_eq_true hb] at this
          exact mem_dropLt this
    rcases List.mem_cons.1 hx with rfl | hx'
    · exact hz hn
    · have hn' : x ∉ diffS xs (dropLt z ys) := by
        intro h
        apply hn
        cases List.rec (motive := fun _ => Bool) false (fun y _ _ => Nat.beq y z) (dropLt z ys)
        · exact List.mem_cons_of_mem _ h
        · exact h
      exact mem_dropLt (diffS_mem xs (dropLt z ys) hx' hn')

theorem eqLK_nil {l : List Nat} (h : eqLK l [] = true) : l = [] := by
  cases l with
  | nil => rfl
  | cons a t =>
    have e : eqLK (a :: t) [] = false := rfl
    rw [e] at h
    exact absurd h (by decide)

theorem spInK_mem {sc : List Nat} {Pch : List (List Nat)} (h : spInK sc Pch = true) :
    ∀ x ∈ sc, ∃ pc ∈ Pch, x ∈ pc := by
  have key : ∀ (Q : List (List Nat)) (acc : List Nat) {x : Nat}, x ∈ acc →
      x ∉ List.foldl (fun acc pc => diffS acc (sortN pc)) acc Q → ∃ pc ∈ Q, x ∈ pc := by
    intro Q
    induction Q with
    | nil => intro acc x hx hn; exact absurd hx hn
    | cons pc Q ih =>
      intro acc x hx hn
      rw [List.foldl_cons] at hn
      by_cases hd : x ∈ diffS acc (sortN pc)
      · obtain ⟨pc', hpc', hx'⟩ := ih _ hd hn
        exact ⟨pc', List.mem_cons_of_mem _ hpc', hx'⟩
      · exact ⟨pc, List.mem_cons_self, (sortN_perm' pc).mem_iff.1 (diffS_mem acc (sortN pc) hx hd)⟩
  intro x hx
  have hn := eqLK_nil h
  exact key Pch sc hx (by rw [hn]; exact List.not_mem_nil)

theorem sincK_lt : ∀ {l : List Nat} {b : Nat}, sincK l b = true → ∀ y ∈ l, b < y
  | [], _, _, y, hy => absurd hy List.not_mem_nil
  | x :: l, b, h, y, hy => by
    change andB (Nat.blt b x) (sincK l x) = true at h
    rw [andB_eq, Bool.and_eq_true] at h
    rcases List.mem_cons.1 hy with rfl | hy'
    · exact Nat.le_of_ble_eq_true h.1
    · exact Nat.lt_trans (Nat.le_of_ble_eq_true h.1) (sincK_lt h.2 y hy')

theorem sincK_nodup : ∀ {l : List Nat} {b : Nat}, sincK l b = true → l.Nodup
  | [], _, _ => List.nodup_nil
  | x :: l, b, h => by
    have h' := h
    change andB (Nat.blt b x) (sincK l x) = true at h'
    rw [andB_eq, Bool.and_eq_true] at h'
    refine List.nodup_cons.2 ⟨fun hx => ?_, sincK_nodup h'.2⟩
    exact Nat.lt_irrefl x (sincK_lt h'.2 x hx)

end CFSG.KC.J4Q

end

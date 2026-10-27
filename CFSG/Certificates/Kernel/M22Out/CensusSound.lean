module

public import CFSG.Certificates.Kernel.M22Out.ReplaySound
public import Mathlib.Tactic.ENatToNat
public import Mathlib.Tactic.ReduceModChar

public section

namespace CFSG.KC.M22Out

open CFSG.EvenSporadicStandard.M22Std.TabCheck CFSG.EvenSporadicStandard.M22Std.OutCheck

private theorem gD {α : Type} {l : List α} {d : α} {i : Nat} (h : i < l.length) :
    l.getD i d = l[i] := by
  simp [List.getD_eq_getElem?_getD, h]

theorem validT_id : ValidT idTab := ⟨by simp [idTab], fun a ha => by simpa [idTab] using ha⟩

theorem tmul_assoc' (a : Tab) {b c : Tab} (hb : ValidT b) (hc : ValidT c) :
    tmul (tmul a b) c = tmul a (tmul b c) := by
  unfold tmul
  rw [List.map_map]
  apply List.map_congr_left
  intro j hj
  have hj' : j < b.length := by rw [hb.1]; exact hc.2 j hj
  rw [Function.comp_apply, gD (l := List.map _ b) (by simpa using hj'), List.getElem_map,
    gD hj']

theorem tmul_id_left {t : Tab} (ht : ValidT t) : tmul idTab t = t := by
  unfold tmul
  conv => rhs; rw [← List.map_id t]
  apply List.map_congr_left
  intro j hj
  have := ht.2 j hj
  simp [idTab, List.getD_eq_getElem?_getD, this]

theorem tmul_id_right {t : Tab} (ht : ValidT t) : tmul t idTab = t := by
  apply List.ext_getElem
  · simp [tmul, idTab, ht.1]
  · intro i h1 h2
    simp only [tmul, idTab, List.getElem_map, List.getElem_range]
    exact gD h2

theorem wordTab_valid {gens : List Tab} (hg : ∀ i < 2, ValidT (gens.getD i idTab)) :
    ∀ w : List Nat, (∀ i ∈ w, i < 2) → ValidT (wordTab gens w)
  | [], _ => validT_id
  | i :: w, h => tmul_valid (hg i (h i (by simp)))
      (wordTab_valid hg w fun j hj => h j (by simp [hj]))

theorem eq_of_map_packT : ∀ A B : List Tab, (∀ a ∈ A, ValidT a) → (∀ b ∈ B, ValidT b) →
    A.map packT = B.map packT → A = B
  | [], [], _, _, _ => rfl
  | [], _ :: _, _, _, h => by simp at h
  | _ :: _, [], _, _, h => by simp at h
  | a :: A, b :: B, hA, hB, h => by
    simp only [List.map_cons, List.cons.injEq] at h
    rw [packT_inj (hA a (by simp)) (hB b (by simp)) h.1,
      eq_of_map_packT A B (fun x hx => hA x (by simp [hx])) (fun x hx => hB x (by simp [hx])) h.2]

theorem map_eq_of_mapEqK {f : Tab → Tab} : ∀ A B : List Tab, A.length = B.length →
    (∀ a ∈ A, ValidT (f a)) → (∀ b ∈ B, ValidT b) → mapEqK f A B = true → A.map f = B
  | [], [], _, _, _, _ => rfl
  | [], _ :: _, h, _, _, _ => by simp at h
  | _ :: _, [], h, _, _, _ => by simp at h
  | a :: A, b :: B, hl, hA, hB, h => by
    change (Nat.beq (packT (f a)) (packT b) && mapEqK f A B) = true at h
    rw [Bool.and_eq_true, Nat.beq_eq] at h
    rw [List.map_cons, packT_inj (hA a (by simp)) (hB b (by simp)) h.1,
      map_eq_of_mapEqK A B (by simpa using hl) (fun x hx => hA x (by simp [hx]))
        (fun x hx => hB x (by simp [hx])) h.2]

private theorem keyOf_lt : ∀ (t : Tab) (acc m : Nat), (∀ x ∈ t, x < 22) → acc < 22 ^ m →
    t.foldl (fun a x => a * 22 + x) acc < 22 ^ (m + t.length)
  | [], acc, m, _, h => by simpa using h
  | x :: t, acc, m, ht, h => by
    have hx := ht x (by simp)
    have h' : acc * 22 + x < 22 ^ (m + 1) := by
      rw [Nat.pow_succ]
      generalize 22 ^ m = X at h ⊢
      omega
    have := keyOf_lt t (acc * 22 + x) (m + 1) (fun y hy => ht y (by simp [hy])) h'
    rw [List.foldl_cons, List.length_cons]
    rw [show m + (t.length + 1) = m + 1 + t.length by omega]
    exact this

private theorem keyOf_lt' {t : Tab} (ht : ValidT t) : keyOf t < 2 ^ 100 := by
  have := keyOf_lt t 0 0 ht.2 (by decide)
  rw [Nat.zero_add, ht.1] at this
  exact Nat.lt_of_lt_of_le this (by decide)

private theorem packKeys_cons (t : Tab) (L : List Tab) :
    packKeys (t :: L) = keyOf t + 2 ^ 100 * packKeys L := rfl

private theorem keysK_cons (KP n j : Nat) (σ : List Nat) (prev : Nat) :
    keysK KP n (j :: σ) prev =
      (Nat.blt j n && Nat.blt prev (laneW 100 (2 ^ 100 - 1) KP j) &&
        keysK KP n σ (laneW 100 (2 ^ 100 - 1) KP j)) := by
  simp only [keysK, strictK_eq]
  try rfl

private theorem keysK_spec (KP n : Nat) : ∀ (σ : List Nat) (prev : Nat), keysK KP n σ prev = true →
    (∀ j ∈ σ, j < n) ∧ (σ.map (laneW 100 (2 ^ 100 - 1) KP)).Pairwise (· < ·) ∧
      ∀ x ∈ σ.map (laneW 100 (2 ^ 100 - 1) KP), prev < x
  | [], _, _ => by simp
  | j :: σ, prev, h => by
    rw [keysK_cons] at h
    simp only [Bool.and_eq_true, Nat.blt_eq] at h
    obtain ⟨⟨hj, hp⟩, hr⟩ := h
    obtain ⟨h1, h2, h3⟩ := keysK_spec KP n σ _ hr
    refine ⟨fun x hx => ?_, ?_, fun x hx => ?_⟩
    · rcases List.mem_cons.1 hx with rfl | hx
      · exact hj
      · exact h1 x hx
    · rw [List.map_cons, List.pairwise_cons]
      exact ⟨h3, h2⟩
    · rw [List.map_cons] at hx
      rcases List.mem_cons.1 hx with rfl | hx
      · exact hp
      · exact Nat.lt_trans hp (h3 x hx)

theorem keys_nodup {L : List Tab} {σ : List Nat} {n : Nat} (h : keysK (packKeys L) n σ 0 = true)
    (hl : σ.length = n) (hn : L.length = n) (hv : ∀ t ∈ L, ValidT t) : (L.map keyOf).Nodup := by
  obtain ⟨h1, h2, -⟩ := keysK_spec _ n σ 0 h
  set K := laneW 100 (2 ^ 100 - 1) (packKeys L)
  have hmap : (σ.map K).Nodup := h2.imp (fun h => Nat.ne_of_lt h)
  have hσ : σ.Nodup := List.Nodup.of_map K hmap
  have hsub : σ ⊆ List.range n := fun j hj => List.mem_range.2 (h1 j hj)
  have hperm : List.Perm σ (List.range n) :=
    (hσ.subperm hsub).perm_of_length_le (by simp [hl])
  have hK : L.map keyOf = (List.range n).map K := by
    apply List.ext_getElem
    · simp [hn]
    · intro j hj1 hj2
      have hjL : j < L.length := by simpa using hj1
      rw [List.getElem_map, List.getElem_map, List.getElem_range]
      change keyOf L[j] = laneW 100 (2 ^ 100 - 1) (packKeys L) j
      rw [laneW_eq, Nat.pow_mul]
      exact (lane_pack keyOf (2 ^ 100) packKeys packKeys_cons L j
        (fun t ht => keyOf_lt' (hv t ht)) hjL).symm
  rw [hK]
  exact (hperm.map K).nodup_iff.1 hmap

private theorem strictInc_of_pairwise : ∀ l : List Nat, l.Pairwise (· < ·) → strictInc l = true
  | [], _ => rfl
  | [_], _ => rfl
  | a :: b :: l, h => by
    have hab : a < b := List.rel_of_pairwise_cons h (by simp)
    have := strictInc_of_pairwise (b :: l) (List.Pairwise.of_cons h)
    simp [strictInc, hab, this]

theorem nodupCheck_of_nodup {l : List Tab} (h : (l.map keyOf).Nodup) : nodupCheck l = true := by
  unfold nodupCheck
  apply strictInc_of_pairwise
  have hs := List.pairwise_mergeSort (le := fun a b : Nat => decide (a ≤ b))
    (fun a b c h1 h2 => by simp only [decide_eq_true_eq] at *; omega)
    (fun a b => by simp only [Bool.or_eq_true, decide_eq_true_eq]; omega) (l.map keyOf)
  have hn := (List.mergeSort_perm (l.map keyOf) fun a b => decide (a ≤ b)).nodup_iff.2 h
  exact (hs.and hn).imp fun ⟨h1, h2⟩ => Nat.lt_of_le_of_ne (by simpa using h1) h2

section Conj

variable {g gi : Tab} (hg : ValidT g) (hgi : ValidT gi) (h1 : tmul gi g = idTab)
  (h2 : tmul g gi = idTab)
include hg hgi h1 h2

private theorem can1 (x : Tab) (hx : ValidT x) : tmul gi (tmul g x) = x := by
  rw [← tmul_assoc' gi hg hx, h1, tmul_id_left hx]

private theorem can2 (x : Tab) (hx : ValidT x) : tmul g (tmul gi x) = x := by
  rw [← tmul_assoc' g hgi hx, h2, tmul_id_left hx]

private theorem commF_conj {l t : Tab} (hl : ValidT l) (ht : ValidT t) :
    commF l (conjT g gi t) = commF (tmul (tmul gi l) g) t := by
  have c1 := can1 hg hgi h1 h2
  have c2 := can2 hg hgi h1 h2
  rw [Bool.eq_iff_iff, commF_iff, commF_iff]
  unfold conjT
  constructor
  · intro h
    have := congrArg (fun x => tmul (tmul gi x) g) h
    simp (disch := repeat' (first | assumption | exact validT_id | apply tmul_valid)) only
      [tmul_assoc', h1, h2, tmul_id_left, tmul_id_right, c1, c2] at this ⊢
    exact this
  · intro h
    have := congrArg (fun x => tmul (tmul g x) gi) h
    simp (disch := repeat' (first | assumption | exact validT_id | apply tmul_valid)) only
      [tmul_assoc', h1, h2, tmul_id_left, tmul_id_right, c1, c2] at this ⊢
    exact this

theorem centN_conj {L : List Tab} (hnd : L.Nodup) (hv : ∀ l ∈ L, ValidT l)
    (hcl : ∀ l ∈ L, tmul (tmul gi l) g ∈ L) {t : Tab} (ht : ValidT t) :
    centN L (conjT g gi t) = centN L t := by
  unfold centN
  rw [List.countP_congr (q := fun l => commF (tmul (tmul gi l) g) t)
    (fun l hl => by rw [commF_conj hg hgi h1 h2 (hv l hl) ht])]
  have hinj : ∀ x ∈ L, ∀ y ∈ L, tmul (tmul gi x) g = tmul (tmul gi y) g → x = y := by
    intro x hx y hy e
    have := congrArg (fun z => tmul (tmul g z) gi) e
    have hx' := hv x hx
    have hy' := hv y hy
    have c2 := can2 hg hgi h1 h2
    simp (disch := repeat' (first | assumption | exact validT_id | apply tmul_valid)) only
      [tmul_assoc', h1, h2, tmul_id_left, tmul_id_right, c2] at this
    exact this
  have hmnd : (L.map fun l => tmul (tmul gi l) g).Nodup := List.Nodup.map_on hinj hnd
  have hperm : List.Perm (L.map fun l => tmul (tmul gi l) g) L :=
    (hmnd.subperm (fun x hx => by
      obtain ⟨l, hl, rfl⟩ := List.mem_map.1 hx
      exact hcl l hl)).perm_of_length_le (by simp)
  have e : L.countP (fun l => commF (tmul (tmul gi l) g) t) =
      (L.map fun l => tmul (tmul gi l) g).countP (fun l => commF l t) := by
    rw [List.countP_map]
    rfl
  rw [e, hperm.countP_eq]

end Conj

section Closed

variable {gens gis : List Tab} {T : List Tab} {β : Tab}

structure ClosedHyp (gens gis T : List Tab) (β : Tab) : Prop where
  tv : ∀ t ∈ T, ValidT t
  nd : T.Nodup
  one : idTab ∈ T
  mul : ∀ t ∈ T, ∀ i < 2, tmul (gens.getD i idTab) t ∈ T
  word : ∀ t ∈ T, ∃ w : List Nat, (∀ i ∈ w, i < 2) ∧ wordTab gens w = t
  gv : ∀ i < 2, ValidT (gens.getD i idTab)
  giv : ∀ i < 2, ValidT (gis.getD i idTab)
  inv : ∀ i < 2, tmul (gis.getD i idTab) (gens.getD i idTab) = idTab
  inv' : ∀ i < 2, tmul (gens.getD i idTab) (gis.getD i idTab) = idTab
  bv : ValidT β
  bb : tmul β β = idTab
  bn : ∀ i < 2, tmul (tmul β (gens.getD i idTab)) β ∈ T

variable (H : ClosedHyp gens gis T β)
include H

private theorem bcan (x : Tab) (hx : ValidT x) : tmul β (tmul β x) = x := by
  rw [← tmul_assoc' β H.bv hx, H.bb, tmul_id_left hx]

private theorem word_mul_mem : ∀ w : List Nat, (∀ i ∈ w, i < 2) →
    ∀ y ∈ T, tmul (wordTab gens w) y ∈ T
  | [], _, y, hy => by
    change tmul idTab y ∈ T
    rw [tmul_id_left (H.tv y hy)]
    exact hy
  | i :: w, hw, y, hy => by
    change tmul (tmul (gens.getD i idTab) (wordTab gens w)) y ∈ T
    rw [tmul_assoc' _ (wordTab_valid H.gv w fun j hj => hw j (by simp [hj])) (H.tv y hy)]
    exact H.mul _ (word_mul_mem w (fun j hj => hw j (by simp [hj])) y hy) i (hw i (by simp))

theorem ClosedHyp.mul_mem {x y : Tab} (hx : x ∈ T) (hy : y ∈ T) : tmul x y ∈ T := by
  obtain ⟨w, hw, rfl⟩ := H.word x hx
  exact word_mul_mem H w hw y hy

theorem ClosedHyp.gen_mem {i : Nat} (hi : i < 2) : gens.getD i idTab ∈ T := by
  have := H.mul _ H.one i hi
  rwa [tmul_id_right (H.gv i hi)] at this

theorem ClosedHyp.inv_mem {i : Nat} (hi : i < 2) : gis.getD i idTab ∈ T := by
  have hinj : ∀ x ∈ T, ∀ y ∈ T, tmul (gens.getD i idTab) x = tmul (gens.getD i idTab) y →
      x = y := by
    intro x hx y hy e
    have := congrArg (tmul (gis.getD i idTab)) e
    rwa [can1 (H.gv i hi) (H.giv i hi) (H.inv i hi) (H.inv' i hi) x (H.tv x hx),
      can1 (H.gv i hi) (H.giv i hi) (H.inv i hi) (H.inv' i hi) y (H.tv y hy)] at this
  have hmnd := List.Nodup.map_on hinj H.nd
  have hperm : List.Perm (T.map (tmul (gens.getD i idTab))) T :=
    (hmnd.subperm (fun x hx => by
      obtain ⟨l, hl, rfl⟩ := List.mem_map.1 hx
      exact H.mul l hl i hi)).perm_of_length_le (by simp)
  obtain ⟨x, hx, e⟩ := List.mem_map.1 (hperm.mem_iff.2 H.one)
  have := congrArg (tmul (gis.getD i idTab)) e
  rw [can1 (H.gv i hi) (H.giv i hi) (H.inv i hi) (H.inv' i hi) x (H.tv x hx),
    tmul_id_right (H.giv i hi)] at this
  rw [← this]
  exact hx

private theorem word_conj_mem : ∀ w : List Nat, (∀ i ∈ w, i < 2) →
    tmul (tmul β (wordTab gens w)) β ∈ T
  | [], _ => by
    change tmul (tmul β idTab) β ∈ T
    rw [tmul_id_right H.bv, H.bb]
    exact H.one
  | i :: w, hw => by
    have hi := hw i (by simp)
    have hw' : ∀ j ∈ w, j < 2 := fun j hj => hw j (by simp [hj])
    have hu := wordTab_valid H.gv w hw'
    have hg := H.gv i hi
    have hb := H.bv
    have bc := bcan H
    have e : tmul (tmul β (wordTab gens (i :: w))) β =
        tmul (tmul (tmul β (gens.getD i idTab)) β) (tmul (tmul β (wordTab gens w)) β) := by
      change tmul (tmul β (tmul (gens.getD i idTab) (wordTab gens w))) β = _
      simp (disch := repeat' (first | assumption | exact validT_id | apply tmul_valid)) only
        [tmul_assoc', bc]
    rw [e]
    exact H.mul_mem (H.bn i hi) (word_conj_mem w hw')

theorem ClosedHyp.conjB_mem {x : Tab} (hx : x ∈ T) : tmul (tmul β x) β ∈ T := by
  obtain ⟨w, hw, rfl⟩ := H.word x hx
  exact word_conj_mem H w hw

theorem ClosedHyp.conj_gen {i : Nat} (hi : i < 2) {x : Tab} (hx : x ∈ T ++ T.map (tmul β)) :
    tmul (tmul (gis.getD i idTab) x) (gens.getD i idTab) ∈ T ++ T.map (tmul β) := by
  have hg := H.gv i hi
  have hc := H.giv i hi
  have hb := H.bv
  have bc := bcan H
  rcases List.mem_append.1 hx with hx | hx
  · exact List.mem_append_left _
      (H.mul_mem (H.mul_mem (H.inv_mem hi) hx) (H.gen_mem hi))
  · obtain ⟨y, hy, rfl⟩ := List.mem_map.1 hx
    have hyv := H.tv y hy
    apply List.mem_append_right
    refine List.mem_map.2 ⟨tmul (tmul (tmul β (gis.getD i idTab)) β)
      (tmul y (gens.getD i idTab)), H.mul_mem (H.conjB_mem (H.inv_mem hi)) (H.mul_mem hy (H.gen_mem hi)),
      ?_⟩
    simp (disch := repeat' (first | assumption | exact validT_id | apply tmul_valid)) only
      [tmul_assoc', bc]

theorem ClosedHyp.conj_beta {x : Tab} (hx : x ∈ T ++ T.map (tmul β)) :
    tmul (tmul β x) β ∈ T ++ T.map (tmul β) := by
  rcases List.mem_append.1 hx with hx | hx
  · exact List.mem_append_left _ (H.conjB_mem hx)
  · obtain ⟨y, hy, rfl⟩ := List.mem_map.1 hx
    have hyv := H.tv y hy
    apply List.mem_append_right
    refine List.mem_map.2 ⟨tmul (tmul β y) β, H.conjB_mem hy, ?_⟩
    have hb := H.bv
    have bc := bcan H
    simp (disch := repeat' (first | assumption | exact validT_id | apply tmul_valid)) only
      [tmul_assoc', bc]

end Closed

theorem conjTreeK_spec (gs gis I : List Tab) (PR : List (Nat × Nat × Nat)) :
    ∀ (PR' : List (Nat × Nat × Nat)) (Is : List Tab), conjTreeK gs gis I PR PR' Is = true →
      ∀ j (hj : j < PR'.length),
        (PR'[j].2.1 = 3 ∧ PR'[j].2.2 = 0) ∨
          (PR'[j].2.1 < 3 ∧ (PR.getD PR'[j].1 (0, 0, 0)).2.2 < PR'[j].2.2 ∧
            conjT (gs.getD PR'[j].2.1 idTab) (gis.getD PR'[j].2.1 idTab) (I.getD PR'[j].1 idTab) =
              Is.getD j idTab)
  | [], _, _, j, hj => absurd hj (by simp)
  | e :: PR', Is, h, j, hj => by
    change (Bool.rec (motive := fun _ => Bool)
          (and (and (Nat.blt e.2.1 3) (Nat.blt (PR.getD e.1 (0, 0, 0)).2.2 e.2.2))
            (conjT (gs.getD e.2.1 idTab) (gis.getD e.2.1 idTab) (I.getD e.1 idTab) ==
              Is.headD idTab))
          (Nat.beq e.2.2 0) (Nat.beq e.2.1 3) && conjTreeK gs gis I PR PR' Is.tail) = true at h
    rw [Bool.and_eq_true] at h
    obtain ⟨h0, hr⟩ := h
    cases j with
    | zero =>
      change (e.2.1 = 3 ∧ e.2.2 = 0) ∨ (e.2.1 < 3 ∧ (PR.getD e.1 (0, 0, 0)).2.2 < e.2.2 ∧
        conjT (gs.getD e.2.1 idTab) (gis.getD e.2.1 idTab) (I.getD e.1 idTab) = Is.getD 0 idTab)
      have hh : Is.getD 0 idTab = Is.headD idTab := by cases Is <;> rfl
      rw [hh]
      cases hb : Nat.beq e.2.1 3
      · have h0' : (Nat.blt e.2.1 3 && Nat.blt (PR.getD e.1 (0, 0, 0)).2.2 e.2.2 &&
            (conjT (gs.getD e.2.1 idTab) (gis.getD e.2.1 idTab) (I.getD e.1 idTab) ==
              Is.headD idTab)) = true := by
          rw [hb] at h0
          exact h0
        simp only [Bool.and_eq_true, Nat.blt_eq, beq_iff_eq] at h0'
        exact Or.inr ⟨h0'.1.1, h0'.1.2, h0'.2⟩
      · have h0' : Nat.beq e.2.2 0 = true := by
          rw [hb] at h0
          exact h0
        exact Or.inl ⟨Nat.eq_of_beq_eq_true hb, Nat.eq_of_beq_eq_true h0'⟩
    | succ j =>
      have hh : Is.getD (j + 1) idTab = Is.tail.getD j idTab := by cases Is <;> simp
      rw [hh]
      exact conjTreeK_spec gs gis I PR PR' Is.tail hr j (by simpa using hj)

end CFSG.KC.M22Out

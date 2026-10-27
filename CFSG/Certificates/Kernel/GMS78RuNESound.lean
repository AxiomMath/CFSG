module

public import Certificates.Data.Kernel.GMS78RuNE
public import CFSG.Certificates.Kernel.GMS78RuGenNE

public section

namespace CFSG.KC.GMS

open CFSG.KLie.CT CFSG.KC.Loop

private theorem andB_eq' (a b : Bool) : andB a b = (a && b) := by cases a <;> rfl
private theorem orB_eq' (a b : Bool) : orB a b = (a || b) := by cases a <;> rfl
private theorem notB_eq' (a : Bool) : notB a = !a := by cases a <;> rfl
private theorem strictN_eq' (y : Nat) (k : Nat → Nat) : strictN y k = k y := by cases y <;> rfl
private theorem neStrictB_eq (y : Nat) (k : Nat → Bool) : neStrictB y k = k y := by
  cases y <;> rfl

private theorem pw2_eq' (w : Nat) : pw2 w = 2 ^ w := by
  simp [pw2, Nat.shiftLeft_eq]

private theorem maskN_eq' (w : Nat) : maskN w = 2 ^ w - 1 := by
  simp [maskN, pw2_eq']

private theorem fget_eq' (X i w : Nat) : fget X i w = X / 2 ^ (i * w) % 2 ^ w := by
  change (X >>> (i * w)) &&& maskN w = _
  rw [maskN_eq', Nat.and_two_pow_sub_one_eq_mod, Nat.shiftRight_eq_div_pow]

private theorem testBit_fget' (X i w j : Nat) :
    (fget X i w).testBit j = (decide (j < w) && X.testBit (i * w + j)) := by
  change ((X >>> (i * w)) &&& maskN w).testBit j = _
  rw [maskN_eq', Nat.testBit_and, Nat.testBit_shiftRight, Nat.testBit_two_pow_sub_one,
    Bool.and_comm]

private theorem allN_iff' {n : Nat} {f : Nat → Bool} :
    allN n f = true ↔ ∀ i < n, f i = true := by
  induction n with
  | zero => exact ⟨fun _ _ hi => absurd hi (Nat.not_lt_zero _), fun _ => rfl⟩
  | succ n ih =>
    change andB (f n) (allN n f) = true ↔ _
    rw [andB_eq', Bool.and_eq_true, ih]
    constructor
    · rintro ⟨h1, h2⟩ i hi
      rcases Nat.lt_succ_iff_lt_or_eq.mp hi with h | h
      · exact h2 i h
      · exact h ▸ h1
    · intro h
      exact ⟨h n (Nat.lt_succ_self n), fun i hi => h i (Nat.lt_succ_of_lt hi)⟩

private theorem orN_testBit' {n : Nat} {f : Nat → Nat} {j : Nat} :
    (orN n f).testBit j = true ↔ ∃ i < n, (f i).testBit j = true := by
  induction n with
  | zero =>
    change (0 : Nat).testBit j = true ↔ _
    simp
  | succ n ih =>
    change (f n ||| orN n f).testBit j = true ↔ _
    rw [Nat.testBit_or, Bool.or_eq_true, ih]
    constructor
    · rintro (h | ⟨i, hi, h⟩)
      · exact ⟨n, Nat.lt_succ_self n, h⟩
      · exact ⟨i, Nat.lt_succ_of_lt hi, h⟩
    · rintro ⟨i, hi, h⟩
      rcases Nat.lt_succ_iff_lt_or_eq.mp hi with h' | h'
      · exact Or.inr ⟨i, h', h⟩
      · exact Or.inl (h' ▸ h)

private theorem orN_congr {n : Nat} {f g : Nat → Nat} (h : ∀ i < n, f i = g i) :
    orN n f = orN n g := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change f n ||| orN n f = g n ||| orN n g
    rw [h n (Nat.lt_succ_self n), ih fun i hi => h i (Nat.lt_succ_of_lt hi)]

private theorem fget_orN {n w : Nat} {f : Nat → Nat} (hf : ∀ i < n, f i < 2 ^ w) {j : Nat}
    (hj : j < n) : fget (orN n fun i => f i <<< (w * i)) j w = f j := by
  apply Nat.eq_of_testBit_eq
  intro b
  rw [testBit_fget', Nat.mul_comm j w]
  by_cases hb : b < w
  · rw [decide_eq_true hb, Bool.true_and]
    apply Bool.eq_iff_iff.mpr
    rw [orN_testBit']
    constructor
    · rintro ⟨i, hi, h⟩
      rw [Nat.testBit_shiftLeft, Bool.and_eq_true, decide_eq_true_eq] at h
      rcases Nat.lt_trichotomy i j with hij | rfl | hij
      · exfalso
        have hle : w * i + w ≤ w * j := by
          have := Nat.mul_le_mul_left w (show i + 1 ≤ j by omega)
          rwa [Nat.mul_succ] at this
        have hm : w ≤ w * j + b - w * i := by omega
        rw [Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le (hf i hi)
          (Nat.pow_le_pow_right Nat.two_pos hm))] at h
        exact Bool.false_ne_true h.2
      · rw [Nat.add_sub_cancel_left] at h
        exact h.2
      · exfalso
        have hle : w * j + w ≤ w * i := by
          have := Nat.mul_le_mul_left w (show j + 1 ≤ i by omega)
          rwa [Nat.mul_succ] at this
        omega
    · intro h
      exact ⟨j, hj, by rw [Nat.testBit_shiftLeft, Nat.add_sub_cancel_left]; simp [h]⟩
  · rw [decide_eq_false hb, Bool.false_and]
    exact (Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le (hf j hj)
      (Nat.pow_le_pow_right Nat.two_pos (by omega)))).symm

private theorem neAllL_eq {α : Type} (p : α → Bool) : ∀ l : List α, neAllL p l = l.all p
  | [] => rfl
  | a :: l => by
    change andB (p a) (neAllL p l) = _
    rw [andB_eq', neAllL_eq p l]
    rfl

private theorem neLen_eq {α : Type} : ∀ l : List α, neLen l = l.length
  | [] => rfl
  | _ :: l => by
    change strictN (neLen l) Nat.succ = _
    rw [strictN_eq', neLen_eq l]
    rfl

private theorem neGet_eq {α : Type} (d : α) : ∀ (l : List α) (k : Nat), neGet d l k = l.getD k d
  | [], k => by simp [neGet]
  | a :: l, 0 => by
    change a = _
    rw [List.getD_cons_zero]
  | a :: l, k + 1 => by
    change neGet d l k = _
    rw [neGet_eq d l k, List.getD_cons_succ]

private theorem neIdx_eq (l : Fin 7) : ∀ L : List (Fin 7), neIdx L l.val = L.idxOf l
  | [] => rfl
  | a :: L => by
    change Bool.rec (motive := fun _ => Nat) (Nat.succ (neIdx L l.val)) 0 (Nat.beq a.val l.val) = _
    rw [List.idxOf_cons, neIdx_eq l L]
    by_cases h : a = l
    · subst h
      rw [Nat.beq_refl]
      simp
    · have h' : Nat.beq a.val l.val = false :=
        Bool.eq_false_iff.mpr fun e => h (Fin.ext (Nat.eq_of_beq_eq_true e))
      rw [h']
      simp [h]

private theorem neBoundK_spec {T : List (List Nat)} (h : neBoundK T = true) :
    ∀ r ∈ T, ∀ x ∈ r, x < 64 := by
  intro r hr x hx
  have h' : neAllL (neAllL fun e => Nat.blt e 64) T = true := h
  rw [neAllL_eq, List.all_eq_true] at h'
  have h'' := h' r hr
  rw [neAllL_eq, List.all_eq_true] at h''
  exact Nat.blt_eq.mp (h'' x hx)

private theorem getD_bound {T : List (List Nat)} (hb : ∀ r ∈ T, ∀ x ∈ r, x < 64) (k : Nat) :
    ∀ x ∈ T.getD k [], x < 64 := by
  rw [List.getD_eq_getElem?_getD]
  cases h : T[k]? with
  | none => simp
  | some r => exact hb r (List.mem_of_getElem? h)

private theorem entry_lt {r : List Nat} (hr : ∀ x ∈ r, x < 64) (i : Nat) : r.getD i 0 < 64 := by
  rw [List.getD_eq_getElem?_getD]
  cases h : r[i]? with
  | none => simp
  | some x => exact hr x (List.mem_of_getElem? h)

private noncomputable def packF (r : List Nat) : Nat → Nat → Nat :=
  List.rec (motive := fun _ => Nat → Nat → Nat) (fun _ _ => nat_lit 0)
    (fun e _ ih n s => Nat.rec (motive := fun _ => Nat) (nat_lit 0)
      (fun n' _ => Nat.lor (Nat.shiftLeft e s) (ih n' (Nat.add s (nat_lit 6)))) n) r

private noncomputable def packV : List Nat → Nat
  | [] => 0
  | x :: R => x + 64 * packV R

private theorem packF_eq : ∀ r : List Nat, (∀ x ∈ r, x < 64) → ∀ n s,
    packF r n s = packV (r.take n) <<< s
  | [], _, n, s => by
    change 0 = _
    simp [packV]
  | x :: r, _, 0, s => by
    change 0 = packV [] <<< s
    simp [packV]
  | x :: r, hr, n + 1, s => by
    change x <<< s ||| packF r n (s + 6) = packV (x :: r.take n) <<< s
    rw [packF_eq r (fun y hy => hr y (List.mem_cons_of_mem _ hy)) n (s + 6)]
    have hx : x < 2 ^ 6 := hr x List.mem_cons_self
    rw [Nat.add_comm s 6, Nat.shiftLeft_add, ← Nat.shiftLeft_or_distrib, Nat.or_comm,
      ← Nat.shiftLeft_add_eq_or_of_lt hx]
    congr 1
    simp only [packV, Nat.shiftLeft_eq, show (2 : Nat) ^ 6 = 64 from rfl]
    omega

private theorem packV_field : ∀ R : List Nat, (∀ x ∈ R, x < 64) → ∀ i,
    packV R / 2 ^ (i * 6) % 2 ^ 6 = R.getD i 0
  | [], _, i => by simp [packV]
  | x :: R, hR, 0 => by
    have hx := hR x List.mem_cons_self
    simp only [packV, Nat.zero_mul, Nat.pow_zero, Nat.div_one, List.getD_cons_zero]
    omega
  | x :: R, hR, i + 1 => by
    have hx := hR x List.mem_cons_self
    rw [List.getD_cons_succ, ← packV_field R (fun y hy => hR y (List.mem_cons_of_mem _ hy)) i,
      show (i + 1) * 6 = 6 + i * 6 by omega, Nat.pow_add, ← Nat.div_div_eq_div_mul]
    congr 2
    simp only [packV]
    omega

private theorem packV_lt : ∀ R : List Nat, (∀ x ∈ R, x < 64) → packV R < 2 ^ (6 * R.length)
  | [], _ => by simp [packV]
  | x :: R, hR => by
    have hx := hR x List.mem_cons_self
    have ih := packV_lt R (fun y hy => hR y (List.mem_cons_of_mem _ hy))
    simp only [packV, List.length_cons]
    rw [show 6 * (R.length + 1) = 6 * R.length + 6 by omega, Nat.pow_add,
      show (2 : Nat) ^ 6 = 64 from rfl]
    omega

private theorem nePack_eq {r : List Nat} (hr : ∀ x ∈ r, x < 64) :
    nePack r = packV (r.take 64) := by
  change packF r 64 0 = _
  rw [packF_eq r hr, Nat.shiftLeft_zero]

private theorem nePack_lt {r : List Nat} (hr : ∀ x ∈ r, x < 64) : nePack r < 2 ^ 384 := by
  rw [nePack_eq hr]
  have hT : ∀ x ∈ r.take 64, x < 64 := fun x hx => hr x (List.mem_of_mem_take hx)
  calc _ < 2 ^ (6 * (r.take 64).length) := packV_lt _ hT
    _ ≤ 2 ^ 384 := Nat.pow_le_pow_right Nat.two_pos (by simp; omega)

private theorem fget_nePack {r : List Nat} (hr : ∀ x ∈ r, x < 64) {i : Nat} (hi : i < 64) :
    fget (nePack r) i 6 = r.getD i 0 := by
  have hT : ∀ x ∈ r.take 64, x < 64 := fun x hx => hr x (List.mem_of_mem_take hx)
  rw [fget_eq', nePack_eq hr, packV_field _ hT i]
  simp [List.getD_eq_getElem?_getD, List.getElem?_take, hi]

section Perm

variable {conjTab : List (List Nat)} {L : List (Fin 7)}

private theorem fget_neRows (hb : ∀ r ∈ conjTab, ∀ x ∈ r, x < 64) (l : Fin 7) :
    fget (neRows conjTab L) l.val 384 = nePack (conjTab.getD (L.idxOf l) []) := by
  change fget (orN 7 fun v => nePack (neGet [] conjTab (neIdx L v)) <<< (384 * v)) l.val 384 = _
  rw [fget_orN (fun i _ => by rw [neGet_eq]; exact nePack_lt (getD_bound hb _)) l.isLt,
    neIdx_eq, neGet_eq]

private theorem fget_row (hb : ∀ r ∈ conjTab, ∀ x ∈ r, x < 64) (l : Fin 7) {j : Nat}
    (hj : j < 64) :
    fget (fget (neRows conjTab L) l.val 384) j 6 = Gen.neConjPermG conjTab L l j := by
  rw [fget_neRows hb, fget_nePack (getD_bound hb _) hj]
  rfl

private theorem conjPerm_lt (hb : ∀ r ∈ conjTab, ∀ x ∈ r, x < 64) (l : Fin 7) (j : Nat) :
    Gen.neConjPermG conjTab L l j < 64 :=
  entry_lt (getD_bound hb _) j

private theorem foldr_lt (hb : ∀ r ∈ conjTab, ∀ x ∈ r, x < 64) :
    ∀ (u : List (Fin 7)) {i : Nat}, i < 64 → u.foldr (Gen.neConjPermG conjTab L) i < 64
  | [], _, hi => hi
  | l :: _, _, _ => conjPerm_lt hb l _

private theorem nePermW_eq (hb : ∀ r ∈ conjTab, ∀ x ∈ r, x < 64) :
    ∀ u : List (Fin 7), nePermW (neRows conjTab L) u =
      orN 64 fun i => u.foldr (Gen.neConjPermG conjTab L) i <<< (6 * i)
  | [] => rfl
  | l :: u => by
    change strictN (nePermW (neRows conjTab L) u) (fun P => orN 64 fun i =>
        fget (fget (neRows conjTab L) l.val 384) (fget P i 6) 6 <<< (6 * i)) = _
    rw [strictN_eq', nePermW_eq hb u]
    apply orN_congr
    intro i hi
    rw [fget_orN (fun i hi => foldr_lt hb u hi) hi, fget_row hb l (foldr_lt hb u hi)]
    rfl

private theorem actPerm_getD (u : List (Fin 7)) {i : Nat} (hi : i < 64) :
    (Gen.neActPermG conjTab L u).getD i 0 = u.foldr (Gen.neConjPermG conjTab L) i := by
  simp [Gen.neActPermG, List.getD_eq_getElem?_getD, hi]

private noncomputable def gpack (lst : List Nat) : Nat := orN 64 fun i => lst.getD i 0 <<< (6 * i)

private theorem nePermW_gpack (hb : ∀ r ∈ conjTab, ∀ x ∈ r, x < 64) (u : List (Fin 7)) :
    nePermW (neRows conjTab L) u = gpack (Gen.neActPermG conjTab L u) := by
  rw [nePermW_eq hb u]
  apply orN_congr
  intro i hi
  rw [actPerm_getD u hi]

end Perm

private theorem nePermsK_eq (R : Nat) :
    ∀ ws : List (List (Fin 7)), nePermsK R ws = ws.map (nePermW R)
  | [] => rfl
  | u :: ws => by
    change nePermW R u :: nePermsK R ws = _
    rw [nePermsK_eq R ws]
    rfl

private theorem neNodup_spec : ∀ Vs : List Nat, neNodup Vs = true → Vs.Nodup
  | [], _ => List.nodup_nil
  | U :: rest, h => by
    change andB (neAllL (fun V => notB (Nat.beq U V)) rest) (neNodup rest) = true at h
    rw [andB_eq', Bool.and_eq_true, neAllL_eq, List.all_eq_true] at h
    refine List.nodup_cons.2 ⟨fun hm => ?_, neNodup_spec rest h.2⟩
    have := h.1 U hm
    rw [notB_eq', Nat.beq_refl] at this
    exact Bool.false_ne_true this

private noncomputable def hitF (r : List Nat) : Nat → Nat :=
  List.rec (motive := fun _ => Nat → Nat) (fun _ => nat_lit 0)
    (fun e _ ih n => Nat.rec (motive := fun _ => Nat) (nat_lit 0)
      (fun n' _ => Nat.lor (pw2 e) (ih n')) n) r

private theorem hitF_spec : ∀ (r : List Nat) (n j : Nat), (hitF r n).testBit j = true →
    ∃ i < n, r.getD i 0 = j
  | [], n, j, h => by
    change (0 : Nat).testBit j = true at h
    simp at h
  | _ :: _, 0, j, h => by
    change (0 : Nat).testBit j = true at h
    simp at h
  | e :: r, n + 1, j, h => by
    change (pw2 e ||| hitF r n).testBit j = true at h
    rw [Nat.testBit_or, pw2_eq', Nat.testBit_two_pow, Bool.or_eq_true, decide_eq_true_eq] at h
    rcases h with rfl | h
    · exact ⟨0, by omega, List.getD_cons_zero⟩
    · obtain ⟨i, hi, he⟩ := hitF_spec r n j h
      exact ⟨i + 1, by omega, by rw [List.getD_cons_succ]; exact he⟩

private theorem witMask_spec : ∀ (wit : List (ℕ × ℕ × ℕ)) (m : Nat),
    (neWitMask wit).testBit m = true → ∃ t ∈ wit, t.1 < 20 ∧ t.2.1 < 20 ∧ 20 * t.1 + t.2.1 = m
  | [], m, h => by
    change (0 : Nat).testBit m = true at h
    simp at h
  | (a, b, c) :: wit, m, h => by
    change (Bool.rec (motive := fun _ => Nat) 0 (pw2 (20 * a + b))
      (andB (Nat.blt a 20) (Nat.blt b 20)) ||| neWitMask wit).testBit m = true at h
    rw [Nat.testBit_or, Bool.or_eq_true] at h
    rcases h with h | h
    · cases hc : andB (Nat.blt a 20) (Nat.blt b 20)
      · rw [hc] at h
        change (0 : Nat).testBit m = true at h
        simp at h
      · rw [hc] at h
        change (pw2 (20 * a + b)).testBit m = true at h
        rw [pw2_eq', Nat.testBit_two_pow, decide_eq_true_eq] at h
        rw [andB_eq', Bool.and_eq_true] at hc
        exact ⟨(a, b, c), List.mem_cons_self, Nat.blt_eq.mp hc.1, Nat.blt_eq.mp hc.2, h⟩
    · obtain ⟨t, ht, h⟩ := witMask_spec wit m h
      exact ⟨t, List.mem_cons_of_mem _ ht, h⟩

private theorem testBit_of_land_pos {M m : Nat} (h : 0 < M &&& 2 ^ m) : M.testBit m = true := by
  cases hb : M.testBit m
  · have : M &&& 2 ^ m = 0 := Nat.eq_of_testBit_eq fun b => by
      rw [Nat.testBit_and, Nat.testBit_two_pow, Nat.zero_testBit]
      by_cases hbm : m = b
      · subst hbm
        simp [hb]
      · simp [hbm]
    omega
  · rfl

private theorem act_letter : ∀ l : Fin 7, Nat.blt 0 (Nat.land 47 (pw2 l.val)) = true →
    l ∈ ([0, 1, 2, 3, 5] : List (Fin 7)) := by
  decide

private theorem orbit_letter : ∀ l : Fin 7, Nat.blt l.val 6 = true →
    l ∈ ([0, 1, 2, 3, 4, 5] : List (Fin 7)) := by
  decide

private theorem allL_spec {α : Type} {p : α → Bool} {ws : List (List α)}
    (h : neAllL (neAllL p) ws = true) : ∀ u ∈ ws, ∀ l ∈ u, p l = true := by
  intro u hu l hl
  rw [neAllL_eq, List.all_eq_true] at h
  have h' := h u hu
  rw [neAllL_eq, List.all_eq_true] at h'
  exact h' l hl

theorem ne_sound (mulTab conjTab : List (List ℕ)) (L : List (Fin 7))
    (actWords orbitWords : List (List (Fin 7))) (wit : List (ℕ × ℕ × ℕ)) (w : List (Fin 7))
    (h1 : kAct mulTab conjTab L actWords orbitWords wit = true) (h2 : kW0 conjTab L w = true) :
    Gen.neActCheckG conjTab L mulTab actWords orbitWords wit = true ∧
      Gen.neW0CheckG conjTab L w = true := by
  simp only [kAct, andB_eq', Bool.and_eq_true, neStrictB_eq] at h1
  obtain ⟨hbM, hbC, hhit, hact, horb, hnd, hlen1, hlen2, hwit⟩ := h1
  have hbM' := neBoundK_spec hbM
  have hbC' := neBoundK_spec hbC
  constructor
  · unfold Gen.neActCheckG
    simp only [Bool.and_eq_true, List.all_eq_true, List.mem_range, decide_eq_true_eq]
    refine ⟨⟨⟨⟨⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩
    · intro j _ i _
      exact ⟨entry_lt (getD_bound hbM' j) i, entry_lt (getD_bound hbC' j) i⟩
    · intro k hk j hj
      have e := Nat.eq_of_beq_eq_true (allN_iff'.mp hhit k hk)
      have hbit : (hitF (neGet [] conjTab k) 64).testBit j = true := by
        change (neHit (neGet [] conjTab k)).testBit j = true
        rw [e, maskN_eq', Nat.testBit_two_pow_sub_one, decide_eq_true_eq]
        exact hj
      obtain ⟨i, hi, hv⟩ := hitF_spec _ 64 j hbit
      rw [neGet_eq] at hv
      rw [List.any_eq_true]
      exact ⟨i, List.mem_range.2 hi, beq_iff_eq.2 hv⟩
    · intro u hu l hl
      exact act_letter l (allL_spec hact u hu l hl)
    · intro u hu l hl
      exact orbit_letter l (allL_spec horb u hu l hl)
    · have h := neNodup_spec _ hnd
      rw [nePermsK_eq, show actWords.map (nePermW (neRows conjTab L)) =
          (actWords.map (Gen.neActPermG conjTab L)).map gpack by
        rw [List.map_map]
        exact List.map_congr_left fun u _ => nePermW_gpack hbC' u] at h
      exact List.Pairwise.of_map gpack (fun a b hab e => hab (congrArg gpack e)) h
    · rw [← neLen_eq]
      exact hlen1
    · rw [← neLen_eq]
      exact hlen2
    · intro k hk l hl
      have hh := allN_iff'.mp (allN_iff'.mp hwit k hk) l hl
      rw [orB_eq', notB_eq', Bool.or_eq_true] at hh
      rw [Bool.or_eq_true]
      by_cases hkl : k < l
      · right
        have hh2 : Nat.blt 0 (Nat.land (neWitMask wit) (pw2 (Nat.add (Nat.mul 20 k) l))) =
            true := hh.resolve_left (by rw [Nat.blt_eq.mpr hkl]; decide)
        have hh' : 0 < Nat.land (neWitMask wit) (pw2 (Nat.add (Nat.mul 20 k) l)) :=
          Nat.blt_eq.mp hh2
        rw [pw2_eq'] at hh'
        obtain ⟨t, ht, ha, hb, he⟩ := witMask_spec wit _ (testBit_of_land_pos hh')
        have he' : 20 * t.1 + t.2.1 = 20 * k + l := he
        rw [List.any_eq_true]
        refine ⟨t, ht, ?_⟩
        rw [Bool.and_eq_true, beq_iff_eq, beq_iff_eq]
        omega
      · left
        simp [hkl]
  · simp only [kW0, andB_eq', Bool.and_eq_true, neStrictB_eq] at h2
    obtain ⟨-, h2⟩ := h2
    unfold Gen.neW0CheckG
    simp only [List.all_eq_true, List.mem_range]
    intro i hi
    rcases i with _ | i
    · simp
    · have hh := allN_iff'.mp h2 i (by omega)
      rw [notB_eq'] at hh
      have key : fget (nePermW (neRows conjTab L) w) (i + 1) 6 =
          (Gen.neActPermG conjTab L w).getD (i + 1) 0 := by
        rw [nePermW_eq hbC', fget_orN (fun j hj => foldr_lt hbC' w hj) hi, actPerm_getD w hi]
      have hne : (Gen.neActPermG conjTab L w).getD (i + 1) 0 ≠ i + 1 := by
        intro e
        rw [← key] at e
        change (!Nat.beq (fget (nePermW (neRows conjTab L) w) (i + 1) 6) (i + 1)) = true at hh
        rw [e, Nat.beq_refl] at hh
        exact Bool.false_ne_true hh
      rw [Bool.or_eq_true]
      exact Or.inl (bne_iff_ne.2 hne)

end CFSG.KC.GMS

end

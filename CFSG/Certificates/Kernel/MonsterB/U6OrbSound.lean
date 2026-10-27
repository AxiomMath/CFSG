module

public import Certificates.Data.Kernel.MonsterB.U6Orb
public import CFSG.Certificates.Kernel.MonsterB.BfsReplaySound
public import Certificates.Data.CFSGNative.MonsterB.Co2Matrix

public section

namespace CFSG.KC.U6Orb

open CFSG.KLie.CT CFSG.KC.Loop CFSG.Monster.B.TwoA.Census

theorem andB_eq_true {a b : Bool} : andB a b = true ↔ a = true ∧ b = true := by
  cases a <;> simp [andB]

theorem notB_eq (a : Bool) : notB a = !a := by cases a <;> rfl

theorem strictB_eq (y : ℕ) (k : ℕ → Bool) : strictB y k = k y := by cases y <;> rfl

theorem pw2_eq (w : ℕ) : pw2 w = 2 ^ w := by
  change 1 <<< w = 2 ^ w
  rw [Nat.shiftLeft_eq, Nat.one_mul]

theorem fget_eq (X i w : ℕ) : fget X i w = X >>> (i * w) % 2 ^ w := by
  change (X >>> (i * w)) &&& (pw2 w - 1) = _
  rw [pw2_eq, Nat.and_two_pow_sub_one_eq_mod]

theorem bit_eq (X i : ℕ) : bit X i = X.testBit i := by
  have h1 : (X >>> i) &&& 1 = X / 2 ^ i % 2 := by
    rw [Nat.shiftRight_eq_div_pow]
    exact Nat.and_two_pow_sub_one_eq_mod _ 1
  change Nat.beq ((X >>> i) &&& 1) 1 = _
  rw [h1, Nat.testBit_eq_decide_div_mod_eq]
  rcases Nat.mod_two_eq_zero_or_one (X / 2 ^ i) with h | h <;> rw [h] <;> rfl

theorem allN_iff (n : ℕ) (f : ℕ → Bool) : allN n f = true ↔ ∀ i < n, f i = true := by
  induction n with
  | zero => simp [allN]
  | succ n ih =>
    change andB (f n) (allN n f) = true ↔ _
    rw [andB_eq_true, ih]
    constructor
    · rintro ⟨h1, h2⟩ i hi
      rcases Nat.lt_succ_iff_lt_or_eq.1 hi with hi | rfl
      · exact h2 i hi
      · exact h1
    · intro h
      exact ⟨h n (Nat.lt_succ_self n), fun i hi => h i (Nat.lt_succ_of_lt hi)⟩

theorem lenL_eq {α : Type} (L : List α) : lenL L = L.length := by
  induction L with
  | nil => rfl
  | cons x L ih => exact congrArg Nat.succ ih

theorem mapL_eq {α : Type} (f : α → ℕ) (L : List α) : mapL f L = L.map f := by
  induction L with
  | nil => rfl
  | cons x L ih => exact congrArg (List.cons (f x)) ih

theorem allL_iff {α : Type} (f : α → Bool) (L : List α) : allL f L = true ↔ ∀ x ∈ L, f x = true := by
  induction L with
  | nil => simp [allL]
  | cons x L ih =>
    change andB (f x) (allL f L) = true ↔ _
    rw [andB_eq_true, ih]
    simp

theorem boundL_iff (b : ℕ) (L : List ℕ) : boundL b L = true ↔ ∀ x ∈ L, x < b := by
  simp [boundL, allL_iff, Nat.blt_eq]

theorem shapeL_iff (n b : ℕ) (LL : List (Array ℕ)) :
    shapeL n b LL = true ↔ ∀ a ∈ LL, a.size = n ∧ ∀ x ∈ a.toList, x < b := by
  simp only [shapeL, allL_iff, andB_eq_true, Nat.beq_eq, lenL_eq, boundL_iff, Array.length_toList]

theorem packL_cons (w x : ℕ) (L : List ℕ) : packL w (x :: L) = x ||| (packL w L <<< w) := rfl

theorem or_shl_eq {x y w : ℕ} (hx : x < 2 ^ w) : x ||| (y <<< w) = y * 2 ^ w + x := by
  rw [Nat.or_comm, ← Nat.shiftLeft_add_eq_or_of_lt hx, Nat.shiftLeft_eq]

theorem packL_lt {w : ℕ} : ∀ {L : List ℕ}, (∀ x ∈ L, x < 2 ^ w) → packL w L < 2 ^ (w * L.length)
  | [], _ => by simp [packL]
  | x :: L, h => by
    rw [packL_cons, or_shl_eq (h x (by simp))]
    have ih := packL_lt (L := L) (fun y hy => h y (by simp [hy]))
    have hx := h x (by simp)
    have : 2 ^ (w * (x :: L).length) = 2 ^ (w * L.length) * 2 ^ w := by
      rw [List.length_cons, Nat.mul_succ, Nat.pow_add]
    rw [this]
    calc packL w L * 2 ^ w + x < packL w L * 2 ^ w + 2 ^ w := by omega
      _ = (packL w L + 1) * 2 ^ w := (Nat.succ_mul _ _).symm
      _ ≤ 2 ^ (w * L.length) * 2 ^ w := Nat.mul_le_mul_right _ ih

theorem fget_packL {w : ℕ} : ∀ {L : List ℕ}, (∀ x ∈ L, x < 2 ^ w) →
    ∀ i (hi : i < L.length), fget (packL w L) i w = L[i]
  | [], _, i, hi => by simp at hi
  | x :: L, h, i, hi => by
    rw [packL_cons, or_shl_eq (h x (by simp)), fget_eq]
    rcases i with _ | i
    · simp only [Nat.zero_mul, Nat.shiftRight_zero, List.getElem_cons_zero]
      rw [Nat.mul_comm, Nat.mul_add_mod]
      exact Nat.mod_eq_of_lt (h x (by simp))
    · have hw : (packL w L * 2 ^ w + x) >>> ((i + 1) * w) = packL w L >>> (i * w) := by
        rw [Nat.add_mul, Nat.one_mul, Nat.add_comm (i * w), Nat.shiftRight_add,
          Nat.shiftRight_eq_div_pow (packL w L * 2 ^ w + x) w]
        rw [Nat.add_comm, Nat.add_mul_div_right _ _ (Nat.two_pow_pos w),
          Nat.div_eq_of_lt (h x (by simp)), Nat.zero_add]
      rw [hw, ← fget_eq, List.getElem_cons_succ]
      exact fget_packL (fun y hy => h y (by simp [hy])) i (by simpa using hi)

theorem getElem!_toList {α : Type} [Inhabited α] (a : Array α) {i : ℕ} (hi : i < a.size) :
    a[i]! = a.toList[i]'(by simpa using hi) := by
  rw [getElem!_pos a i hi, Array.getElem_toList]

theorem fget_packA {w : ℕ} {a : Array ℕ} (h : ∀ x ∈ a.toList, x < 2 ^ w) {i : ℕ}
    (hi : i < a.size) : fget (packL w a.toList) i w = a[i]! := by
  rw [fget_packL h i (by simpa using hi), getElem!_toList a hi]

theorem nodupM_cons (x : ℕ) (L : List ℕ) (M : ℕ) :
    nodupM (x :: L) M = andB (notB (bit M x)) (nodupM L (M ||| pw2 x)) := by
  change andB (notB (bit M x)) (strictB (Nat.lor M (pw2 x)) (nodupM L)) = _
  rw [strictB_eq]
  rfl

theorem nodupM_spec : ∀ (L : List ℕ) (M : ℕ), nodupM L M = true →
    L.Nodup ∧ ∀ x ∈ L, M.testBit x = false
  | [], _, _ => by simp
  | x :: L, M, h => by
    rw [nodupM_cons, andB_eq_true, notB_eq, bit_eq, pw2_eq] at h
    obtain ⟨h1, h2⟩ := h
    obtain ⟨hnd, hb⟩ := nodupM_spec L _ h2
    have h1' : M.testBit x = false := by simpa using h1
    refine ⟨List.nodup_cons.2 ⟨fun hx => ?_, hnd⟩, fun y hy => ?_⟩
    · have := hb x hx
      simp [Nat.testBit_or, Nat.testBit_two_pow_self] at this
    · rcases List.mem_cons.1 hy with rfl | hy
      · exact h1'
      · have := hb y hy
        rw [Nat.testBit_or] at this
        simp only [Bool.or_eq_false_iff] at this
        exact this.1

theorem xorK_succ (n : ℕ) (f : ℕ → ℕ) : xorK (n + 1) f = f n ^^^ xorK n f := rfl

theorem xorK_congr {n : ℕ} {f g : ℕ → ℕ} (h : ∀ i < n, f i = g i) : xorK n f = xorK n g := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [xorK_succ, xorK_succ, h n (Nat.lt_succ_self n), ih fun i hi => h i (Nat.lt_succ_of_lt hi)]

theorem actGo_eq (rows : Array ℕ) (v : ℕ) : ∀ d acc,
    CFSG.Monster.VisCert.Native.actGo rows v d acc =
      acc ^^^ xorK d (fun t => if v.testBit t then rows[t]! else 0)
  | 0, acc => by simp [CFSG.Monster.VisCert.Native.actGo, xorK]
  | d + 1, acc => by
    rw [CFSG.Monster.VisCert.Native.actGo, actGo_eq rows v d, xorK_succ]
    split <;> simp_all [Nat.xor_assoc]

theorem actD_eq_actK {rows : Array ℕ} (hs : rows.size = 22) (hb : ∀ x ∈ rows.toList, x < 2 ^ 22)
    (v : ℕ) : CFSG.Monster.B.Co2.Native.actD 22 rows v = actK (packL 22 rows.toList) v := by
  rw [CFSG.Monster.B.Co2.Native.actD, actGo_eq, Nat.zero_xor]
  refine xorK_congr fun t ht => ?_
  rw [bit_eq, fget_packA hb (by omega)]
  cases v.testBit t <;> rfl

theorem vec_lt {L : Array ℕ} (h : boundL (pw2 22) L.toList = true) :
    ∀ j < L.size, L[j]! < 2 ^ 22 := by
  intro j hj
  rw [getElem!_toList L hj]
  exact (boundL_iff _ _).1 h _ (List.getElem_mem _) |>.trans_eq (pw2_eq 22)

theorem vec_inj {L : Array ℕ} (h : L.toList.Nodup) :
    ∀ i < L.size, ∀ j < L.size, L[i]! = L[j]! → i = j := by
  intro i hi j hj e
  rw [getElem!_toList L hi, getElem!_toList L hj] at e
  exact (List.Nodup.getElem_inj_iff h).1 e

theorem perm_lt {P : Array (Array ℕ)} {n b : ℕ} (h : shapeL n b P.toList = true) :
    ∀ k < P.size, P[k]!.size = n ∧ ∀ j < n, P[k]![j]! < b := by
  intro k hk
  have hm : P[k]! ∈ P.toList := by
    rw [getElem!_toList P hk]
    exact List.getElem_mem _
  obtain ⟨hs, hb⟩ := (shapeL_iff n b _).1 h _ hm
  refine ⟨hs, fun j hj => ?_⟩
  rw [getElem!_toList _ (by omega)]
  exact hb _ (List.getElem_mem _)

theorem packR_get {R : Array (Array ℕ)} (h : shapeL 22 (pw2 22) R.toList = true) {k : ℕ}
    (hk : k < R.size) :
    fget (packL 484 (mapL (fun a => packL 22 a.toList) R.toList)) k 484 =
      packL 22 R[k]!.toList := by
  have hall : ∀ a ∈ R.toList, a.size = 22 ∧ ∀ x ∈ a.toList, x < 2 ^ 22 := by
    intro a ha
    have := (shapeL_iff _ _ _).1 h a ha
    rw [pw2_eq] at this
    exact this
  have hlt : ∀ x ∈ R.toList.map (fun a => packL 22 a.toList), x < 2 ^ 484 := by
    intro x hx
    obtain ⟨a, ha, rfl⟩ := List.mem_map.1 hx
    have := packL_lt (w := 22) (hall a ha).2
    have e : (22 : ℕ) * 22 = 484 := rfl
    rwa [Array.length_toList, (hall a ha).1, e] at this
  rw [mapL_eq, fget_packL hlt k (by simpa using hk), List.getElem_map, getElem!_toList R hk]

theorem packP_get {P : Array (Array ℕ)} {n w : ℕ} (hn : n ≤ 2 ^ w)
    (h : shapeL n n P.toList = true) {k : ℕ} (hk : k < P.size) {i : ℕ} (hi : i < n) :
    permTab n w (packP n w P.toList) i k = P[k]![i]! := by
  have hall : ∀ a ∈ P.toList, a.size = n ∧ ∀ x ∈ a.toList, x < 2 ^ w := by
    intro a ha
    obtain ⟨h1, h2⟩ := (shapeL_iff _ _ _).1 h a ha
    exact ⟨h1, fun x hx => lt_of_lt_of_le (h2 x hx) hn⟩
  have hlt : ∀ x ∈ P.toList.map (fun a => packL w a.toList), x < 2 ^ (n * w) := by
    intro x hx
    obtain ⟨a, ha, rfl⟩ := List.mem_map.1 hx
    have := packL_lt (w := w) (hall a ha).2
    rwa [Array.length_toList, (hall a ha).1, Nat.mul_comm] at this
  have hk' : P[k]! ∈ P.toList := by
    rw [getElem!_toList P hk]
    exact List.getElem_mem _
  rw [permTab, packP, mapL_eq]
  change fget (fget (packL (n * w) _) k (n * w)) i w = _
  rw [fget_packL hlt k (by simpa using hk), List.getElem_map, ← getElem!_toList P hk,
    fget_packA (hall _ hk').2 (by rw [(hall _ hk').1]; exact hi)]

theorem edge_sound {L : Array ℕ} {R : Array (Array ℕ)} {D : ℕ} {Ef : ℕ → ℕ → ℕ → ℕ} {n ng : ℕ}
    (hn : L.size = n) (hng : R.size = ng) (hL : boundL (pw2 22) L.toList = true)
    (hR : shapeL 22 (pw2 22) R.toList = true) (h : edgeLOK L.toList R.toList D Ef n ng = true) :
    ∀ i < n, ∀ k < ng, Ef D i k < n ∧
      L[Ef D i k]! = CFSG.Monster.B.Co2.Native.actD 22 R[k]! L[i]! := by
  intro i hi k hk
  simp only [edgeLOK, strictB_eq, edgeOK, allN_iff] at h
  have h' := h i hi k hk
  rw [andB_eq_true, Nat.blt_eq, Nat.beq_eq] at h'
  have hLb : ∀ x ∈ L.toList, x < 2 ^ 22 := fun x hx => by
    have := (boundL_iff _ _).1 hL x hx
    rwa [pw2_eq] at this
  obtain ⟨hR1, hR2⟩ := perm_lt hR k (by omega)
  have hRb : ∀ x ∈ R[k]!.toList, x < 2 ^ 22 := by
    intro x hx
    obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hx
    rw [Array.getElem_toList, ← getElem!_pos _ j (by simpa using hj)]
    have := hR2 j (by simpa [hR1] using hj)
    rwa [pw2_eq] at this
  refine ⟨h'.1, ?_⟩
  rw [packR_get hR (by omega), fget_packA hLb (by omega), fget_packA hLb (by omega)] at h'
  rw [h'.2, actD_eq_actK hR1 hRb]

theorem strictN_eq (y : ℕ) (k : ℕ → ℕ) : strictN y k = k y := by cases y <;> rfl

theorem memOK_sound {L : Array ℕ} {s X wX I wI n m c : ℕ} (hm : L.size = m)
    (hL : boundL (pw2 22) L.toList = true) (h : memOK L.toList s X wX I wI n m c = true) :
    ∀ j < m, (∃ t < n, fget X t wX = s ^^^ L[j]!) ∧ s ^^^ L[j]! < 2 ^ 22 ∧
      s ^^^ L[j]! ≠ c := by
  subst hm
  intro j hj
  simp only [memOK, strictB_eq, allN_iff] at h
  have h' := h j hj
  have hLb : ∀ x ∈ L.toList, x < 2 ^ 22 := fun x hx => by
    have := (boundL_iff _ _).1 hL x hx
    rwa [pw2_eq] at this
  rw [fget_packA hLb hj] at h'
  simp only [andB_eq_true, Nat.blt_eq, Nat.beq_eq, notB_eq, Bool.not_eq_true', pw2_eq] at h'
  refine ⟨⟨_, h'.1, h'.2.1⟩, h'.2.2.1, fun e => ?_⟩
  have h2 := h'.2.2.2
  have e' : Nat.xor s L[j]! = c := e
  rw [e', Nat.beq_refl] at h2
  exact absurd h2 (by decide)

theorem nodup_of_card_le {L : List ℕ} (h : L.length ≤ L.toFinset.card) : L.Nodup := by
  have h2 := List.toFinset_card_le L
  have e : (L : Multiset ℕ).toFinset.card = Multiset.card (L : Multiset ℕ) := by
    rw [Multiset.coe_card]
    exact le_antisymm h2 h
  exact Multiset.coe_nodup.1 (Multiset.toFinset_card_eq_card_iff_nodup.1 e)

theorem sortOK_sound {L : List ℕ} {S w n : ℕ} (h : sortOK L S w n = true) :
    L.Nodup ∧ ∀ x ∈ L, x < 2 ^ 22 := by
  simp only [sortOK, andB_eq_true, Nat.beq_eq, lenL_eq, strictB_eq, allN_iff] at h
  obtain ⟨hn, hb, h⟩ := h
  have hLb : ∀ x ∈ L, x < 2 ^ 22 := fun x hx => by
    have := (boundL_iff _ _).1 hb x hx
    rwa [pw2_eq] at this
  refine ⟨?_, hLb⟩
  have hS : ∀ t < n, fget S t w < L.length := fun t ht => by
    have := (h t ht).1
    rw [Nat.blt_eq] at this
    omega
  let g : ℕ → ℕ := fun t => fget (packL 22 L) (fget S t w) 22
  have hstep : ∀ t, t + 1 < n → g t < g (t + 1) := fun t ht => by
    have := (h t (by omega)).2
    have hb' : Nat.blt t.succ n = true := by
      rw [Nat.blt_eq]
      exact ht
    rw [hb'] at this
    change Nat.blt _ _ = true at this
    rw [Nat.blt_eq] at this
    exact this
  have hmono : ∀ a b, a < b → b < n → g a < g b := by
    intro a b hab hb
    induction b with
    | zero => omega
    | succ b ih =>
      rcases Nat.lt_succ_iff_lt_or_eq.1 hab with h' | rfl
      · exact lt_trans (ih h' (by omega)) (hstep b hb)
      · exact hstep a hb
  have hinj : Set.InjOn g (Finset.range n : Set ℕ) := by
    intro a ha b hb e
    simp only [Finset.coe_range, Set.mem_Iio] at ha hb
    rcases lt_trichotomy a b with hab | rfl | hab
    · exact absurd e (ne_of_lt (hmono a b hab hb))
    · rfl
    · exact absurd e (ne_of_gt (hmono b a hab ha))
  have hsub : (Finset.range n).image g ⊆ L.toFinset := by
    intro y hy
    obtain ⟨t, ht, rfl⟩ := Finset.mem_image.1 hy
    rw [Finset.mem_range] at ht
    rw [List.mem_toFinset]
    change fget (packL 22 L) (fget S t w) 22 ∈ L
    rw [fget_packL hLb _ (hS t ht)]
    exact List.getElem_mem _
  apply nodup_of_card_le
  have := Finset.card_le_card hsub
  rw [Finset.card_image_of_injOn hinj, Finset.card_range] at this
  omega

theorem bfs_sound {L : Array ℕ} {R : Array (Array ℕ)} {D : ℕ} {Ef : ℕ → ℕ → ℕ → ℕ}
    {n ng root fuel : ℕ} {act : ℕ → ℕ → ℕ}
    (hact : ∀ k a, act k a = CFSG.Monster.B.Co2.Native.actD 22 R[k]! a)
    (hn : L.size = n) (hpos : 0 < n) (hng : R.size = ng) (h0 : L[0]! = root) (hfuel : n ≤ fuel)
    (hL : boundL (pw2 22) L.toList = true) (hd : L.toList.Nodup)
    (hR : shapeL 22 (pw2 22) R.toList = true) (he : edgeLOK L.toList R.toList D Ef n ng = true)
    (hr : replayDOK D Ef ng n = true) :
    natCertOK act ng (fun a => decide (a < 2 ^ 22)) root (natBfs act ng root fuel) = true ∧
      (natBfs act ng root fuel).pts = L := by
  have hE := edge_sound hn hng hL hR he
  rw [replayDOK, strictB_eq] at hr
  subst hn
  obtain ⟨h1, h2⟩ := CFSG.KC.Bfs.natBfs_of_replay (act := act) (valid := fun a => decide (a < 2 ^ 22))
    (E := Ef D) hpos h0 (vec_inj hd) (fun i hi k hk => by rw [hact]; exact hE i hi k hk) hr
    (fun j hj => by simpa using vec_lt hL j hj) hfuel
  exact ⟨h2, h1⟩

end CFSG.KC.U6Orb

end

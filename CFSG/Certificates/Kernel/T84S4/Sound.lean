module

public import Certificates.Data.Kernel.T84S4.Check

public section

namespace CFSG.KD.T84S4

theorem recB_all (P : Nat → Bool) : ∀ n : Nat,
    Nat.rec (motive := fun _ => Bool) true (fun t ih => Bool.and ih (P t)) n = true →
      ∀ t < n, P t = true
  | 0, _, t, ht => absurd ht (Nat.not_lt_zero t)
  | n + 1, h, t, ht => by
    have h' : Bool.and (Nat.rec (motive := fun _ => Bool) true (fun t ih => Bool.and ih (P t)) n)
        (P n) = true := h
    rw [Bool.and_eq_true] at h'
    rcases Nat.lt_succ_iff_lt_or_eq.1 ht with ht | ht
    · exact recB_all P n h'.1 t ht
    · rw [ht]
      exact h'.2

theorem recB_any (P : Nat → Bool) : ∀ n : Nat,
    Nat.rec (motive := fun _ => Bool) false (fun t ih => Bool.or ih (P t)) n = true →
      ∃ t < n, P t = true
  | 0, h => absurd h Bool.false_ne_true
  | n + 1, h => by
    have h' : Bool.or (Nat.rec (motive := fun _ => Bool) false (fun t ih => Bool.or ih (P t)) n)
        (P n) = true := h
    rw [Bool.or_eq_true] at h'
    rcases h' with h' | h'
    · obtain ⟨t, ht, hp⟩ := recB_any P n h'
      exact ⟨t, Nat.lt_succ_of_lt ht, hp⟩
    · exact ⟨n, Nat.lt_succ_self n, h'⟩

theorem recL_all (P : Nat → Bool) : ∀ l : List Nat,
    List.rec (motive := fun _ => Bool) true (fun y _ ih => Bool.and (P y) ih) l = true →
      ∀ y ∈ l, P y = true
  | [], _, y, hy => absurd hy List.not_mem_nil
  | x :: l, h, y, hy => by
    have h' : Bool.and (P x)
        (List.rec (motive := fun _ => Bool) true (fun y _ ih => Bool.and (P y) ih) l) = true := h
    rw [Bool.and_eq_true] at h'
    rcases List.mem_cons.1 hy with hy | hy
    · rw [hy]
      exact h'.1
    · exact recL_all P l h'.2 y hy

theorem recL_all' (P : Nat → Bool) : ∀ l : List Nat,
    List.rec (motive := fun _ => Bool) true (fun y _ ih => Bool.and ih (P y)) l = true →
      ∀ y ∈ l, P y = true
  | [], _, y, hy => absurd hy List.not_mem_nil
  | x :: l, h, y, hy => by
    have h' : Bool.and
        (List.rec (motive := fun _ => Bool) true (fun y _ ih => Bool.and ih (P y)) l) (P x) = true :=
      h
    rw [Bool.and_eq_true] at h'
    rcases List.mem_cons.1 hy with hy | hy
    · rw [hy]
      exact h'.2
    · exact recL_all' P l h'.1 y hy

open CFSG.KC.Misc CFSG.KC.Misc.T84

theorem boundB_sound {ACT TM : Nat} (h : boundB ACT TM = true) :
    ∀ i < 192, ∀ j < 192, mI ACT TM i j < 192 := by
  unfold boundB at h
  generalize hN : (192 : Nat) = N at h
  intro i hi j hj
  have h2 := recB_all _ N (recB_all _ N h i hi) j hj
  subst hN
  simpa [Nat.blt_eq] using h2

theorem tabB_sound {ACT TM TC lo n : Nat} (h : tabB ACT TM TC lo n = true) :
    ∀ t < n, ∀ j < 192, mulT (eC TC (lo + t)) (eC TC j) = eC TC (mI ACT TM (lo + t) j) := by
  unfold tabB at h
  generalize hN : (192 : Nat) = N at h
  intro t ht j hj
  exact Nat.eq_of_beq_eq_true (recB_all _ N (recB_all _ n h t ht) j hj)

theorem injB_sound {TC : Nat} (h : injB TC = true) :
    ∀ i < 192, ∀ j < 192, eC TC i = eC TC j → i = j := by
  unfold injB at h
  generalize hN : (192 : Nat) = N at h
  intro i hi j hj he
  have h2 := recB_all _ N (recB_all _ N h i hi) j hj
  rw [Bool.or_eq_true] at h2
  rcases h2 with h2 | h2
  · exact Nat.eq_of_beq_eq_true h2
  · rw [he, Nat.beq_refl] at h2
    exact absurd h2 (by decide)

theorem jEqB_sound {TC : Nat} (h : jEqB TC = true) : ∀ i < 192, memJ (eC TC i) = jB i := by
  unfold jEqB at h
  generalize hN : (192 : Nat) = N at h
  intro i hi
  have h1 := recB_all _ N h i hi
  revert h1
  cases jB i <;> simp

theorem tcB_sound {TC : Nat} (h : tcB TC = true) : ∀ k < 12, memN (l16 TC k) S0L = true := by
  unfold tcB at h
  generalize hS : S0L = SL at h ⊢
  generalize hN : (12 : Nat) = N at h ⊢
  exact recB_all _ N h

theorem jkB_sound {TC : Nat} (h : jkB TC = true) : ∀ y ∈ JK, ∃ i < 192, Nat.beq (eC TC i) y = true := by
  unfold jkB at h
  generalize hK : JK = K at h ⊢
  generalize hN : (192 : Nat) = N at h ⊢
  intro y hy
  exact recB_any _ N (recL_all _ _ h y hy)

theorem invB_sound {ACT TM INV : Nat} (h : invB ACT TM INV = true) :
    ∀ i < 192, l8 INV i < 192 ∧ mI ACT TM i (l8 INV i) = 0 := by
  unfold invB at h
  generalize hN : (192 : Nat) = N at h
  intro i hi
  have h1 := recB_all _ N h i hi
  subst hN
  rw [Bool.and_eq_true] at h1
  exact ⟨by simpa [Nat.blt_eq] using h1.1, Nat.eq_of_beq_eq_true h1.2⟩

theorem normB_sound {ACT TM INV : Nat} (h : normB ACT TM INV = true) :
    ∀ i < 192, ∀ j < 192, jB j = true → jB (mI ACT TM (mI ACT TM i j) (l8 INV i)) = true := by
  unfold normB at h
  generalize hN : (192 : Nat) = N at h
  intro i hi j hj hJ
  have h1 := recB_all _ N (recB_all _ N h i hi) j hj
  revert h1
  rw [hJ]
  exact id

theorem gen3B_sound {ACT TM : Nat} (h : gen3B ACT TM = true) :
    mI ACT TM (mI ACT TM 191 191) 191 = 0 ∧ ∀ i < 192, mI ACT TM (mI ACT TM i i) i = 0 ∨
      mI ACT TM (mI ACT TM (mI ACT TM i 191) (mI ACT TM i 191)) (mI ACT TM i 191) = 0 := by
  unfold gen3B at h
  rw [Bool.and_eq_true] at h
  refine ⟨Nat.eq_of_beq_eq_true h.1, fun i hi => ?_⟩
  have h0 := h.2
  generalize hN : (192 : Nat) = N at h0
  have h1 := recB_all _ N h0 i (hN ▸ hi)
  rw [Bool.or_eq_true] at h1
  rcases h1 with h1 | h1
  · exact Or.inl (Nat.eq_of_beq_eq_true h1)
  · exact Or.inr (Nat.eq_of_beq_eq_true h1)

theorem fpfB_sound {ACT TM : Nat} (h : fpfB ACT TM = true) :
    ∀ i < 192, 0 < i → mI ACT TM (mI ACT TM i i) i = 0 → ∀ j < 192, jB j = true →
      mI ACT TM i j = mI ACT TM j i → j = 0 := by
  unfold fpfB at h
  generalize hN : (192 : Nat) = N at h
  intro i hi hi0 h3 j hj hJ hc
  have h1 := recB_all _ N h i hi
  have hb : Bool.and (Nat.blt 0 i) (Nat.beq (mI ACT TM (mI ACT TM i i) i) 0) = true := by
    rw [Bool.and_eq_true, h3]
    exact ⟨by simpa [Nat.blt_eq] using hi0, Nat.beq_refl 0⟩
  revert h1
  rw [hb]
  intro h1
  have h2 := recB_all _ N h1 j hj
  revert h2
  rw [hJ, hc, Nat.beq_refl]
  intro h2
  simpa using h2

theorem oddB_sound {TC lo n : Nat} (h : oddB TC lo n = true) :
    ∀ t < n, ∀ m ∈ S0L, oddOne TC (mkT (lo + t) m) = true := by
  unfold oddB at h
  generalize hS : S0L = SL at h ⊢
  intro t ht m hm
  exact recL_all' _ _ (recB_all _ n h t ht) m hm

theorem oddOne_sound {TC z : Nat} (h : oddOne TC z = true) (h1 : mulT z (pow44T z) = oneT)
    (h2 : memJ (mulT (mulT z (eC TC 50)) (pow44T z)) = true)
    (h3 : memJ (mulT (mulT z (eC TC 181)) (pow44T z)) = true)
    (h4 : memJ (mulT (mulT z (eC TC 158)) (pow44T z)) = true)
    (h5 : memJ (mulT (mulT z (eC TC 110)) (pow44T z)) = true) :
    ∃ k < 12, Nat.beq (hiT z) (l16 TC k) = true := by
  have hT : inTC TC z = true := by
    cases hx : inTC TC z
    · unfold oddOne at h
      simp [h1, h2, h3, h4, h5, hx] at h
    · rfl
  unfold inTC at hT
  generalize hN : (12 : Nat) = N at hT ⊢
  exact recB_any _ N hT

theorem recL_any (P : Nat → Bool) : ∀ l : List Nat,
    List.rec (motive := fun _ => Bool) false (fun y _ ih => Bool.or (P y) ih) l = true →
      ∃ y ∈ l, P y = true
  | [], h => absurd h Bool.false_ne_true
  | x :: l, h => by
    have h' : Bool.or (P x)
        (List.rec (motive := fun _ => Bool) false (fun y _ ih => Bool.or (P y) ih) l) = true := h
    rw [Bool.or_eq_true] at h'
    rcases h' with h' | h'
    · exact ⟨x, List.mem_cons.2 (Or.inl rfl), h'⟩
    · obtain ⟨y, hy, hp⟩ := recL_any P l h'
      exact ⟨y, List.mem_cons_of_mem _ hy, hp⟩

theorem inL_iff (x : Nat) : ∀ l : List Nat, inL x l = true ↔ x ∈ l
  | [] => ⟨fun h => absurd h Bool.false_ne_true, fun h => absurd h List.not_mem_nil⟩
  | y :: l => by
    have e : inL x (y :: l) = Bool.or (Nat.beq x y) (inL x l) := rfl
    rw [e, Bool.or_eq_true, inL_iff x l, List.mem_cons]
    constructor
    · rintro (h | h)
      · exact Or.inl (Nat.eq_of_beq_eq_true h)
      · exact Or.inr h
    · rintro (h | h)
      · rw [h]
        exact Or.inl (Nat.beq_refl y)
      · exact Or.inr h

theorem setB_sound {p : Nat → Bool} {l : List Nat} {n : Nat} (h : setB p l n = true) :
    ∀ x < n, (x ∈ l ↔ p x = true) := by
  unfold setB at h
  intro x hx
  have h1 := recB_all _ n h x hx
  rw [← inL_iff]
  revert h1
  cases p x <;> cases inL x l <;> decide

theorem sel_hom {f : Nat → Nat} (hf0 : f 0 = 0) (d a b c : Nat) :
    f (sel d a b c) = sel d (f a) (f b) (f c) := by
  unfold sel
  cases Nat.beq d 3 <;> cases Nat.beq d 2 <;> cases Nat.beq d 1 <;> first | exact hf0 | rfl

theorem sel_lt {d a b c : Nat} (ha : a < 192) (hb : b < 192) (hc : c < 192) :
    sel d a b c < 192 := by
  unfold sel
  cases Nat.beq d 3 <;> cases Nat.beq d 2 <;> cases Nat.beq d 1 <;>
    first | exact ha | exact hb | exact hc | exact (by decide : (0 : Nat) < 192)

theorem evR_hom {ACT TM a b c : Nat} {f : Nat → Nat} (hb : boundB ACT TM = true)
    (hf0 : f 0 = 0) (hf : ∀ i < 192, ∀ j < 192, f (mI ACT TM i j) = mI ACT TM (f i) (f j))
    (ha : a < 192) (hb' : b < 192) (hc : c < 192) : ∀ n acc w, acc < 192 →
      f (Nat.rec (motive := fun _ => Nat → Nat → Nat) (fun acc _ => acc)
        (fun _ ih acc w => ih (mI ACT TM acc (sel (Nat.land w 3) a b c)) (Nat.shiftRight w 2))
        n acc w) =
      Nat.rec (motive := fun _ => Nat → Nat → Nat) (fun acc _ => acc)
        (fun _ ih acc w => ih (mI ACT TM acc (sel (Nat.land w 3) (f a) (f b) (f c)))
          (Nat.shiftRight w 2)) n (f acc) w
  | 0, _, _, _ => rfl
  | n + 1, acc, w, h => by
    have h1 := evR_hom hb hf0 hf ha hb' hc n (mI ACT TM acc (sel (Nat.land w 3) a b c))
      (Nat.shiftRight w 2) (boundB_sound hb _ h _ (sel_lt ha hb' hc))
    rw [hf _ h _ (sel_lt ha hb' hc), sel_hom hf0] at h1
    exact h1

theorem ev2_hom {ACT TM a b c : Nat} {f : Nat → Nat} (hb : boundB ACT TM = true)
    (hf0 : f 0 = 0) (hf : ∀ i < 192, ∀ j < 192, f (mI ACT TM i j) = mI ACT TM (f i) (f j))
    (ha : a < 192) (hb' : b < 192) (hc : c < 192) (w : Nat) :
    f (ev2 ACT TM a b c w) = ev2 ACT TM (f a) (f b) (f c) w := by
  have h := evR_hom hb hf0 hf ha hb' hc 9 0 w (by decide)
  rw [hf0] at h
  exact h

theorem natRec_succ_t84 {α : Sort _} (h0 : α) (h : Nat → α → α) (n : Nat) :
    Nat.rec (motive := fun _ => α) h0 h (n + 1) = h n (Nat.rec (motive := fun _ => α) h0 h n) :=
  rfl

theorem fixR_sound (Q P : Nat → Bool) (X : Nat → Nat) : ∀ n,
    (Nat.rec (motive := fun _ => Nat × Bool) (0, true)
      (fun t ih => (fun x => Bool.rec ih (Nat.succ ih.1, Bool.and ih.2 (P x)) (Q x)) (X t)) n).1 =
      ((List.range n).filter fun t => Q (X t)).length ∧
    ((∀ t < n, Q (X t) = true → P (X t) = true) →
      (Nat.rec (motive := fun _ => Nat × Bool) (0, true)
        (fun t ih => (fun x => Bool.rec ih (Nat.succ ih.1, Bool.and ih.2 (P x)) (Q x)) (X t))
          n).2 = true)
  | 0 => ⟨rfl, fun _ => rfl⟩
  | n + 1 => by
    obtain ⟨ih1, ih2⟩ := fixR_sound Q P X n
    simp only [natRec_succ_t84]
    rw [List.range_succ, List.filter_append, List.length_append, ← ih1]
    cases hq : Q (X n)
    · refine ⟨by simp [hq], fun H => ih2 fun t ht => H t (Nat.lt_succ_of_lt ht)⟩
    · refine ⟨by simp [hq], fun H => ?_⟩
      change Bool.and _ _ = true
      rw [Bool.and_eq_true]
      exact ⟨ih2 fun t ht => H t (Nat.lt_succ_of_lt ht), H n (Nat.lt_succ_self n) hq⟩

theorem jB_count (g : Nat → Bool) : ((List.range 192).filter fun x => jB x && g x).length =
    ((List.range 64).filter fun t =>
      g (Nat.add (Nat.mul 12 (Nat.div t 4)) (Nat.mod t 4))).length := by
  have e : (List.range 192).filter jB =
      (List.range 64).map fun t => Nat.add (Nat.mul 12 (Nat.div t 4)) (Nat.mod t 4) := by
    decide +kernel
  have e2 : ((List.range 192).filter fun x => jB x && g x) =
      ((List.range 192).filter jB).filter g := by
    rw [List.filter_filter]
    exact List.filter_congr fun x _ => Bool.and_comm _ _
  rw [e2, e, List.filter_map, List.length_map]
  rfl

theorem nbeq_eq (a b : Nat) : Nat.beq a b = (a == b) :=
  Bool.eq_iff_iff.2 ⟨fun h => beq_iff_eq.2 (Nat.eq_of_beq_eq_true h), fun h => by
    rw [beq_iff_eq.1 h]
    exact Nat.beq_refl b⟩

theorem sOf_mem {ACT TM a c : Nat} (h0 : ev2 ACT TM a 0 c 3549 = 0) :
    ∀ l : List Nat, c ∈ l → c ∈ sOf ACT TM a l
  | [], h => absurd h List.not_mem_nil
  | y :: l, h => by
    have e : sOf ACT TM a (y :: l) = Bool.rec (motive := fun _ => List Nat) (sOf ACT TM a l)
        (y :: sOf ACT TM a l) (Nat.beq (ev2 ACT TM a 0 y 3549) 0) := rfl
    rw [e]
    rcases List.mem_cons.1 h with h | h
    · rw [← h, h0, Nat.beq_refl]
      exact List.mem_cons.2 (Or.inl rfl)
    · have ih := sOf_mem h0 l h
      cases Nat.beq (ev2 ACT TM a 0 y 3549) 0
      · exact ih
      · exact List.mem_cons_of_mem _ ih

theorem finK2_sound {ACT TM WP : Nat} {L3 : List Nat} {a b c : Nat}
    (h : finK2 ACT TM WP L3 a b c = true) (h1 : phi2 ACT TM WP a b c a = 191)
    (h2 : phi2 ACT TM WP a b c b = 169) (h3 : phi2 ACT TM WP a b c c = 156)
    (h4 : (fixJ2 ACT TM WP a b c).1 = 4) (h5 : (fixJ2 ACT TM WP a b c).2 = true) :
    anyY2 ACT TM WP a b c L3 = true := by
  unfold finK2 at h
  dsimp only at h
  rw [h1, h2, h3, h4, h5, Nat.beq_refl, Nat.beq_refl, Nat.beq_refl, Nat.beq_refl] at h
  exact h

theorem ev_1446 (ACT TM a b : Nat) : ev2 ACT TM a b 0 1446 = mI ACT TM (mI ACT TM (mI ACT TM
    (mI ACT TM (mI ACT TM (mI ACT TM (mI ACT TM (mI ACT TM (mI ACT TM 0 b) a) b) b) a) a) 0) 0)
    0 := rfl

theorem ev_243110 (ACT TM a b c : Nat) : ev2 ACT TM a b c 243110 = mI ACT TM (mI ACT TM
    (mI ACT TM (mI ACT TM (mI ACT TM (mI ACT TM (mI ACT TM (mI ACT TM (mI ACT TM 0 b) a) b) b) a)
      a) c) b) c := rfl

theorem enum_sound {ACT TM WP : Nat} {L3 L4 I2 : List Nat} {SS : List (List Nat)}
    (hl : listB ACT TM L3 L4 I2 = true) (hw : wordsB ACT TM WP = true)
    (hr : relsB ACT TM = true) (hb : boundB ACT TM = true)
    (hid : ∀ i < 192, mI ACT TM i 0 = i) (hcut : SS.flatten = L3)
    (he : ∀ S ∈ SS, enumB ACT TM WP L3 L4 I2 S = true)
    (f : Nat → Nat) (hf1 : ∀ i < 192, f i < 192) (hf0 : f 0 = 0)
    (hf : ∀ i < 192, ∀ j < 192, f (mI ACT TM i j) = mI ACT TM (f i) (f j))
    (hff : ∀ i < 192, f (f i) = i)
    (hcard : ((List.range 192).filter fun x => jB x && f x == x).length = 4)
    (hel : ∀ i < 192, jB i = true → f i = i → mI ACT TM i i = 0) :
    ∃ y < 192, y ≠ 0 ∧ mI ACT TM (mI ACT TM y y) y = 0 ∧ f y = y := by
  have bnd := boundB_sound hb
  have h191 : (191 : Nat) < 192 := by decide
  have h169 : (169 : Nat) < 192 := by decide
  have h156 : (156 : Nat) < 192 := by decide
  have ha := hf1 191 h191
  have hb4 := hf1 169 h169
  have hc2 := hf1 156 h156
  unfold listB at hl
  simp only [Bool.and_eq_true] at hl
  obtain ⟨hl3, hl4, hl2, hlt⟩ := hl
  have m3 := setB_sound hl3
  have m4 := setB_sound hl4
  have m2 := setB_sound hl2
  have hlt' := recL_all _ _ hlt
  unfold relsB at hr
  simp only [Bool.and_eq_true] at hr
  obtain ⟨r1, r2, r3, r4, r5, r6, r7⟩ := hr
  have hw' : ∀ x < 192, Nat.beq (phi2 ACT TM WP 191 169 156 x) x = true := by
    unfold wordsB at hw
    generalize hN : (192 : Nat) = N at hw
    intro x hx
    exact recB_all _ N hw x hx
  have hev : ∀ w, ev2 ACT TM (f 191) (f 169) (f 156) w = f (ev2 ACT TM 191 169 156 w) :=
    fun w => (ev2_hom hb hf0 hf h191 h169 h156 w).symm
  have hphi : ∀ x < 192, phi2 ACT TM WP (f 191) (f 169) (f 156) x = f x := by
    intro x hx
    unfold phi2
    rw [hev]
    exact congrArg f (Nat.eq_of_beq_eq_true (hw' x hx))
  have hfm : ∀ i < 192, ∀ j < 192, mI ACT TM (f i) (f j) = f (mI ACT TM i j) :=
    fun i hi j hj => (hf i hi j hj).symm
  have ha3 : f 191 ∈ L3 := by
    refine (m3 _ ha).2 ?_
    rw [hfm 191 h191 191 h191, hfm _ (bnd 191 h191 191 h191) 191 h191,
      Nat.eq_of_beq_eq_true r1, hf0]
    exact Nat.beq_refl 0
  have hb44 : f 169 ∈ L4 := by
    refine (m4 _ hb4).2 ?_
    rw [hfm 169 h169 169 h169, hfm _ (bnd 169 h169 169 h169) _ (bnd 169 h169 169 h169),
      Nat.eq_of_beq_eq_true r2, hf0]
    exact Nat.beq_refl 0
  have hc22 : f 156 ∈ I2 := by
    refine (m2 _ hc2).2 ?_
    rw [hfm 156 h156 156 h156, Nat.eq_of_beq_eq_true r3, hf0]
    exact Nat.beq_refl 0
  have e170 : ev2 ACT TM (f 191) (f 169) 0 170 = 0 := by
    have e : ev2 ACT TM (f 191) (f 169) 0 170 = ev2 ACT TM (f 191) (f 169) (f 156) 170 := rfl
    rw [e, hev, Nat.eq_of_beq_eq_true r4, hf0]
  have e1638 : ev2 ACT TM (f 191) (f 169) 0 1638 = 0 := by
    have e : ev2 ACT TM (f 191) (f 169) 0 1638 = ev2 ACT TM (f 191) (f 169) (f 156) 1638 := rfl
    rw [e, hev, Nat.eq_of_beq_eq_true r5, hf0]
  have e3549 : ev2 ACT TM (f 191) 0 (f 156) 3549 = 0 := by
    have e : ev2 ACT TM (f 191) 0 (f 156) 3549 = ev2 ACT TM (f 191) (f 169) (f 156) 3549 := rfl
    rw [e, hev, Nat.eq_of_beq_eq_true r6, hf0]
  obtain ⟨S, hS, haS⟩ := List.mem_flatten.1 (by rw [hcut]; exact ha3 : f 191 ∈ SS.flatten)
  have hE : loopB2 ACT TM WP L3 L4 (f 191) (sOf ACT TM (f 191) I2) = true :=
    recL_all (fun a => loopB2 ACT TM WP L3 L4 a (sOf ACT TM a I2)) S (he S hS) _ haS
  have hB : Bool.rec (motive := fun _ => Bool) true
      (loopC2 ACT TM WP L3 (f 191) (f 169) (ev2 ACT TM (f 191) (f 169) 0 1446)
        (sOf ACT TM (f 191) I2))
      (Bool.and (Nat.beq (ev2 ACT TM (f 191) (f 169) 0 170) 0)
        (Nat.beq (ev2 ACT TM (f 191) (f 169) 0 1638) 0)) = true :=
    recL_all (fun b => Bool.rec (motive := fun _ => Bool) true
      (loopC2 ACT TM WP L3 (f 191) b (ev2 ACT TM (f 191) b 0 1446) (sOf ACT TM (f 191) I2))
      (Bool.and (Nat.beq (ev2 ACT TM (f 191) b 0 170) 0)
        (Nat.beq (ev2 ACT TM (f 191) b 0 1638) 0))) L4 hE _ hb44
  rw [e170, e1638, Nat.beq_refl] at hB
  have hC : loopC2 ACT TM WP L3 (f 191) (f 169) (ev2 ACT TM (f 191) (f 169) 0 1446)
      (sOf ACT TM (f 191) I2) = true := hB
  have hcS : f 156 ∈ sOf ACT TM (f 191) I2 := sOf_mem e3549 I2 hc22
  obtain ⟨Q, hQd⟩ : ∃ Q, mI ACT TM (mI ACT TM (mI ACT TM (mI ACT TM (mI ACT TM (mI ACT TM 0
      (f 169)) (f 191)) (f 169)) (f 169)) (f 191)) (f 191) = Q := ⟨_, rfl⟩
  have hQ : Q < 192 := by
    rw [← hQd]
    exact bnd _ (bnd _ (bnd _ (bnd _ (bnd _ (bnd 0 (by decide) _ hb4) _ ha) _ hb4) _ hb4) _ ha) _ ha
  have e1446 := ev_1446 ACT TM (f 191) (f 169)
  rw [hQd, hid _ hQ, hid _ hQ, hid _ hQ] at e1446
  have e243 := ev_243110 ACT TM (f 191) (f 169) (f 156)
  rw [hQd, hev, Nat.eq_of_beq_eq_true r7, hf0] at e243
  rw [e1446] at hC
  have hF : Bool.rec (motive := fun _ => Bool) true (finK2 ACT TM WP L3 (f 191) (f 169) (f 156))
      (Nat.beq (mI ACT TM (mI ACT TM (mI ACT TM Q (f 156)) (f 169)) (f 156)) 0) = true :=
    recL_all (fun c => Bool.rec (motive := fun _ => Bool) true
      (finK2 ACT TM WP L3 (f 191) (f 169) c)
      (Nat.beq (mI ACT TM (mI ACT TM (mI ACT TM Q c) (f 169)) c) 0)) _ hC _ hcS
  rw [← e243, Nat.beq_refl] at hF
  have hX : ∀ t < 64, Nat.add (Nat.mul 12 (Nat.div t 4)) (Nat.mod t 4) < 192 ∧
      jB (Nat.add (Nat.mul 12 (Nat.div t 4)) (Nat.mod t 4)) = true := by
    intro t ht
    refine ⟨?_, ?_⟩
    · change 12 * (t / 4) + t % 4 < 192
      omega
    · change Nat.blt ((12 * (t / 4) + t % 4) % 12) 4 = true
      simp only [Nat.blt_eq]
      omega
  obtain ⟨F1, F2⟩ := fixR_sound (fun x => Nat.beq (phi2 ACT TM WP (f 191) (f 169) (f 156) x) x)
    (fun x => Nat.beq (mI ACT TM x x) 0)
    (fun t => Nat.add (Nat.mul 12 (Nat.div t 4)) (Nat.mod t 4)) 64
  rw [jB_count (fun x => f x == x)] at hcard
  have hcnt : ((List.range 64).filter fun t => Nat.beq (phi2 ACT TM WP (f 191) (f 169) (f 156)
      (Nat.add (Nat.mul 12 (Nat.div t 4)) (Nat.mod t 4)))
      (Nat.add (Nat.mul 12 (Nat.div t 4)) (Nat.mod t 4))).length = 4 := by
    refine Eq.trans (congrArg List.length (List.filter_congr fun t ht => ?_)) hcard
    rw [hphi _ (hX t (List.mem_range.1 ht)).1, nbeq_eq]
  have h4 : (fixJ2 ACT TM WP (f 191) (f 169) (f 156)).1 = 4 := by
    rw [← hcnt]
    exact F1
  have h5 : (fixJ2 ACT TM WP (f 191) (f 169) (f 156)).2 = true := by
    refine F2 fun t ht hq => ?_
    obtain ⟨hx, hj⟩ := hX t ht
    generalize Nat.add (Nat.mul 12 (Nat.div t 4)) (Nat.mod t 4) = x at hq hx hj ⊢
    have hfx : f x = x := by
      have h' := Nat.eq_of_beq_eq_true hq
      rwa [hphi _ hx] at h'
    rw [hel x hx hj hfx]
    exact Nat.beq_refl 0
  have p1 : phi2 ACT TM WP (f 191) (f 169) (f 156) (f 191) = 191 := by
    rw [hphi _ ha, hff 191 h191]
  have p2 : phi2 ACT TM WP (f 191) (f 169) (f 156) (f 169) = 169 := by
    rw [hphi _ hb4, hff 169 h169]
  have p3 : phi2 ACT TM WP (f 191) (f 169) (f 156) (f 156) = 156 := by
    rw [hphi _ hc2, hff 156 h156]
  have hY := finK2_sound hF p1 p2 p3 h4 h5
  unfold anyY2 at hY
  obtain ⟨y, hyL, hy⟩ := recL_any _ _ hY
  rw [Bool.and_eq_true] at hy
  have hy192 : y < 192 := by
    have h' := hlt' y (List.mem_append_left _ (List.mem_append_left _ hyL))
    simpa [Nat.blt_eq] using h'
  refine ⟨y, hy192, ?_, ?_, ?_⟩
  · have h' := hy.1
    simp only [Nat.blt_eq] at h'
    omega
  · exact Nat.eq_of_beq_eq_true ((m3 y hy192).1 hyL)
  · rw [← hphi y hy192]
    exact Nat.eq_of_beq_eq_true hy.2

end CFSG.KD.T84S4

end

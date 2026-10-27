module

public import Certificates.Data.Kernel.PackSet
public import Mathlib.GroupTheory.Perm.Sign
import Mathlib.Tactic.Ring.RingNF

public section

namespace CFSG.KC.Pack

open CFSG.KC.Enum CFSG.KS

theorem strictN_eq (y : Nat) (k : Nat → Nat) : strictN y k = k y := by cases y <;> rfl

theorem strictB_eq (y : Nat) (k : Nat → Bool) : strictB y k = k y := by cases y <;> rfl

theorem band_iff {a b : Bool} : Bool.rec (motive := fun _ => Bool) false b a = true ↔
    a = true ∧ b = true := by
  cases a <;> simp

theorem nif_true {c : Bool} {t e : Nat} (h : c = true) :
    Bool.rec (motive := fun _ => Nat) e t c = t := by subst h; rfl

theorem nif_false {c : Bool} {t e : Nat} (h : c = false) :
    Bool.rec (motive := fun _ => Nat) e t c = e := by subst h; rfl

theorem foldBlk_eq (b : Nat) (f : Nat → Nat → Nat) :
    ∀ len s, foldBlk b f len s = (List.range len).foldr (fun l s => f (b + l) s) s
  | 0, _ => rfl
  | len + 1, s => by
    change strictN (f (Nat.add b len) s) (foldBlk b f len) = _
    rw [strictN_eq, foldBlk_eq b f len, List.range_succ, List.foldr_append]
    rfl

theorem shl6 (x : Nat) : Nat.shiftLeft x (nat_lit 6) = 64 * x := by
  change x <<< 6 = _
  rw [Nat.shiftLeft_eq, Nat.mul_comm]

theorem foldN_rec (f : Nat → Nat → Nat) : ∀ q s,
    Nat.rec (motive := fun _ => Nat → Nat) (fun s => s)
      (fun h ih s => strictN (foldBlk (Nat.shiftLeft h (nat_lit 6)) f (nat_lit 64) s) ih) q s =
    (List.range (64 * q)).foldr f s
  | 0, _ => rfl
  | q + 1, s => by
    change strictN (foldBlk (Nat.shiftLeft q (nat_lit 6)) f (nat_lit 64) s)
      (Nat.rec (motive := fun _ => Nat → Nat) (fun s => s)
        (fun h ih s => strictN (foldBlk (Nat.shiftLeft h (nat_lit 6)) f (nat_lit 64) s) ih) q) = _
    rw [strictN_eq, foldN_rec f q, foldBlk_eq, shl6, Nat.mul_succ, List.range_add,
      List.foldr_append, List.foldr_map]

theorem foldN_eq (n : Nat) (f : Nat → Nat → Nat) (s : Nat) :
    foldN n f s = (List.range n).foldr f s := by
  have e64 : Nat.shiftRight n (nat_lit 6) = n / 64 := by
    change n >>> 6 = n / 64
    rw [Nat.shiftRight_eq_div_pow]
  have er : Nat.land n (nat_lit 63) = n % 64 := by
    change n &&& (2 ^ 6 - 1) = n % 2 ^ 6
    exact Nat.and_two_pow_sub_one_eq_mod n 6
  change Nat.rec (motive := fun _ => Nat → Nat) (fun s => s)
      (fun h ih s => strictN (foldBlk (Nat.shiftLeft h (nat_lit 6)) f (nat_lit 64) s) ih)
      (Nat.shiftRight n (nat_lit 6))
      (foldBlk (Nat.shiftLeft (Nat.shiftRight n (nat_lit 6)) (nat_lit 6)) f
        (Nat.land n (nat_lit 63)) s) = _
  rw [foldN_rec, foldBlk_eq, shl6, e64, er]
  conv_rhs => rw [← Nat.div_add_mod n 64, List.range_add, List.foldr_append, List.foldr_map]

theorem foldr_rev (f : Nat → Nat → Nat) : ∀ n s,
    (List.range n).foldr (fun i s => f (n - 1 - i) s) s =
      (List.range n).foldl (fun s i => f i s) s
  | 0, _ => rfl
  | n + 1, s => by
    conv_lhs => rw [List.range_succ_eq_map, List.foldr_cons, List.foldr_map]
    conv_rhs => rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
    have e : ∀ i, n + 1 - 1 - Nat.succ i = n - 1 - i := fun i => by omega
    have e0 : n + 1 - 1 - 0 = n := by omega
    simp only [e, e0]
    rw [foldr_rev f n s]

theorem foldUp_eq (n : Nat) (f : Nat → Nat → Nat) (s : Nat) :
    foldUp n f s = (List.range n).foldl (fun s i => f i s) s := by
  unfold foldUp
  rw [foldN_eq]
  exact foldr_rev f n s

theorem allBlk_spec {b : Nat} {f : Nat → Bool} :
    ∀ {len : Nat}, allBlk b f len = true → ∀ l < len, f (Nat.add b l) = true
  | 0, _, l, hl => absurd hl (Nat.not_lt_zero l)
  | len + 1, h, l, hl => by
    change Bool.rec (motive := fun _ => Bool) false (allBlk b f len) (f (Nat.add b len)) = true
      at h
    obtain ⟨h1, h2⟩ := band_iff.1 h
    rcases Nat.lt_or_ge l len with hl' | hl'
    · exact allBlk_spec h2 l hl'
    · obtain rfl : l = len := by omega
      exact h1

theorem rec_blocks_spec {f : Nat → Bool} : ∀ {q : Nat},
    Nat.rec (motive := fun _ => Bool) true
      (fun h ih => Bool.rec (motive := fun _ => Bool) false ih
        (allBlk (Nat.shiftLeft h (nat_lit 6)) f (nat_lit 64))) q = true →
    ∀ h < q, allBlk (Nat.shiftLeft h (nat_lit 6)) f (nat_lit 64) = true
  | 0, _, h, hh => absurd hh (Nat.not_lt_zero h)
  | q + 1, H, h, hh => by
    change Bool.rec (motive := fun _ => Bool) false
      (Nat.rec (motive := fun _ => Bool) true
        (fun h ih => Bool.rec (motive := fun _ => Bool) false ih
          (allBlk (Nat.shiftLeft h (nat_lit 6)) f (nat_lit 64))) q)
      (allBlk (Nat.shiftLeft q (nat_lit 6)) f (nat_lit 64)) = true at H
    obtain ⟨h1, h2⟩ := band_iff.1 H
    rcases Nat.lt_or_ge h q with hl | hl
    · exact rec_blocks_spec h2 h hl
    · obtain rfl : h = q := by omega
      exact h1

theorem allN_spec {n : Nat} {f : Nat → Bool} (h : allN n f = true) : ∀ i < n, f i = true := by
  have e64 : Nat.shiftRight n (nat_lit 6) = n / 64 := by
    change n >>> 6 = n / 64
    rw [Nat.shiftRight_eq_div_pow]
  have er : Nat.land n (nat_lit 63) = n % 64 := by
    change n &&& (2 ^ 6 - 1) = n % 2 ^ 6
    exact Nat.and_two_pow_sub_one_eq_mod n 6
  change Bool.rec (motive := fun _ => Bool) false
      (Nat.rec (motive := fun _ => Bool) true
        (fun h ih => Bool.rec (motive := fun _ => Bool) false ih
          (allBlk (Nat.shiftLeft h (nat_lit 6)) f (nat_lit 64))) (Nat.shiftRight n (nat_lit 6)))
      (allBlk (Nat.shiftLeft (Nat.shiftRight n (nat_lit 6)) (nat_lit 6)) f
        (Nat.land n (nat_lit 63))) = true at h
  obtain ⟨h1, h2⟩ := band_iff.1 h
  intro i hi
  have hd := Nat.div_add_mod i 64
  have hm := Nat.mod_lt i (by norm_num : 0 < 64)
  have hdn := Nat.div_add_mod n 64
  rcases Nat.lt_or_ge (i / 64) (n / 64) with hq | hq
  · have := allBlk_spec (rec_blocks_spec h2 (i / 64) (by rw [e64]; exact hq)) (i % 64) hm
    rwa [shl6, Nat.add_eq, hd] at this
  · have hq' : i / 64 = n / 64 := by
      have : i / 64 ≤ n / 64 := Nat.div_le_div_right hi.le
      omega
    have := allBlk_spec h1 (i % 64) (by rw [er]; omega)
    rwa [shl6, e64, Nat.add_eq, ← hq', hd] at this

theorem fld_eq (q o r : Nat) : Nat.land (Nat.shiftRight q o) (2 ^ r - 1) = q / 2 ^ o % 2 ^ r := by
  change (q >>> o) &&& (2 ^ r - 1) = _
  rw [Nat.shiftRight_eq_div_pow]
  exact Nat.and_two_pow_sub_one_eq_mod _ _

theorem mask_eq (w : Nat) : mask w = 2 ^ w - 1 := by
  change 1 <<< w - 1 = _
  rw [Nat.shiftLeft_eq, Nat.one_mul]

theorem pg_eq (w q i : Nat) : pg w (2 ^ w - 1) q i = q / 2 ^ (w * i) % 2 ^ w :=
  fld_eq q (Nat.mul w i) w

theorem parts {A g r o a : Nat} (hg : g < 2 ^ a) (hr : r < 2 ^ o) :
    (A * 2 ^ (o + a) + g * 2 ^ o + r) / 2 ^ o % 2 ^ a = g ∧
      (A * 2 ^ (o + a) + g * 2 ^ o + r) % 2 ^ o = r ∧
      (A * 2 ^ (o + a) + g * 2 ^ o + r) / 2 ^ (o + a) = A := by
  have e : A * 2 ^ (o + a) + g * 2 ^ o + r = r + 2 ^ o * (A * 2 ^ a + g) := by
    rw [pow_add]
    ring
  have h0 : 0 < 2 ^ o := Nat.two_pow_pos o
  have h1 : 0 < 2 ^ a := Nat.two_pow_pos a
  have d : (A * 2 ^ (o + a) + g * 2 ^ o + r) / 2 ^ o = A * 2 ^ a + g := by
    rw [e, Nat.add_mul_div_left _ _ h0, Nat.div_eq_of_lt hr, Nat.zero_add]
  refine ⟨?_, ?_, ?_⟩
  · rw [d, Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hg]
  · rw [e, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hr]
  · have e2 : (A * 2 ^ (o + a) + g * 2 ^ o + r) / 2 ^ (o + a) =
        (A * 2 ^ (o + a) + g * 2 ^ o + r) / 2 ^ o / 2 ^ a := by
      rw [Nat.div_div_eq_div_mul, ← pow_add]
    rw [e2, d, Nat.add_comm, Nat.add_mul_div_right _ _ h1,
      Nat.div_eq_of_lt hg, Nat.zero_add]

theorem decomp (q o a : Nat) :
    q = q / 2 ^ (o + a) * 2 ^ (o + a) + q / 2 ^ o % 2 ^ a * 2 ^ o + q % 2 ^ o := by
  have h1 := Nat.div_add_mod q (2 ^ o)
  have h2 := Nat.div_add_mod (q / 2 ^ o) (2 ^ a)
  rw [Nat.div_div_eq_div_mul, ← pow_add] at h2
  conv_lhs => rw [← h1, ← h2]
  rw [pow_add]
  ring

theorem setO_eq (q o a v : Nat) :
    setO q o (2 ^ a - 1) v = q / 2 ^ (o + a) * 2 ^ (o + a) + v * 2 ^ o + q % 2 ^ o := by
  unfold setO
  change q - (Nat.land (Nat.shiftRight q o) (2 ^ a - 1)) <<< o + v <<< o = _
  rw [Nat.shiftLeft_eq, Nat.shiftLeft_eq, fld_eq]
  have := decomp q o a
  generalize q / 2 ^ (o + a) * 2 ^ (o + a) = X at *
  generalize q / 2 ^ o % 2 ^ a * 2 ^ o = Y at *
  generalize v * 2 ^ o = Z
  omega

theorem fields_eq {y z o a o' r : Nat} (hm : y % 2 ^ o = z % 2 ^ o)
    (hd : y / 2 ^ (o + a) = z / 2 ^ (o + a)) (ho : o' + r ≤ o ∨ o + a ≤ o') :
    y / 2 ^ o' % 2 ^ r = z / 2 ^ o' % 2 ^ r := by
  rcases ho with ho | ho
  · have hdv : 2 ^ (o' + r) ∣ 2 ^ o := pow_dvd_pow 2 ho
    rw [← Nat.mod_mul_right_div_self, ← Nat.mod_mul_right_div_self, ← pow_add,
      ← Nat.mod_mod_of_dvd y hdv, ← Nat.mod_mod_of_dvd z hdv, hm]
  · have e : o' = (o + a) + (o' - (o + a)) := by omega
    rw [e, pow_add, ← Nat.div_div_eq_div_mul, ← Nat.div_div_eq_div_mul, hd]

theorem setO_get {q o a v : Nat} (hv : v < 2 ^ a) :
    Nat.land (Nat.shiftRight (setO q o (2 ^ a - 1) v) o) (2 ^ a - 1) = v := by
  rw [fld_eq, setO_eq]
  exact (parts hv (Nat.mod_lt _ (Nat.two_pow_pos o))).1

theorem setO_other {q o a v o' r : Nat} (hv : v < 2 ^ a) (ho : o' + r ≤ o ∨ o + a ≤ o') :
    Nat.land (Nat.shiftRight (setO q o (2 ^ a - 1) v) o') (2 ^ r - 1) =
      Nat.land (Nat.shiftRight q o') (2 ^ r - 1) := by
  rw [fld_eq, fld_eq, setO_eq]
  have hq := decomp q o a
  have hp := parts (A := q / 2 ^ (o + a)) hv (Nat.mod_lt q (Nat.two_pow_pos o))
  have hp' := parts (A := q / 2 ^ (o + a)) (Nat.mod_lt (q / 2 ^ o) (Nat.two_pow_pos a))
    (Nat.mod_lt q (Nat.two_pow_pos o))
  rw [← hq] at hp'
  exact fields_eq (hp.2.1.trans hp'.2.1.symm) (hp.2.2.trans hp'.2.2.symm) ho

theorem setO_lt {q o a v T : Nat} (hq : q < 2 ^ T) (hv : v < 2 ^ a) (ho : o + a ≤ T) :
    setO q o (2 ^ a - 1) v < 2 ^ T := by
  have h0 : 0 < 2 ^ (o + a) := Nat.two_pow_pos _
  have eT : 2 ^ T = 2 ^ (T - (o + a)) * 2 ^ (o + a) := by
    rw [← pow_add]
    congr 1
    omega
  have hd := (parts (A := q / 2 ^ (o + a)) hv (Nat.mod_lt q (Nat.two_pow_pos o))).2.2
  rw [setO_eq, eT, ← Nat.div_lt_iff_lt_mul h0, hd, Nat.div_lt_iff_lt_mul h0, ← eT]
  exact hq

theorem fld_high {q o r T : Nat} (hq : q < 2 ^ T) (ho : T ≤ o) :
    Nat.land (Nat.shiftRight q o) (2 ^ r - 1) = 0 := by
  rw [fld_eq, Nat.div_eq_of_lt (lt_of_lt_of_le hq (Nat.pow_le_pow_right (by norm_num) ho)),
    Nat.zero_mod]

theorem fld_lt (q o r : Nat) : Nat.land (Nat.shiftRight q o) (2 ^ r - 1) < 2 ^ r := by
  rw [fld_eq]
  exact Nat.mod_lt _ (Nat.two_pow_pos r)

theorem disj {w i j : Nat} (h : i ≠ j) : w * i + w ≤ w * j ∨ w * j + w ≤ w * i := by
  rcases Nat.lt_or_gt_of_ne h with h | h
  · left
    have := Nat.mul_le_mul_left w (Nat.succ_le_of_lt h)
    rw [Nat.mul_succ] at this
    exact this
  · right
    have := Nat.mul_le_mul_left w (Nat.succ_le_of_lt h)
    rw [Nat.mul_succ] at this
    exact this

theorem pg_swapF {w q a b i : Nat} :
    pg w (2 ^ w - 1) (swapF w (2 ^ w - 1) q a b) i =
      if i = b then pg w (2 ^ w - 1) q a else if i = a then pg w (2 ^ w - 1) q b
      else pg w (2 ^ w - 1) q i := by
  unfold swapF
  rw [strictN_eq, strictN_eq, strictN_eq]
  have hx : pg w (2 ^ w - 1) q a < 2 ^ w := fld_lt q (Nat.mul w a) w
  have hy : pg w (2 ^ w - 1) q b < 2 ^ w := fld_lt q (Nat.mul w b) w
  change Nat.land (Nat.shiftRight (setO (setO q (w * a) (2 ^ w - 1) (pg w (2 ^ w - 1) q b))
    (w * b) (2 ^ w - 1) (pg w (2 ^ w - 1) q a)) (w * i)) (2 ^ w - 1) = _
  by_cases hib : i = b
  · subst hib
    rw [ite_eq_left rfl]
    exact setO_get hx
  · rw [ite_eq_right hib]
    rw [setO_other hx (disj hib)]
    by_cases hia : i = a
    · subst hia
      rw [ite_eq_left rfl]
      exact setO_get hy
    · rw [ite_eq_right hia]
      exact setO_other hy (disj hia)

theorem swaps_inv {n w : Nat} (T : Nat) (F : Nat → Nat → Nat)
    (hF : ∀ j q, F j q = swapF w (2 ^ w - 1) q (pg w (2 ^ w - 1) T (2 * j))
      (pg w (2 ^ w - 1) T (2 * j + 1))) :
    ∀ (l : List Nat) (π : Equiv.Perm (Fin n)) (q : Nat),
      (∀ j ∈ l, pg w (2 ^ w - 1) T (2 * j) < n ∧ pg w (2 ^ w - 1) T (2 * j + 1) < n ∧
        pg w (2 ^ w - 1) T (2 * j) ≠ pg w (2 ^ w - 1) T (2 * j + 1)) →
      (∀ i : Fin n, pg w (2 ^ w - 1) q i = π i) →
      ∃ σ : Equiv.Perm (Fin n), Equiv.Perm.sign σ = (-1) ^ l.length ∧
        ∀ i : Fin n, pg w (2 ^ w - 1) (l.foldl (fun s j => F j s) q) i = (π * σ) i
  | [], π, q, _, hq => ⟨1, by simp, fun i => by simpa using hq i⟩
  | j :: l, π, q, hl, hq => by
    obtain ⟨ha, hb, hab⟩ := hl j List.mem_cons_self
    set a : Fin n := ⟨_, ha⟩
    set b : Fin n := ⟨_, hb⟩
    have hab' : a ≠ b := fun e => hab (congrArg Fin.val e)
    have hq' : ∀ i : Fin n, pg w (2 ^ w - 1) (F j q) i = (π * Equiv.swap a b) i := by
      intro i
      rw [hF, pg_swapF,Equiv.Perm.mul_apply, Equiv.swap_apply_def]
      by_cases hia : i = a
      · subst hia
        have : (a : Nat) ≠ b := fun e => hab' (Fin.ext e)
        rw [ite_eq_right this, ite_eq_left rfl, ite_eq_left rfl]
        exact hq b
      · by_cases hib : i = b
        · subst hib
          rw [ite_eq_left rfl, ite_eq_right hia, ite_eq_left rfl]
          exact hq a
        · rw [ite_eq_right (fun e => hib (Fin.ext e)), ite_eq_right (fun e => hia (Fin.ext e)),
            ite_eq_right hia, ite_eq_right hib]
          exact hq i
    obtain ⟨σ, hs, hσ⟩ := swaps_inv T F hF l (π * Equiv.swap a b) (F j q)
      (fun k hk => hl k (List.mem_cons_of_mem j hk)) hq'
    refine ⟨Equiv.swap a b * σ, ?_, fun i => ?_⟩
    · rw [Equiv.Perm.sign_mul, Equiv.Perm.sign_swap hab', hs, List.length_cons, pow_succ]
      exact mul_comm _ _
    · simp only [List.foldl_cons]
      rw [hσ i, mul_assoc]

theorem sign_of_signK {n w m p T k : Nat} (h : signK n w m p T k = true)
    {g : Equiv.Perm (Fin n)} (hg : ∀ i : Fin n, (g i : Nat) = pg w m p i) :
    Equiv.Perm.sign g = (-1) ^ k := by
  unfold signK at h
  obtain ⟨hm, h⟩ := band_iff.1 h
  obtain ⟨hp, hid⟩ := band_iff.1 h
  rw [Nat.beq_eq] at hm
  subst hm
  rw [mask_eq] at hg hp hid
  have hpairs : ∀ j ∈ List.range k, pg w (2 ^ w - 1) T (2 * j) < n ∧
      pg w (2 ^ w - 1) T (2 * j + 1) < n ∧
      pg w (2 ^ w - 1) T (2 * j) ≠ pg w (2 ^ w - 1) T (2 * j + 1) := by
    intro j hj
    have := allN_spec hp j (List.mem_range.1 hj)
    simp only [strictB_eq] at this
    obtain ⟨h1, h2⟩ := band_iff.1 this
    obtain ⟨h2, h3⟩ := band_iff.1 h2
    rw [Nat.blt_eq] at h1 h2
    refine ⟨h1, h2, fun e => ?_⟩
    change Bool.rec (motive := fun _ => Bool) true false
      (Nat.beq (pg w (2 ^ w - 1) T (2 * j)) (pg w (2 ^ w - 1) T (2 * j + 1))) = true at h3
    rw [e, Nat.beq_refl] at h3
    exact Bool.false_ne_true h3
  rw [strictB_eq] at hid
  obtain ⟨σ, hs, hσ⟩ := swaps_inv (n := n) T _ (fun j q => rfl)
    (List.range k) g p hpairs (fun i => (hg i).symm)
  have hone : g * σ = 1 := by
    refine Equiv.ext fun i => Fin.ext ?_
    rw [← hσ i]
    have := allN_spec hid i i.2
    rw [Nat.beq_eq] at this
    unfold swapsF at this
    rw [foldUp_eq] at this
    exact this
  rw [eq_inv_of_mul_eq_one_left hone, Equiv.Perm.sign_inv, hs, List.length_range]

end CFSG.KC.Pack

end

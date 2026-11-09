module

public import Mathlib.Algebra.BigOperators.Group.List.Basic
public import Mathlib.Algebra.Group.Conj
public import Mathlib.Tactic.Group
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.NormNum.Basic

public section

namespace CFSG.KC.PcCollect

variable {G : Type*} [Group G] (x : ℕ → G)

@[expose] def evW (l : List ℕ) : G := (l.map x).prod

@[expose] def nfFrom : ℕ → List ℕ → List ℕ
  | _, [] => []
  | i, a :: v => List.replicate a i ++ nfFrom (i + 1) v

@[expose] def vecL (n v : ℕ) : List ℕ := (List.range n).map fun i => v / 16 ^ i % 16

@[expose] def evV (n v : ℕ) : G := evW x (nfFrom 0 (vecL n v))

@[expose] def slot (T i : ℕ) : ℕ :=
  Nat.land (Nat.shiftRight T (Nat.mul 96 i)) 79228162514264337593543950335

@[expose] def decS (wd : ℕ) : List ℕ := (List.range (wd % 256)).map fun i => wd / 2 ^ (8 + 4 * i) % 16

@[expose] def dT (T n k j : ℕ) : List ℕ := decS (slot T (k * n + j))

@[expose] def pT (PT k : ℕ) : List ℕ := decS (slot PT k)

@[expose] def appW (g : ℕ → ℕ → ℕ) (wd w : ℕ) : ℕ :=
  Nat.rec (motive := fun _ => ℕ → ℕ → ℕ) (fun _ w => w)
    (fun _ ih d w => ih (Nat.shiftRight d 4) (g w (Nat.land d 15)))
    (Nat.land wd 255) (Nat.shiftRight wd 8) w

@[expose] def appC (g : ℕ → ℕ → ℕ) (wd c w : ℕ) : ℕ :=
  Nat.rec (motive := fun _ => ℕ → ℕ) (fun w => w) (fun _ ih w => ih (appW g wd w)) c w

@[expose] def sufL (g : ℕ → ℕ → ℕ) (T n k v t w : ℕ) : ℕ :=
  Nat.rec (motive := fun _ => ℕ → ℕ) (fun w => w)
    (fun i ih w => ih (appC g (slot T (Nat.add (Nat.mul k n) (Nat.sub (Nat.sub n 1) i)))
      (Nat.land (Nat.shiftRight v (Nat.mul 4 (Nat.sub (Nat.sub n 1) i))) 15) w)) t w

@[expose] def mulR (n T PT : ℕ) (f : ℕ) : ℕ → ℕ → ℕ :=
  Nat.rec (motive := fun _ => ℕ → ℕ → ℕ) (fun v _ => v)
    (fun _ ih v k =>
      sufL ih T n k v (Nat.sub (Nat.sub n 1) k)
        (Bool.rec (motive := fun _ => ℕ)
          (Nat.add (Nat.land v (Nat.sub (Nat.shiftLeft 1 (Nat.mul 4 (Nat.add k 1))) 1))
            (Nat.shiftLeft 1 (Nat.mul 4 k)))
          (appW ih (slot PT k)
            (Nat.sub (Nat.land v (Nat.sub (Nat.shiftLeft 1 (Nat.mul 4 (Nat.add k 1))) 1))
              (Nat.shiftLeft 4 (Nat.mul 4 k))))
          (Nat.beq (Nat.land (Nat.shiftRight v (Nat.mul 4 k)) 15) 4)))
    f

@[expose] def colR (n T PT : ℕ) (l : List ℕ) : ℕ :=
  List.rec (motive := fun _ => ℕ → ℕ) (fun v => v) (fun a _ ih v => ih (mulR n T PT n v a)) l 0

@[expose] def colE (n T PT : ℕ) (l l' : List ℕ) : Bool := Nat.beq (colR n T PT l) (colR n T PT l')

section Words

theorem evW_nil : evW x [] = 1 := rfl

theorem evW_cons (a : ℕ) (l : List ℕ) : evW x (a :: l) = x a * evW x l := by
  simp [evW]

theorem evW_append (l l' : List ℕ) : evW x (l ++ l') = evW x l * evW x l' := by
  simp [evW, List.map_append, List.prod_append]

theorem evW_replicate (e k : ℕ) : evW x (List.replicate e k) = x k ^ e := by
  simp [evW, List.map_replicate, List.prod_replicate]

theorem nfFrom_cons (i a : ℕ) (v : List ℕ) :
    nfFrom i (a :: v) = List.replicate a i ++ nfFrom (i + 1) v := rfl

theorem nfFrom_append (w : List ℕ) :
    ∀ (u : List ℕ) (i : ℕ), nfFrom i (u ++ w) = nfFrom i u ++ nfFrom (i + u.length) w
  | [], i => by simp [nfFrom]
  | a :: u, i => by
    rw [List.cons_append, nfFrom, nfFrom, nfFrom_append w u (i + 1), List.append_assoc,
      List.length_cons, Nat.add_assoc, Nat.add_comm 1 u.length]

theorem nfFrom_zeros : ∀ (m i : ℕ), nfFrom i (List.replicate m 0) = []
  | 0, _ => rfl
  | m + 1, i => by rw [List.replicate_succ, nfFrom, nfFrom_zeros m (i + 1)]; rfl

theorem nfFrom_mem : ∀ (u : List ℕ) (i l : ℕ), l ∈ nfFrom i u → i ≤ l ∧ l < i + u.length
  | [], _, _, h => by simp [nfFrom] at h
  | a :: u, i, l, h => by
    rw [nfFrom, List.mem_append] at h
    rcases h with h | h
    · rw [(List.mem_replicate.1 h).2]
      simp
    · have := nfFrom_mem u (i + 1) l h
      simp only [List.length_cons]
      omega

theorem evW_mul_of_conj {k n : ℕ} {D : ℕ → List ℕ}
    (hD : ∀ j, k < j → j < n → x j * x k = x k * evW x (D j)) :
    ∀ l : List ℕ, (∀ j ∈ l, k < j ∧ j < n) → evW x l * x k = x k * evW x (l.flatMap D)
  | [], _ => by simp [evW]
  | j :: l, hl => by
    rw [evW_cons, List.flatMap_cons, evW_append, mul_assoc,
      evW_mul_of_conj hD l fun j' hj' => hl j' (List.mem_cons_of_mem _ hj'), ← mul_assoc,
      hD j (hl j (List.mem_cons_self ..)).1 (hl j (List.mem_cons_self ..)).2, mul_assoc]

theorem mul_evW_of_rel {k n : ℕ} {C : ℕ → List ℕ}
    (hC : ∀ m, k < m → m < n → x k * x m = evW x (C m) * x k) :
    ∀ l : List ℕ, (∀ m ∈ l, k < m ∧ m < n) → x k * evW x l = evW x (l.flatMap C) * x k
  | [], _ => by simp [evW]
  | m :: l, hl => by
    rw [evW_cons, List.flatMap_cons, evW_append, ← mul_assoc,
      hC m (hl m (List.mem_cons_self ..)).1 (hl m (List.mem_cons_self ..)).2, mul_assoc,
      mul_evW_of_rel hC l fun m' hm' => hl m' (List.mem_cons_of_mem _ hm'), ← mul_assoc]

theorem evW_flatMap_replicate {R : ℕ → List ℕ} :
    ∀ e k : ℕ, evW x ((List.replicate e k).flatMap R) = evW x (R k) ^ e
  | 0, _ => by simp [evW]
  | e + 1, k => by
    rw [List.replicate_succ, List.flatMap_cons, evW_append, evW_flatMap_replicate e k, pow_succ']

end Words

section Digits

theorem pow16_pos (k : ℕ) : 0 < 16 ^ k := pow_pos (by norm_num) k

theorem shiftLeft_one_four (k : ℕ) : Nat.shiftLeft 1 (Nat.mul 4 k) = 16 ^ k := by
  change 1 <<< (4 * k) = _
  rw [Nat.shiftLeft_eq, one_mul, pow_mul]
  norm_num

theorem shiftLeft_four_four (k : ℕ) : Nat.shiftLeft 4 (Nat.mul 4 k) = 4 * 16 ^ k := by
  change 4 <<< (4 * k) = _
  rw [Nat.shiftLeft_eq, pow_mul]
  norm_num

theorem land_mask (v k : ℕ) :
    Nat.land v (Nat.sub (Nat.shiftLeft 1 (Nat.mul 4 (Nat.add k 1))) 1) = v % 16 ^ (k + 1) := by
  change v &&& (1 <<< (4 * (k + 1)) - 1) = _
  rw [Nat.shiftLeft_eq, one_mul, Nat.and_two_pow_sub_one_eq_mod, pow_mul]
  norm_num

theorem dig_eq (v s : ℕ) : Nat.land (Nat.shiftRight v (Nat.mul 4 s)) 15 = v / 16 ^ s % 16 := by
  change (v >>> (4 * s)) &&& (2 ^ 4 - 1) = _
  rw [Nat.and_two_pow_sub_one_eq_mod, Nat.shiftRight_eq_div_pow, pow_mul]
  norm_num

theorem digit_add (A c k i : ℕ) (hA : A < 16 ^ k) (hc : c < 16) :
    (A + c * 16 ^ k) / 16 ^ i % 16 = if i < k then A / 16 ^ i % 16 else if i = k then c else 0 := by
  split_ifs with h1 h2
  · obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_lt h1
    have e : A + c * 16 ^ (i + d + 1) = A + 16 ^ i * (c * 16 ^ d * 16) := by ring
    rw [e, Nat.add_mul_div_left _ _ (pow16_pos i), Nat.add_mul_mod_self_right]
  · subst h2
    rw [Nat.add_mul_div_right _ _ (pow16_pos _), Nat.div_eq_of_lt hA, zero_add,
      Nat.mod_eq_of_lt hc]
  · have hik : k + 1 ≤ i := by omega
    have : A + c * 16 ^ k < 16 ^ i := by
      calc A + c * 16 ^ k < 16 ^ k + c * 16 ^ k := by omega
        _ = (c + 1) * 16 ^ k := by ring
        _ ≤ 16 * 16 ^ k := Nat.mul_le_mul_right _ (by omega)
        _ = 16 ^ (k + 1) := by ring
        _ ≤ 16 ^ i := Nat.pow_le_pow_right (by norm_num) hik
    rw [Nat.div_eq_of_lt this, Nat.zero_mod]

theorem digit_mod (v k i : ℕ) (hi : i < k) : v % 16 ^ k / 16 ^ i % 16 = v / 16 ^ i % 16 := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_lt hi
  rw [show i + d + 1 = i + (d + 1) by omega, pow_add, Nat.mod_mul_right_div_self, pow_succ,
    Nat.mod_mul_left_mod]

theorem mod_succ_split (v k : ℕ) : v % 16 ^ (k + 1) = v % 16 ^ k + v / 16 ^ k % 16 * 16 ^ k := by
  rw [Nat.mod_pow_succ]
  ring

theorem vecL_set (n v k c : ℕ) (hk : k < n) (hc : c < 16) :
    vecL n (v % 16 ^ k + c * 16 ^ k) =
      (vecL n v).take k ++ c :: List.replicate (n - (k + 1)) 0 := by
  have hlen : ((vecL n v).take k).length = k := by simp [vecL]; omega
  apply List.ext_getElem
  · simp [vecL]
    omega
  · intro i h1 h2
    simp only [vecL, List.length_map, List.length_range] at h1
    simp only [vecL, List.getElem_map, List.getElem_range]
    rw [digit_add _ _ _ _ (Nat.mod_lt _ (pow16_pos k)) hc]
    have hl2 : (List.take k (List.map (fun i => v / 16 ^ i % 16) (List.range n))).length = k := by
      simp; omega
    split_ifs with h3 h4
    · rw [digit_mod _ _ _ h3, List.getElem_append_left (by simp; omega),
        List.getElem_take, List.getElem_map, List.getElem_range]
    · subst h4
      rw [List.getElem_append_right (by simp)]
      simp [hl2]
    · rw [List.getElem_append_right (by simp; omega)]
      obtain ⟨d, rfl⟩ : ∃ d, i = k + 1 + d := ⟨i - k - 1, by omega⟩
      have e : k + 1 + d - k = d + 1 := by omega
      simp [hl2, e]

theorem getElem_vecL (n v k : ℕ) (hk : k < (vecL n v).length) : (vecL n v)[k] = v / 16 ^ k % 16 := by
  simp [vecL]

theorem vecL_split (n v k : ℕ) (hk : k < n) :
    vecL n v = (vecL n v).take k ++ (v / 16 ^ k % 16) :: (vecL n v).drop (k + 1) := by
  have hl : k < (vecL n v).length := by simp [vecL]; exact hk
  conv_lhs => rw [← List.take_append_drop k (vecL n v), List.drop_eq_getElem_cons hl]
  rw [getElem_vecL]

end Digits

section Loops

theorem appW_rec (g : ℕ → ℕ → ℕ) :
    ∀ (t d w : ℕ), Nat.rec (motive := fun _ => ℕ → ℕ → ℕ) (fun _ w => w)
        (fun _ ih d w => ih (Nat.shiftRight d 4) (g w (Nat.land d 15))) t d w =
      ((List.range t).map fun i => d / 2 ^ (4 * i) % 16).foldl g w
  | 0, _, _ => rfl
  | t + 1, d, w => by
    rw [List.range_succ_eq_map, List.map_cons, List.map_map, List.foldl_cons]
    change (Nat.rec (motive := fun _ => ℕ → ℕ → ℕ) (fun _ w => w)
        (fun _ ih d w => ih (Nat.shiftRight d 4) (g w (Nat.land d 15))) t) (Nat.shiftRight d 4)
        (g w (Nat.land d 15)) = _
    rw [appW_rec g t]
    have e1 : Nat.land d 15 = d / 2 ^ (4 * 0) % 16 := by
      change d &&& (2 ^ 4 - 1) = _
      rw [Nat.and_two_pow_sub_one_eq_mod]
      simp
    have e2 : ∀ i, Nat.shiftRight d 4 / 2 ^ (4 * i) % 16 = d / 2 ^ (4 * (i + 1)) % 16 := by
      intro i
      have e : Nat.shiftRight d 4 = d / 2 ^ 4 := Nat.shiftRight_eq_div_pow d 4
      rw [e, Nat.div_div_eq_div_mul, ← pow_add]
      ring_nf
    rw [e1]
    congr 1
    apply List.map_congr_left
    intro i _
    rw [e2]
    rfl

theorem appW_eq (g : ℕ → ℕ → ℕ) (wd w : ℕ) : appW g wd w = (decS wd).foldl g w := by
  have h1 : Nat.land wd 255 = wd % 256 := by
    change wd &&& (2 ^ 8 - 1) = _
    rw [Nat.and_two_pow_sub_one_eq_mod]
  have h2 : ∀ i, Nat.shiftRight wd 8 / 2 ^ (4 * i) % 16 = wd / 2 ^ (8 + 4 * i) % 16 := by
    intro i
    have e : Nat.shiftRight wd 8 = wd / 2 ^ 8 := Nat.shiftRight_eq_div_pow wd 8
    rw [e, Nat.div_div_eq_div_mul, ← pow_add]
  rw [appW, appW_rec, h1, decS]
  congr 1
  apply List.map_congr_left
  intro i _
  exact h2 i

theorem appC_eq (g : ℕ → ℕ → ℕ) (wd : ℕ) :
    ∀ (c w : ℕ), appC g wd c w = ((List.replicate c 0).flatMap fun _ => decS wd).foldl g w
  | 0, _ => rfl
  | c + 1, w => by
    change appC g wd c (appW g wd w) = _
    rw [appC_eq g wd c, appW_eq, List.replicate_succ, List.flatMap_cons, List.foldl_append]

theorem flatMap_replicate_const (f : ℕ → List ℕ) (a b : ℕ) :
    ∀ e : ℕ, (List.replicate e a).flatMap f = (List.replicate e b).flatMap fun _ => f a
  | 0 => rfl
  | e + 1 => by
    rw [List.replicate_succ, List.replicate_succ, List.flatMap_cons, List.flatMap_cons,
      flatMap_replicate_const f a b e]

theorem sufL_eq (g : ℕ → ℕ → ℕ) (T n k v : ℕ) :
    ∀ t w, t ≤ n → sufL g T n k v t w =
      ((nfFrom (n - t) ((vecL n v).drop (n - t))).flatMap (dT T n k)).foldl g w
  | 0, w, _ => by
    have hl : (vecL n v).length = n := by simp [vecL]
    rw [Nat.sub_zero, List.drop_eq_nil_of_le (by omega)]
    rfl
  | t + 1, w, ht => by
    change sufL g T n k v t (appC g (slot T (k * n + (n - 1 - t))) (Nat.land (Nat.shiftRight v
      (Nat.mul 4 (n - 1 - t))) 15) w) = _
    rw [sufL_eq g T n k v t _ (by omega), appC_eq, dig_eq]
    have hl : n - (t + 1) < (vecL n v).length := by simp [vecL]; omega
    have e1 : n - (t + 1) + 1 = n - t := by omega
    have e2 : n - 1 - t = n - (t + 1) := by omega
    rw [List.drop_eq_getElem_cons hl, getElem_vecL, nfFrom, List.flatMap_append, List.foldl_append,
      e1, e2, flatMap_replicate_const (dT T n k) (n - (t + 1)) 0]
    rfl

theorem colR_eq (n T PT : ℕ) :
    ∀ (l : List ℕ) (v : ℕ), List.rec (motive := fun _ => ℕ → ℕ) (fun v => v)
      (fun a _ ih v => ih (mulR n T PT n v a)) l v = l.foldl (fun v a => mulR n T PT n v a) v
  | [], _ => rfl
  | _ :: l, _ => colR_eq n T PT l _

theorem mulR_succ (n T PT f v k : ℕ) :
    mulR n T PT (f + 1) v k = sufL (mulR n T PT f) T n k v (n - 1 - k)
      (if v / 16 ^ k % 16 = 4 then appW (mulR n T PT f) (slot PT k) (v % 16 ^ k)
        else v % 16 ^ k + (v / 16 ^ k % 16 + 1) * 16 ^ k) := by
  have h : mulR n T PT (f + 1) v k = sufL (mulR n T PT f) T n k v (Nat.sub (Nat.sub n 1) k)
      (Bool.rec (motive := fun _ => ℕ)
        (Nat.add (Nat.land v (Nat.sub (Nat.shiftLeft 1 (Nat.mul 4 (Nat.add k 1))) 1))
          (Nat.shiftLeft 1 (Nat.mul 4 k)))
        (appW (mulR n T PT f) (slot PT k)
          (Nat.sub (Nat.land v (Nat.sub (Nat.shiftLeft 1 (Nat.mul 4 (Nat.add k 1))) 1))
            (Nat.shiftLeft 4 (Nat.mul 4 k))))
        (Nat.beq (Nat.land (Nat.shiftRight v (Nat.mul 4 k)) 15) 4)) := rfl
  rw [h, land_mask, shiftLeft_one_four, shiftLeft_four_four, dig_eq, mod_succ_split]
  congr 1
  by_cases he : v / 16 ^ k % 16 = 4
  · simp only [he, ↓reduceIte, Nat.beq_refl]
    change appW (mulR n T PT f) (slot PT k) (v % 16 ^ k + 4 * 16 ^ k - 4 * 16 ^ k) = _
    rw [Nat.add_sub_cancel]
  · have hb : Nat.beq (v / 16 ^ k % 16) 4 = false := by
      cases h : Nat.beq (v / 16 ^ k % 16) 4
      · rfl
      · exact absurd (Nat.eq_of_beq_eq_true h) he
    simp only [he, ↓reduceIte, hb]
    change v % 16 ^ k + v / 16 ^ k % 16 * 16 ^ k + 16 ^ k = _
    ring

end Loops

section Sound

@[expose] def okV (n v : ℕ) : Prop := v < 16 ^ n ∧ ∀ i < n, v / 16 ^ i % 16 ≤ 4

theorem okV_set (n v k c : ℕ) (hk : k < n) (hv : okV n v) (hc : c ≤ 4) :
    okV n (v % 16 ^ k + c * 16 ^ k) := by
  have hA := Nat.mod_lt v (pow16_pos k)
  refine ⟨?_, fun i hi => ?_⟩
  · calc v % 16 ^ k + c * 16 ^ k < 16 ^ k + 4 * 16 ^ k := by
          have := Nat.mul_le_mul_right (16 ^ k) hc
          omega
      _ ≤ 16 ^ (k + 1) := by rw [pow_succ]; omega
      _ ≤ 16 ^ n := Nat.pow_le_pow_right (by norm_num) hk
  · rw [digit_add _ _ _ _ hA (by omega)]
    split_ifs with h1 h2
    · rw [digit_mod _ _ _ h1]
      exact hv.2 i hi
    · exact hc
    · omega

theorem evV_set (n v k c : ℕ) (hk : k < n) (hc : c < 16) :
    evV x n (v % 16 ^ k + c * 16 ^ k) = evW x (nfFrom 0 ((vecL n v).take k)) * x k ^ c := by
  have hlt : ((vecL n v).take k).length = k := by simp [vecL]; omega
  rw [evV, vecL_set n v k c hk hc, nfFrom_append, hlt, Nat.zero_add, nfFrom, nfFrom_zeros,
    List.append_nil, evW_append, evW_replicate]

theorem evV_split (n v k : ℕ) (hk : k < n) :
    evV x n v = evW x (nfFrom 0 ((vecL n v).take k)) * x k ^ (v / 16 ^ k % 16) *
      evW x (nfFrom (k + 1) ((vecL n v).drop (k + 1))) := by
  have hlt : ((vecL n v).take k).length = k := by simp [vecL]; omega
  rw [evV]
  conv_lhs => rw [vecL_split n v k hk]
  rw [nfFrom_append, hlt, Nat.zero_add, nfFrom, evW_append, evW_append, evW_replicate, mul_assoc]

theorem evV_zero (n : ℕ) : evV x n 0 = 1 := by
  have : vecL n 0 = List.replicate n 0 := by
    apply List.ext_getElem
    · simp [vecL]
    · intro i _ _
      simp [vecL]
  rw [evV, this, nfFrom_zeros, evW_nil]

theorem okV_zero (n : ℕ) : okV n 0 := ⟨pow16_pos n, fun i _ => by simp⟩

theorem mulR_sound (n T PT m : ℕ)
    (hD : ∀ k j, m ≤ k → k < j → j < n → x j * x k = x k * evW x (dT T n k j))
    (hDl : ∀ k j, m ≤ k → k < j → j < n → ∀ l ∈ dT T n k j, k < l ∧ l < n)
    (hP : ∀ k, m ≤ k → k < n → x k ^ 5 = evW x (pT PT k))
    (hPl : ∀ k, m ≤ k → k < n → ∀ l ∈ pT PT k, k < l ∧ l < n) :
    ∀ f v k, n ≤ k + f → m ≤ k → k < n → okV n v →
      evV x n v * x k = evV x n (mulR n T PT f v k) ∧ okV n (mulR n T PT f v k) := by
  intro f
  induction f with
  | zero => intro v k h1 _ h3; omega
  | succ f ih =>
    intro v k hf hmk hkn hv
    have hfold : ∀ (l : List ℕ) (w : ℕ), okV n w → (∀ j ∈ l, k < j ∧ j < n) →
        evV x n w * evW x l = evV x n (l.foldl (mulR n T PT f) w) ∧
          okV n (l.foldl (mulR n T PT f) w) := by
      intro l
      induction l with
      | nil => intro w hw _; exact ⟨by rw [evW_nil, mul_one, List.foldl_nil], hw⟩
      | cons j l ihl =>
        intro w hw hl
        have hj := hl j (List.mem_cons_self ..)
        obtain ⟨e1, o1⟩ := ih w j (by omega) (by omega) hj.2 hw
        obtain ⟨e2, o2⟩ := ihl _ o1 fun j' hj' => hl j' (List.mem_cons_of_mem _ hj')
        exact ⟨by rw [evW_cons, ← mul_assoc, e1, e2, List.foldl_cons], o2⟩
    have he : v / 16 ^ k % 16 ≤ 4 := hv.2 k hkn
    set S := nfFrom (k + 1) ((vecL n v).drop (k + 1)) with hS
    have hSl : ∀ j ∈ S, k < j ∧ j < n := fun j hj => by
      have := nfFrom_mem _ _ _ hj
      simp only [List.length_drop, vecL, List.length_map, List.length_range] at this
      omega
    have hSD : ∀ j ∈ S.flatMap (dT T n k), k < j ∧ j < n := by
      intro j hj
      obtain ⟨i, hi, hj'⟩ := List.mem_flatMap.1 hj
      exact hDl k i hmk (hSl i hi).1 (hSl i hi).2 j hj'
    have hconj : evW x S * x k = x k * evW x (S.flatMap (dT T n k)) :=
      evW_mul_of_conj x (fun j h1 h2 => hD k j hmk h1 h2) S hSl
    have hmain : evV x n v * x k = evW x (nfFrom 0 ((vecL n v).take k)) *
        x k ^ (v / 16 ^ k % 16 + 1) * evW x (S.flatMap (dT T n k)) := by
      rw [evV_split x n v k hkn, mul_assoc, hconj, pow_succ]
      simp only [mul_assoc]
    have hsuf : n - (n - 1 - k) = k + 1 := by omega
    rw [mulR_succ, sufL_eq _ _ _ _ _ _ _ (by omega), hsuf, ← hS]
    split_ifs with h4
    · rw [appW_eq]
      have oA : okV n (v % 16 ^ k) := by
        have := okV_set n v k 0 hkn hv (by norm_num)
        rwa [zero_mul, add_zero] at this
      have eA : evV x n (v % 16 ^ k) = evW x (nfFrom 0 ((vecL n v).take k)) := by
        have := evV_set x n v k 0 hkn (by norm_num)
        rwa [zero_mul, add_zero, pow_zero, mul_one] at this
      obtain ⟨e1, o1⟩ := hfold (pT PT k) _ oA (hPl k hmk hkn)
      obtain ⟨e2, o2⟩ := hfold (S.flatMap (dT T n k)) _ o1 hSD
      have h5 : x k ^ (v / 16 ^ k % 16 + 1) = evW x (pT PT k) := by
        rw [h4]
        exact hP k hmk hkn
      refine ⟨?_, o2⟩
      rw [hmain, h5, ← eA, e1, e2, pT]
    · obtain ⟨e2, o2⟩ := hfold (S.flatMap (dT T n k)) _
        (okV_set n v k (v / 16 ^ k % 16 + 1) hkn hv (by omega)) hSD
      refine ⟨?_, o2⟩
      rw [hmain, ← evV_set x n v k _ hkn (by omega), e2]

theorem colR_sound (n T PT m : ℕ)
    (hD : ∀ k j, m ≤ k → k < j → j < n → x j * x k = x k * evW x (dT T n k j))
    (hDl : ∀ k j, m ≤ k → k < j → j < n → ∀ l ∈ dT T n k j, k < l ∧ l < n)
    (hP : ∀ k, m ≤ k → k < n → x k ^ 5 = evW x (pT PT k))
    (hPl : ∀ k, m ≤ k → k < n → ∀ l ∈ pT PT k, k < l ∧ l < n)
    {l : List ℕ} (hl : ∀ j ∈ l, m ≤ j ∧ j < n) : evW x l = evV x n (colR n T PT l) := by
  have key : ∀ (l : List ℕ) (w : ℕ), okV n w → (∀ j ∈ l, m ≤ j ∧ j < n) →
      evV x n w * evW x l = evV x n (l.foldl (fun w j => mulR n T PT n w j) w) := by
    intro l
    induction l with
    | nil => intro w _ _; rw [evW_nil, mul_one]; rfl
    | cons j l ihl =>
      intro w hw hl
      have hj := hl j (List.mem_cons_self ..)
      obtain ⟨e1, o1⟩ := mulR_sound x n T PT m hD hDl hP hPl n w j (by omega) hj.1 hj.2 hw
      rw [evW_cons, ← mul_assoc, e1, List.foldl_cons,
        ihl _ o1 fun j' hj' => hl j' (List.mem_cons_of_mem _ hj')]
  have := key l 0 (okV_zero n) hl
  rwa [evV_zero, one_mul, ← colR_eq] at this

theorem colE_sound (n T PT m : ℕ)
    (hD : ∀ k j, m ≤ k → k < j → j < n → x j * x k = x k * evW x (dT T n k j))
    (hDl : ∀ k j, m ≤ k → k < j → j < n → ∀ l ∈ dT T n k j, k < l ∧ l < n)
    (hP : ∀ k, m ≤ k → k < n → x k ^ 5 = evW x (pT PT k))
    (hPl : ∀ k, m ≤ k → k < n → ∀ l ∈ pT PT k, k < l ∧ l < n)
    {l l' : List ℕ} (hl : ∀ j ∈ l, m ≤ j ∧ j < n) (hl' : ∀ j ∈ l', m ≤ j ∧ j < n)
    (h : colE n T PT l l' = true) : evW x l = evW x l' := by
  rw [colR_sound x n T PT m hD hDl hP hPl hl, colR_sound x n T PT m hD hDl hP hPl hl',
    Nat.eq_of_beq_eq_true h]

theorem conjD_of_checks (n T PT m₀ : ℕ) (C : ℕ → ℕ → List ℕ)
    (hC : ∀ k m, m₀ ≤ k → k < m → m < n → x k * x m = evW x (C k m) * x k)
    (hCl : ∀ k m, m₀ ≤ k → k < m → m < n → ∀ l ∈ C k m, k < l ∧ l < n)
    (hDl : ∀ k j, m₀ ≤ k → k < j → j < n → ∀ l ∈ dT T n k j, k < l ∧ l < n)
    (hP : ∀ k, m₀ ≤ k → k < n → x k ^ 5 = evW x (pT PT k))
    (hPl : ∀ k, m₀ ≤ k → k < n → ∀ l ∈ pT PT k, k < l ∧ l < n)
    (hchk : ∀ k j, m₀ ≤ k → k < j → j < n →
      colE n T PT ((dT T n k j).flatMap (C k)) [j] = true) :
    ∀ k j, m₀ ≤ k → k < j → j < n → x j * x k = x k * evW x (dT T n k j) := by
  suffices h : ∀ t k, n - k ≤ t → m₀ ≤ k → ∀ j, k < j → j < n →
      x j * x k = x k * evW x (dT T n k j) from
    fun k j hk hkj hjn => h (n - k) k le_rfl hk j hkj hjn
  intro t
  induction t with
  | zero => intro k hk _ j hkj hjn; omega
  | succ t ih =>
    intro k hk hmk j hkj hjn
    have hD' : ∀ k' j', k + 1 ≤ k' → k' < j' → j' < n → x j' * x k' = x k' * evW x (dT T n k' j') :=
      fun k' j' h1 h2 h3 => ih k' (by omega) (by omega) j' h2 h3
    have hlD : ∀ l ∈ (dT T n k j).flatMap (C k), k + 1 ≤ l ∧ l < n := by
      intro l hl
      obtain ⟨i, hi, hl'⟩ := List.mem_flatMap.1 hl
      have := hDl k j hmk hkj hjn i hi
      have := hCl k i hmk this.1 this.2 l hl'
      omega
    have e := colE_sound x n T PT (k + 1) hD'
      (fun k' j' h1 h2 h3 => hDl k' j' (by omega) h2 h3)
      (fun k' h1 h2 => hP k' (by omega) h2) (fun k' h1 h2 => hPl k' (by omega) h2)
      hlD (fun l hl => by rw [List.mem_singleton.1 hl]; omega) (hchk k j hmk hkj hjn)
    rw [evW_cons, evW_nil, mul_one] at e
    rw [← e, ← mul_evW_of_rel x (fun m h1 h2 => hC k m hmk h1 h2) _ (hDl k j hmk hkj hjn)]

end Sound

section Images

theorem evW_conj (n : G) : ∀ l : List ℕ, evW (fun m => n * x m * n⁻¹) l = n * evW x l * n⁻¹
  | [] => by simp [evW]
  | m :: l => by rw [evW_cons, evW_cons, evW_conj n l]; group

theorem evW_of_images {y : ℕ → G} {R : ℕ → List ℕ} :
    ∀ l : List ℕ, (∀ m ∈ l, y m = evW x (R m)) → evW y l = evW x (l.flatMap R)
  | [], _ => rfl
  | m :: l, h => by
    rw [evW_cons, List.flatMap_cons, evW_append, h m (List.mem_cons_self ..),
      evW_of_images l fun m' hm' => h m' (List.mem_cons_of_mem _ hm')]

theorem eq_of_pow_eq {a b : G} {e e' : ℕ} (ha : a ^ 5 = 1) (hb : b ^ 5 = 1) (h : a ^ e = b ^ e)
    (hee : (e * e') % 5 = 1) : a = b := by
  have key : ∀ c : G, c ^ 5 = 1 → c ^ (e * e') = c := fun c hc => by
    rw [← Nat.div_add_mod (e * e') 5, hee, pow_add, pow_mul, hc, one_pow, one_mul, pow_one]
  rw [← key a ha, ← key b hb, pow_mul, pow_mul, h]

theorem image_of_rel {n : G} {R : ℕ → List ℕ} (k e e' : ℕ) (lw L1 L2 : List ℕ)
    (hrel : evW x lw = evW x (L1 ++ List.replicate e k ++ L2))
    (hK : ∀ m ∈ lw ++ L1 ++ L2, n * x m = evW x (R m) * n)
    (hcol : evW x (lw.flatMap R) =
      evW x (L1.flatMap R ++ (List.replicate e k).flatMap R ++ L2.flatMap R))
    (hk5 : x k ^ 5 = 1) (hR5 : evW x (R k) ^ 5 = 1) (hee : (e * e') % 5 = 1) :
    n * x k = evW x (R k) * n := by
  set y : ℕ → G := fun m => n * x m * n⁻¹ with hy
  have hyK : ∀ m ∈ lw ++ L1 ++ L2, y m = evW x (R m) := fun m hm => by
    rw [hy]
    simp only
    rw [hK m hm, mul_inv_cancel_right]
  have hrel' : evW y lw = evW y (L1 ++ List.replicate e k ++ L2) := by
    rw [hy, evW_conj, evW_conj, hrel]
  have h1 : evW y lw = evW x (lw.flatMap R) :=
    evW_of_images x lw fun m hm => hyK m (List.mem_append_left _ (List.mem_append_left _ hm))
  have h2 : evW y L1 = evW x (L1.flatMap R) :=
    evW_of_images x L1 fun m hm => hyK m (List.mem_append_left _ (List.mem_append_right _ hm))
  have h3 : evW y L2 = evW x (L2.flatMap R) :=
    evW_of_images x L2 fun m hm => hyK m (List.mem_append_right _ hm)
  have h4 : evW x ((List.replicate e k).flatMap R) = evW x (R k) ^ e := evW_flatMap_replicate x e k
  rw [evW_append, evW_append, h1, h2, h3, evW_replicate, hcol, evW_append, evW_append, h4] at hrel'
  have hpow : y k ^ e = evW x (R k) ^ e := (mul_left_cancel (mul_right_cancel hrel')).symm
  have hy5 : y k ^ 5 = 1 := by rw [hy]; simp only [conj_pow, hk5, mul_one, mul_inv_cancel]
  have := eq_of_pow_eq hy5 hR5 hpow hee
  rw [hy] at this
  simp only at this
  rw [← this, inv_mul_cancel_right]

end Images

end CFSG.KC.PcCollect

end

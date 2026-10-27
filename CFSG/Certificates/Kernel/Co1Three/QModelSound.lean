module

public import Certificates.Data.Kernel.Co1Three.QModel
public import CFSG.Certificates.Kernel.Co1Three.ActSound
public import CFSG.Certificates.Kernel.Spor.RawOrbEval
import CFSG.Certificates.Kernel.Spor.Loops

public section

namespace CFSG.KC.Co1Cl

open CFSG.KC.Enum CFSG.KC.Co1F2 CFSG.KC.Co1B

theorem addVK_lt {p : Nat} (hp : 0 < p) : ∀ n x y : Nat, addVK p n x y < p ^ n
  | 0, _, _ => by
    change 0 < p ^ 0
    rw [pow_zero]
    exact Nat.one_pos
  | n + 1, x, y => by
    rw [addVK_succ, pow_succ]
    have h1 := Nat.mod_lt (x % p + y % p) hp
    have h2 := addVK_lt hp n (x / p) (y / p)
    calc (x % p + y % p) % p + p * addVK p n (x / p) (y / p)
        < p + p * addVK p n (x / p) (y / p) := by omega
      _ = p * (addVK p n (x / p) (y / p) + 1) := by ring
      _ ≤ p * p ^ n := Nat.mul_le_mul_left _ h2
      _ = p ^ n * p := Nat.mul_comm _ _

theorem actK_lt {p n : Nat} (hp : 0 < p) :
    ∀ (rows : List Nat) (v acc : Nat), acc < p ^ n → actK p n rows v acc < p ^ n
  | [], _, _, h => h
  | r :: rows, v, acc, h => by
    have iter : ∀ e, Nat.rec (motive := fun _ => Nat) acc
        (fun _ b => strictN b fun b => addVK p n b r) e < p ^ n := by
      intro e
      cases e with
      | zero => exact h
      | succ e =>
        change strictN (Nat.rec (motive := fun _ => Nat) acc
          (fun _ b => strictN b fun b => addVK p n b r) e) (fun b => addVK p n b r) < p ^ n
        rw [strictN_eq]
        exact addVK_lt hp n _ _
    change strictN (v % p) (fun e => strictN (Nat.rec (motive := fun _ => Nat) acc
      (fun _ b => strictN b fun b => addVK p n b r) e) fun acc' => actK p n rows (v / p) acc') < p ^ n
    rw [strictN_eq, strictN_eq]
    exact actK_lt hp rows _ _ (iter _)

theorem addVK_addK (p m : Nat) : ∀ k x y : Nat,
    addVK p (k + m) x y = addVK p k x y + p ^ k * addVK p m (x / p ^ k) (y / p ^ k)
  | 0, x, y => by
    have e : addVK p 0 x y = 0 := rfl
    rw [Nat.zero_add, pow_zero, Nat.div_one, Nat.div_one, one_mul, e, Nat.zero_add]
  | k + 1, x, y => by
    rw [Nat.add_right_comm, addVK_succ p (k + m), addVK_succ p k, addVK_addK p m k, pow_succ',
      ← Nat.div_div_eq_div_mul, ← Nat.div_div_eq_div_mul]
    ring

theorem addVK_modK {p : Nat} (hp : 0 < p) : ∀ k x y : Nat,
    addVK p k x y = addVK p k (x % p ^ k) (y % p ^ k)
  | 0, _, _ => rfl
  | k + 1, x, y => by
    have e1 : ∀ z, z % p ^ (k + 1) % p = z % p := fun z =>
      Nat.mod_mod_of_dvd z (dvd_pow_self p (Nat.succ_ne_zero k))
    have e2 : ∀ z, z % p ^ (k + 1) / p % p ^ k = z / p % p ^ k := fun z => by
      rw [pow_succ', Nat.mod_mul_right_div_self, Nat.mod_mod]
    rw [addVK_succ p k x y, addVK_succ p k (x % p ^ (k + 1)) (y % p ^ (k + 1)), e1, e1,
      addVK_modK hp k (x / p) (y / p),
      addVK_modK hp k (x % p ^ (k + 1) / p) (y % p ^ (k + 1) / p), e2, e2]

theorem addTK_eq {ADT : Nat} (h : adtQK ADT = true) {x y : Nat} (hx : x < 729) (hy : y < 729) :
    addTK ADT x y = addVK 3 6 x y := by
  have hfield : ∀ a < 27, ∀ b < 27,
      Nat.land (Nat.shiftRight ADT (5 * (27 * a + b))) 31 = addVK 3 3 a b := by
    intro a ha b hb
    have e : Nat.land (Nat.shiftRight ADT (5 * (27 * a + b))) 31 =
        addVK 3 3 ((27 * a + b) / 27) ((27 * a + b) % 27) :=
      Nat.eq_of_beq_eq_true (CFSG.KS.allN_spec h (27 * a + b) (by
        change 27 * a + b < 729
        omega))
    have e1 : (27 * a + b) / 27 = a := by omega
    have e2 : (27 * a + b) % 27 = b := by omega
    rw [e1, e2] at e
    exact e
  change Nat.land (Nat.shiftRight ADT (5 * (27 * (x % 27) + y % 27))) 31 +
    27 * Nat.land (Nat.shiftRight ADT (5 * (27 * (x / 27) + y / 27))) 31 = _
  rw [hfield _ (Nat.mod_lt _ (by omega)) _ (Nat.mod_lt _ (by omega)),
    hfield _ (by omega) _ (by omega)]
  have e3 : addVK 3 3 (x % 27) (y % 27) = addVK 3 3 x y := (addVK_modK (by omega) 3 x y).symm
  have e4 : addVK 3 6 x y = addVK 3 3 x y + 27 * addVK 3 3 (x / 27) (y / 27) :=
    addVK_addK 3 3 3 x y
  rw [e3, e4]

@[expose] noncomputable def atF (AT : List Nat) (l v : Nat) : Nat :=
  fld(getL (nat_lit 0) AT l, Nat.mul (nat_lit 10) v, nat_lit 1023)

theorem addVK_comm (p : Nat) : ∀ n x y : Nat, addVK p n x y = addVK p n y x
  | 0, _, _ => rfl
  | n + 1, x, y => by rw [addVK_succ, addVK_succ, Nat.add_comm (x % p), addVK_comm p n]

theorem addVK_mod {p : Nat} (n x y : Nat) : addVK p (n + 1) x y % p = (x % p + y % p) % p := by
  rw [addVK_succ, Nat.add_mul_mod_self_left, Nat.mod_mod]

theorem addVK_div {p : Nat} (hp : 0 < p) (n x y : Nat) :
    addVK p (n + 1) x y / p = addVK p n (x / p) (y / p) := by
  rw [addVK_succ, Nat.add_mul_div_left _ _ hp, Nat.div_eq_of_lt (Nat.mod_lt _ hp), Nat.zero_add]

theorem addVK_assoc {p : Nat} (hp : 0 < p) : ∀ n x y z : Nat,
    addVK p n (addVK p n x y) z = addVK p n x (addVK p n y z)
  | 0, _, _, _ => rfl
  | n + 1, x, y, z => by
    rw [addVK_succ p n (addVK p (n + 1) x y), addVK_succ p n x (addVK p (n + 1) y z), addVK_mod,
      addVK_mod, addVK_div hp, addVK_div hp, addVK_assoc hp n, Nat.mod_add_mod,
      Nat.add_mod_mod (x % p) (y % p + z % p), Nat.add_assoc]

theorem addVK_zero {p : Nat} (hp : 0 < p) : ∀ n x : Nat, addVK p n x 0 = x % p ^ n
  | 0, x => by rw [pow_zero, Nat.mod_one]; rfl
  | n + 1, x => by
    rw [addVK_succ, Nat.zero_mod, Nat.add_zero, Nat.mod_mod, Nat.zero_div, addVK_zero hp n,
      pow_succ', Nat.mod_mul]

theorem actK_cons (p n r : Nat) (rows : List Nat) (v acc : Nat) :
    actK p n (r :: rows) v acc = actK p n rows (v / p)
      (Nat.rec (motive := fun _ => Nat) acc (fun _ a => strictN a fun a => addVK p n a r) (v % p)) := by
  change strictN (v % p) (fun e => strictN (Nat.rec (motive := fun _ => Nat) acc
    (fun _ a => strictN a fun a => addVK p n a r) e) fun acc' => actK p n rows (v / p) acc') = _
  rw [strictN_eq, strictN_eq]

theorem iterK_succ (p n r acc e : Nat) :
    Nat.rec (motive := fun _ => Nat) acc (fun _ a => strictN a fun a => addVK p n a r) (e + 1) =
      addVK p n (Nat.rec (motive := fun _ => Nat) acc
        (fun _ a => strictN a fun a => addVK p n a r) e) r := strictN_eq _ _

theorem actK_addVK {p n : Nat} (hp : 0 < p) : ∀ (rows : List Nat) (v b c : Nat),
    actK p n rows v (addVK p n b c) = addVK p n (actK p n rows v b) c
  | [], _, _, _ => rfl
  | r :: rows, v, b, c => by
    have iter : ∀ e, Nat.rec (motive := fun _ => Nat) (addVK p n b c)
        (fun _ a => strictN a fun a => addVK p n a r) e =
        addVK p n (Nat.rec (motive := fun _ => Nat) b
          (fun _ a => strictN a fun a => addVK p n a r) e) c := by
      intro e
      induction e with
      | zero => rfl
      | succ e ih =>
        rw [iterK_succ, iterK_succ, ih, addVK_assoc hp, addVK_comm p n c, ← addVK_assoc hp]
    rw [actK_cons, actK_cons, iter, actK_addVK hp rows]

theorem actK_digit {p n : Nat} (hp : 0 < p) : ∀ (rows : List Nat) (j m d acc : Nat), d + 1 < p →
    acc < p ^ n → actK p n rows (p ^ j * (p * m + d + 1)) acc =
      addVK p n (actK p n rows (p ^ j * (p * m + d)) acc) (getL 0 rows j)
  | [], j, _, _, acc, _, hacc => by
    change acc = addVK p n acc 0
    rw [addVK_zero hp, Nat.mod_eq_of_lt hacc]
  | r :: rows, 0, m, d, acc, hd, _ => by
    have e1 : p ^ 0 * (p * m + d + 1) % p = d + 1 := by
      rw [pow_zero, one_mul, Nat.add_assoc, Nat.mul_add_mod, Nat.mod_eq_of_lt hd]
    have e2 : p ^ 0 * (p * m + d + 1) / p = m := by
      rw [pow_zero, one_mul, Nat.add_assoc, Nat.mul_add_div hp, Nat.div_eq_of_lt hd, Nat.add_zero]
    have e3 : p ^ 0 * (p * m + d) % p = d := by
      rw [pow_zero, one_mul, Nat.mul_add_mod, Nat.mod_eq_of_lt (by omega)]
    have e4 : p ^ 0 * (p * m + d) / p = m := by
      rw [pow_zero, one_mul, Nat.mul_add_div hp, Nat.div_eq_of_lt (by omega), Nat.add_zero]
    rw [actK_cons, actK_cons, e1, e2, e3, e4, iterK_succ, actK_addVK hp]
    rfl
  | r :: rows, j + 1, m, d, acc, hd, hacc => by
    have e1 : ∀ x, p ^ (j + 1) * x % p = 0 := fun x => by
      rw [pow_succ', mul_assoc, Nat.mul_mod_right]
    have e2 : ∀ x, p ^ (j + 1) * x / p = p ^ j * x := fun x => by
      rw [pow_succ', mul_assoc, Nat.mul_div_cancel_left _ hp]
    rw [actK_cons, actK_cons, e1, e1, e2, e2]
    exact actK_digit hp rows j m d acc hd hacc

theorem lowJK_spec : ∀ f v : Nat, v < 3 ^ f → 0 < v →
    ∃ m d, d + 1 < 3 ∧ v = 3 ^ lowJK f v * (3 * m + d + 1)
  | 0, v, h, h0 => by
    rw [pow_zero] at h
    omega
  | f + 1, v, h, h0 => by
    have e : lowJK (f + 1) v = Bool.rec (motive := fun _ => Nat) 0 (Nat.succ (lowJK f (v / 3)))
        (Nat.beq (v % 3) 0) := rfl
    rw [pow_succ] at h
    by_cases hv : v % 3 = 0
    · have hb : Nat.beq (v % 3) 0 = true := by rw [hv]; rfl
      obtain ⟨m, d, hd, hm⟩ := lowJK_spec f (v / 3) (by omega) (by omega)
      refine ⟨m, d, hd, ?_⟩
      rw [e, hb]
      change v = 3 ^ (lowJK f (v / 3) + 1) * _
      rw [pow_succ, mul_comm (3 ^ lowJK f (v / 3)) 3, mul_assoc, ← hm]
      omega
    · have hb : Nat.beq (v % 3) 0 = false :=
        Bool.eq_false_iff.2 fun h' => hv (Nat.eq_of_beq_eq_true h')
      refine ⟨v / 3, v % 3 - 1, by omega, ?_⟩
      rw [e, hb]
      change v = 3 ^ 0 * _
      rw [pow_zero, one_mul]
      omega

theorem atQK_eq {N ADT : Nat} {A : List (List Nat)} {AT : List Nat} (hadt : adtQK ADT = true)
    (h : atQK N ADT A AT = true) (hA : ∀ l < N, ∀ r ∈ getLL A l, r < 729) {l v : Nat}
    (hl : l < N) (hv : v < 729) : atF AT l v = actK 3 6 (getLL A l) v 0 := by
  have h3 : (3 : Nat) ^ 6 = 729 := by norm_num
  unfold atQK at h
  rw [brec_eq_true] at h
  rcases h with ⟨-, h⟩ | ⟨-, h⟩
  swap
  · exact absurd h (by decide)
  have hrow := CFSG.KS.allN_spec h l hl
  beta_reduce at hrow
  rw [strictB_eq] at hrow
  induction v using Nat.strong_induction_on with
  | _ v ih =>
    have hv' := CFSG.KS.allN_spec hrow v hv
    beta_reduce at hv'
    rw [brec_eq_true] at hv'
    rcases Nat.eq_zero_or_pos v with h0 | hpos
    · subst h0
      rw [actK_zero]
      rcases hv' with ⟨-, hb⟩ | ⟨hc, -⟩
      · exact Nat.eq_of_beq_eq_true hb
      · exact absurd hc (by decide)
    rcases hv' with ⟨hc, -⟩ | ⟨-, hb⟩
    · exact absurd (Nat.eq_of_beq_eq_true hc) (Nat.pos_iff_ne_zero.1 hpos)
    rw [strictB_eq] at hb
    have key : atF AT l v = addTK ADT (atF AT l (v - 3 ^ lowJK 6 v))
        (getL 0 (getLL A l) (lowJK 6 v)) := Nat.eq_of_beq_eq_true hb
    obtain ⟨m, d, hd, hm⟩ := lowJK_spec 6 v (by rw [h3]; exact hv) hpos
    generalize lowJK 6 v = j at key hm
    have hj : 0 < 3 ^ j := Nat.pow_pos (by norm_num)
    have hlt : v - 3 ^ j < v := Nat.sub_lt hpos hj
    have hr : getL 0 (getLL A l) j < 729 := by
      rw [getL_eq]
      rcases Nat.lt_or_ge j (getLL A l).length with hj' | hj'
      · rw [List.getD_eq_getElem _ _ hj']
        exact hA l hl _ (List.getElem_mem hj')
      · rw [List.getD_eq_default _ _ hj']
        norm_num
    have hb' := actK_lt (n := 6) (by norm_num : 0 < 3) (getLL A l) (v - 3 ^ j) 0 (by norm_num)
    rw [h3] at hb'
    rw [key, ih _ hlt (by omega), addTK_eq hadt hb' hr]
    have e1 : v - 3 ^ j = 3 ^ j * (3 * m + d) := by
      have : 3 ^ j * (3 * m + d + 1) = 3 ^ j * (3 * m + d) + 3 ^ j := by ring
      omega
    rw [e1, hm]
    exact (actK_digit (by norm_num) (getLL A l) j m d 0 hd (by positivity)).symm

theorem mulQK_eq {N ADT : Nat} {TT : List (List Nat)} {A : List (List Nat)} {AT : List Nat}
    (hadt : adtQK ADT = true) (hat : atQK N ADT A AT = true)
    (hA : ∀ l < N, ∀ r ∈ getLL A l, r < 729) {x y : Nat} (hy : y / 729 < N) :
    mulQK ADT TT AT x y =
      729 * (getL 0 (getLL TT (x / 729)) (y / 729) / 729) +
        addVK 3 6 (addVK 3 6 (getL 0 (getLL TT (x / 729)) (y / 729) % 729) (y % 729))
          (actK 3 6 (getLL A (y / 729)) (x % 729) 0) := by
  have e : mulQK ADT TT AT x y =
      729 * (getL 0 (getLL TT (x / 729)) (y / 729) / 729) +
        addTK ADT (addTK ADT (getL 0 (getLL TT (x / 729)) (y / 729) % 729) (y % 729))
          (atF AT (y / 729) (x % 729)) := by
    unfold mulQK
    simp only [strictN_eq]
    rfl
  have h1 : (3 : Nat) ^ 6 = 729 := by norm_num
  have hw := Nat.mod_lt y (show 0 < 729 by norm_num)
  have hu := Nat.mod_lt (getL 0 (getLL TT (x / 729)) (y / 729)) (show 0 < 729 by norm_num)
  have hv := Nat.mod_lt x (show 0 < 729 by norm_num)
  rw [e, atQK_eq hadt hat hA hy hv, addTK_eq hadt hu hw]
  have ha := addVK_lt (show 0 < 3 by norm_num) 6
    (getL 0 (getLL TT (x / 729)) (y / 729) % 729) (y % 729)
  have hb := actK_lt (n := 6) (show 0 < 3 by norm_num) (getLL A (y / 729)) (x % 729) 0
    (by norm_num)
  rw [h1] at ha hb
  rw [addTK_eq hadt ha hb]

theorem recK_mul {TS : Nat → Nat} {S : List Nat} {lo k c : Nat} (h : recK TS S lo k c = true)
    (h0 : Nat.land c 1 = 0) :
    TS k = mulWK (TS (refK S S.length lo (Nat.land (Nat.shiftRight c 1) 1048575)))
      (TS (refK S S.length lo (Nat.shiftRight c 21))) := by
  unfold recK at h
  simp only [strictB_eq, lenL_eq, brec_eq_true, Bool.false_eq_true, and_false, or_false] at h
  obtain ⟨-, -, h3⟩ := h
  rcases h3 with ⟨h4, -⟩ | ⟨-, -, h5⟩
  · rw [h0] at h4
    exact absurd h4 (by decide)
  · exact Nat.eq_of_beq_eq_true h5

theorem relQK_spec {P N tb qb : Nat} {Q : List (List Nat)} {RL : List Nat}
    (h : relQK P N tb qb Q RL = true) {i : Nat} (hi : i < 2 * N) :
    getL 0 RL i < P * N ∧ getLL Q i = [2 * (tb + i / 2), 2 * (qb + i % 2),
      8 * (getL 0 RL i % P) + 1, 2 * (tb + getL 0 RL i / P)] := by
  unfold relQK at h
  have h' := CFSG.KS.Raw.Orb.allN_iff.1 h i hi
  simp only [strictB_eq, brec_eq_true, Bool.false_eq_true, and_false, or_false] at h'
  obtain ⟨h1, h2⟩ := h'
  rw [Nat.blt_eq] at h1
  exact ⟨h1, eqLK_sound _ _ h2⟩

theorem tabQK_spec {p n P N : Nat} {A B : List (List Nat)} {RL W : List Nat}
    {TT : List (List Nat)} (h : tabQK p n P N A B RL W TT = true) {k l : Nat} (hk : k < N)
    (hl : l < N) :
    getL 0 (getLL TT k) l < P * N ∧
      ((l = 0 ∧ getL 0 (getLL TT k) l = P * k) ∨
        (l ≠ 0 ∧ Nat.land (getL 0 W l) 1 = 0 ∧
          3 ≤ Nat.land (Nat.shiftRight (getL 0 W l) 1) 1048575 ∧
          Nat.land (Nat.shiftRight (getL 0 W l) 1) 1048575 - 3 < l ∧
          Nat.shiftRight (getL 0 W l) 21 < 2 ∧
          getL 0 (getLL TT k) l =
            P * (getL 0 RL (2 * (getL 0 (getLL TT k)
              (Nat.land (Nat.shiftRight (getL 0 W l) 1) 1048575 - 3) / P) +
                Nat.shiftRight (getL 0 W l) 21) / P) +
            actK p n (getLL A (getL 0 RL (2 * (getL 0 (getLL TT k)
              (Nat.land (Nat.shiftRight (getL 0 W l) 1) 1048575 - 3) / P) +
                Nat.shiftRight (getL 0 W l) 21) / P))
              (getL 0 RL (2 * (getL 0 (getLL TT k)
                (Nat.land (Nat.shiftRight (getL 0 W l) 1) 1048575 - 3) / P) +
                  Nat.shiftRight (getL 0 W l) 21) % P)
              (actK p n (getLL B (Nat.shiftRight (getL 0 W l) 21))
                (getL 0 (getLL TT k) (Nat.land (Nat.shiftRight (getL 0 W l) 1) 1048575 - 3) % P)
                0))) := by
  unfold tabQK at h
  simp only [brec_eq_true, Bool.false_eq_true, and_false, or_false] at h
  have hr := CFSG.KS.Raw.Orb.allN_iff.1 h.2 k hk
  simp only [brec_eq_true, Bool.false_eq_true, and_false, or_false] at hr
  have he := CFSG.KS.Raw.Orb.allN_iff.1 hr.2 l hl
  unfold tabEntK at he
  simp only [strictB_eq, brec_eq_true, Bool.false_eq_true, and_false, or_false] at he
  obtain ⟨h1, h2⟩ := he
  rw [Nat.blt_eq] at h1
  refine ⟨h1, ?_⟩
  rcases h2 with ⟨h3, h4⟩ | ⟨h3, h4, h5, h6, h7, h8⟩
  · exact Or.inl ⟨Nat.eq_of_beq_eq_true h3, Nat.eq_of_beq_eq_true h4⟩
  · rw [Nat.ble_eq] at h5
    rw [Nat.blt_eq] at h6 h7
    exact Or.inr ⟨Nat.ne_of_beq_eq_false h3, Nat.eq_of_beq_eq_true h4, h5, h6, h7,
      Nat.eq_of_beq_eq_true h8⟩

@[expose] def FusAt (N ADT : Nat) (TT : List (List Nat)) (AT GC RP : List Nat) (DP x f : Nat) :
    Prop :=
  (depK DP x = 0 → mulQK ADT TT AT (mulQK ADT TT AT x x) x ≠ 0) ∧
  (depK DP x = 1 → x ∈ RP) ∧
  (depK DP x ≠ 0 → depK DP x ≠ 1 → f % 8 < GC.length ∧ 729 ≤ f / 8 ∧ f / 8 < 729 * N ∧
    depK DP (f / 8) + 1 = depK DP x ∧
    mulQK ADT TT AT x (getL 0 GC (f % 8)) = mulQK ADT TT AT (getL 0 GC (f % 8)) (f / 8))

theorem fusFromK_sound {N ADT : Nat} {TT : List (List Nat)} {AT GC RP : List Nat} {DP k : Nat} :
    ∀ (FL : List Nat) (v₀ : Nat), fusFromK N ADT TT AT GC RP DP k FL v₀ = true →
      ∀ v, v₀ ≤ v → v < 729 → FusAt N ADT TT AT GC RP DP (729 * k + v) (FL.getD (v - v₀) 0)
  | [], v₀, h, v, h1, h2 => by
    have e : v₀ = 729 := Nat.eq_of_beq_eq_true h
    omega
  | f :: FL, v₀, h, v, h1, h2 => by
    change strictB v₀ (fun v => strictB (Nat.add (Nat.mul (nat_lit 729) k) v) fun x =>
      strictB (depK DP x) fun d =>
      bAnd(bIf(Nat.beq d (nat_lit 0),
          strictB (mulQK ADT TT AT x x) fun x₂ =>
            Bool.not (Nat.beq (mulQK ADT TT AT x₂ x) (nat_lit 0)),
        bIf(Nat.beq d (nat_lit 1), memK x RP,
          strictB (Nat.div f (nat_lit 8)) fun c => strictB (Nat.mod f (nat_lit 8)) fun g =>
          strictB (getL (nat_lit 0) GC g) fun h =>
          bAnd(Nat.blt g (lenL GC), bAnd(Nat.ble (nat_lit 729) c,
          bAnd(Nat.blt c (Nat.mul (nat_lit 729) N), bAnd(Nat.beq (Nat.succ (depK DP c)) d,
            Nat.beq (mulQK ADT TT AT x h) (mulQK ADT TT AT h c))))))),
        fusFromK N ADT TT AT GC RP DP k FL (Nat.succ v))) = true at h
    simp only [strictB_eq] at h
    rw [brec_eq_true] at h
    simp only [Bool.false_eq_true, and_false, or_false] at h
    obtain ⟨h3, h4⟩ := h
    rcases Nat.lt_or_ge v₀ v with hlt | hge
    · have := fusFromK_sound FL (v₀ + 1) h4 v hlt h2
      have e : v - v₀ = (v - (v₀ + 1)) + 1 := by omega
      rwa [e, List.getD_cons_succ]
    · have e : v = v₀ := by omega
      subst e
      rw [Nat.sub_self, List.getD_cons_zero]
      have hx : Nat.add (Nat.mul 729 k) v = 729 * k + v := rfl
      rw [hx] at h3
      refine ⟨fun hd => ?_, fun hd => ?_, fun hd0 hd1 => ?_⟩
      · rw [brec_eq_true] at h3
        rcases h3 with ⟨-, h5⟩ | ⟨h5, -⟩
        · intro h6
          change (!(mulQK ADT TT AT (mulQK ADT TT AT (729 * k + v) (729 * k + v))
            (729 * k + v)).beq 0) = true at h5
          rw [h6] at h5
          exact absurd h5 (by decide)
        · rw [hd] at h5
          exact absurd h5 (by decide)
      · rw [brec_eq_true] at h3
        rcases h3 with ⟨h5, -⟩ | ⟨-, h5⟩
        · have := Nat.eq_of_beq_eq_true h5
          omega
        · rw [brec_eq_true] at h5
          rcases h5 with ⟨-, h6⟩ | ⟨h6, -⟩
          · exact memK_sound h6
          · rw [hd] at h6
            exact absurd h6 (by decide)
      · rw [brec_eq_true] at h3
        rcases h3 with ⟨h5, -⟩ | ⟨-, h5⟩
        · exact absurd (Nat.eq_of_beq_eq_true h5) hd0
        · rw [brec_eq_true] at h5
          rcases h5 with ⟨h6, -⟩ | ⟨-, h6⟩
          · exact absurd (Nat.eq_of_beq_eq_true h6) hd1
          · simp only [strictB_eq, brec_eq_true, Bool.false_eq_true, and_false, or_false,
              lenL_eq, getL_eq] at h6
            obtain ⟨g1, g2, g3, g4, g5⟩ := h6
            rw [Nat.blt_eq] at g1 g3
            rw [Nat.ble_eq] at g2
            exact ⟨g1, g2, g3, Nat.eq_of_beq_eq_true g4, by
              rw [getL_eq]
              exact Nat.eq_of_beq_eq_true g5⟩

theorem fusQK_sound {N ADT : Nat} {TT : List (List Nat)} {AT GC RP : List Nat} {DP k : Nat}
    {FL : List Nat} (h : fusQK N ADT TT AT GC RP DP k FL = true) {v : Nat} (hv : v < 729) :
    FusAt N ADT TT AT GC RP DP (729 * k + v) (FL.getD v 0) := by
  have := fusFromK_sound FL 0 h v (Nat.zero_le v) hv
  rwa [Nat.sub_zero] at this

theorem isConj_of_mul' {M : Type*} [Group M] {x y g : M} (h : x * g = g * y) : IsConj y x :=
  isConj_iff.2 ⟨g, by rw [← h, mul_inv_cancel_right]⟩

theorem fus_conj {M : Type*} [Group M] {N ADT : Nat} {TT : List (List Nat)} {AT GC RP : List Nat}
    {DP : Nat} {FL : Nat → List Nat} (mdl : Nat → M)
    (hmul : ∀ x y, x < 729 * N → y < 729 * N →
      mulQK ADT TT AT x y < 729 * N ∧ mdl (mulQK ADT TT AT x y) = mdl x * mdl y)
    (h1 : ∀ x < 729 * N, mdl x = 1 → x = 0)
    (hGC : ∀ g < GC.length, getL 0 GC g < 729 * N)
    (hF : ∀ k, 1 ≤ k → k < N → fusQK N ADT TT AT GC RP DP k (FL k) = true) :
    ∀ x, 729 ≤ x → x < 729 * N → mdl x ^ 3 = 1 → ∃ r ∈ RP, IsConj (mdl r) (mdl x) := by
  suffices H : ∀ d x, depK DP x = d → 729 ≤ x → x < 729 * N → mdl x ^ 3 = 1 →
      ∃ r ∈ RP, IsConj (mdl r) (mdl x) from fun x => H _ x rfl
  intro d
  induction d using Nat.strong_induction_on with
  | _ d ih =>
    intro x hd hx1 hx2 hx3
    have hk1 : 1 ≤ x / 729 := (Nat.le_div_iff_mul_le (by norm_num)).2 (by omega)
    have hk2 : x / 729 < N := Nat.div_lt_of_lt_mul hx2
    have hxe : 729 * (x / 729) + x % 729 = x := Nat.div_add_mod x 729
    have hF' := fusQK_sound (hF _ hk1 hk2) (Nat.mod_lt x (show 0 < 729 by norm_num))
    rw [hxe] at hF'
    obtain ⟨hA, hB, hC⟩ := hF'
    by_cases hd0 : depK DP x = 0
    · exfalso
      obtain ⟨hlt2, he2⟩ := hmul x x hx2 hx2
      obtain ⟨-, he3⟩ := hmul _ x hlt2 hx2
      refine hA hd0 (h1 _ ?_ ?_)
      · exact (hmul _ x hlt2 hx2).1
      · rw [he3, he2, ← pow_two, ← pow_succ, hx3]
    by_cases hd1 : depK DP x = 1
    · exact ⟨x, hB hd1, IsConj.refl _⟩
    obtain ⟨hg, hc1, hc2, hcd, hxc⟩ := hC hd0 hd1
    set f := (FL (x / 729)).getD (x % 729) 0
    have hh := hGC _ hg
    have hxm : mdl x * mdl (getL 0 GC (f % 8)) = mdl (getL 0 GC (f % 8)) * mdl (f / 8) := by
      rw [← (hmul _ _ hx2 hh).2, ← (hmul _ _ hh hc2).2, hxc]
    have hconj : IsConj (mdl (f / 8)) (mdl x) := isConj_of_mul' hxm
    have hc3 : mdl (f / 8) ^ 3 = 1 := by
      obtain ⟨c, hc⟩ := isConj_iff.1 hconj
      have e := hx3
      rw [← hc, conj_pow] at e
      calc mdl (f / 8) ^ 3 = c⁻¹ * (c * mdl (f / 8) ^ 3 * c⁻¹) * c := by group
        _ = 1 := by rw [e]; group
    obtain ⟨r, hr, hrc⟩ := ih _ (by omega) (f / 8) rfl hc1 hc2 hc3
    exact ⟨r, hr, hrc.trans hconj⟩

end CFSG.KC.Co1Cl

end

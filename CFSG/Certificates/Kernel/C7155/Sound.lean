module

public import Certificates.Data.Kernel.C7155.Check
public import CFSG.Quasithin.H13.NQCatT513L35Defs

public section

namespace CFSG.KC.C7155

open CFSG.Quasithin.H13.NQCat.T513.L35 CFSG.KC.Loop CFSG.KC.Ord Matrix Polynomial

abbrev Tri := ZMod 5 × ZMod 5 × ZMod 5

@[expose] def mulA (t c : ZMod 5) (a b : Tri) : Tri :=
  (a.1 * b.1 + (a.2.1 * b.2.2 + a.2.2 * b.2.1) + t * (a.2.2 * b.2.2),
    a.1 * b.2.1 + a.2.1 * b.1 - c * (a.2.1 * b.2.2 + a.2.2 * b.2.1) +
      (1 - t * c) * (a.2.2 * b.2.2),
    a.1 * b.2.2 + a.2.1 * b.2.1 + a.2.2 * b.1 + t * (a.2.1 * b.2.2 + a.2.2 * b.2.1) +
      (t * t - c) * (a.2.2 * b.2.2))

@[expose] def powA (t c : ZMod 5) : ℕ → Tri
  | 0 => (1, 0, 0)
  | n + 1 => mulA t c (powA t c n) (0, 1, 0)

@[expose] def Prop5 (v w : Fin 3 → ZMod 5) : Prop := ∃ μ : ZMod 5, μ ≠ 0 ∧ w = μ • v

theorem k7_andB {a b : Bool} : andB a b = true ↔ a = true ∧ b = true := by
  cases a <;> cases b <;> decide

theorem k7_orB {a b : Bool} : orB a b = true ↔ a = true ∨ b = true := by
  cases a <;> cases b <;> decide

theorem k7_notB {a : Bool} : notB a = true ↔ a = false := by
  cases a <;> decide

theorem k7_beq {x y : ℕ} : Nat.beq x y = true ↔ x = y :=
  ⟨Nat.eq_of_beq_eq_true, fun h => by
    subst h
    exact Nat.beq_refl x⟩

theorem k7_beq_false {x y : ℕ} : Nat.beq x y = false ↔ ¬ x = y := by
  rw [← Bool.not_eq_true, k7_beq]

theorem k7_strictN (y : ℕ) (k : ℕ → ℕ) : strictN y k = k y := by
  cases y <;> rfl

theorem k7_strictB (y : ℕ) (k : ℕ → Bool) : strictB y k = k y := by
  cases y <;> rfl

theorem k7_nadd (x y : ℕ) : Nat.add x y = x + y := rfl

theorem k7_nmul (x y : ℕ) : Nat.mul x y = x * y := rfl

theorem k7_nmod (x y : ℕ) : Nat.mod x y = x % y := rfl

theorem k7_nsub (x y : ℕ) : Nat.sub x y = x - y := rfl

theorem k7_shl (a b : ℕ) : Nat.shiftLeft a b = a * 2 ^ b := Nat.shiftLeft_eq a b

theorem k7_land (a b : ℕ) : Nat.land a b = a &&& b := rfl

theorem k7_allN {n : ℕ} {f : ℕ → Bool} : allN n f = true ↔ ∀ i < n, f i = true := by
  induction n with
  | zero => exact ⟨fun _ i hi => absurd hi (Nat.not_lt_zero i), fun _ => rfl⟩
  | succ n ih =>
    change andB (f n) (allN n f) = true ↔ _
    rw [k7_andB, ih]
    constructor
    · rintro ⟨h1, h2⟩ i hi
      rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | rfl
      · exact h2 i hi
      · exact h1
    · intro h
      exact ⟨h n (Nat.lt_succ_self n), fun i hi => h i (Nat.lt_succ_of_lt hi)⟩

theorem k7_anyN {n : ℕ} {f : ℕ → Bool} : anyN n f = true ↔ ∃ i < n, f i = true := by
  induction n with
  | zero =>
    exact ⟨fun h => (Bool.false_ne_true h).elim, fun ⟨i, hi, _⟩ => absurd hi (Nat.not_lt_zero i)⟩
  | succ n ih =>
    change orB (f n) (anyN n f) = true ↔ _
    rw [k7_orB, ih]
    constructor
    · rintro (h | ⟨i, hi, h⟩)
      · exact ⟨n, Nat.lt_succ_self n, h⟩
      · exact ⟨i, Nat.lt_succ_of_lt hi, h⟩
    · rintro ⟨i, hi, h⟩
      rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | rfl
      · exact Or.inr ⟨i, hi, h⟩
      · exact Or.inl h

theorem k7_anyL {L : List ℕ} {f : ℕ → Bool} : anyL L f = true ↔ ∃ t ∈ L, f t = true := by
  induction L with
  | nil => exact ⟨fun h => (Bool.false_ne_true h).elim, fun ⟨_, ht, _⟩ => by simp at ht⟩
  | cons a L ih =>
    change orB (f a) (anyL L f) = true ↔ _
    rw [k7_orB, ih]
    simp only [List.mem_cons, exists_eq_or_imp]

theorem k7_four : (4 : ZMod 5) = -1 := by decide

theorem k7_lt8 {a : ℕ} (h : a < 5) : a < 8 := by omega

theorem k7_mod_lt8 (x : ℕ) : Nat.mod x 5 < 8 :=
  Nat.lt_of_lt_of_le (Nat.mod_lt x (by norm_num)) (by norm_num)

theorem k7_cast_mod (n : ℕ) : ((n % 5 : ℕ) : ZMod 5) = n := ZMod.natCast_mod n 5

theorem k7_natCast_inj {a b : ℕ} (ha : a < 5) (hb : b < 5) (h : (a : ZMod 5) = b) : a = b := by
  have e := congrArg ZMod.val h
  rwa [ZMod.val_natCast, ZMod.val_natCast, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb] at e

theorem k7_cast_eq_zero {x : ℕ} (hx : x < 5) : (x : ZMod 5) = 0 ↔ x = 0 :=
  ⟨fun h => k7_natCast_inj hx (by norm_num) (by rw [h, Nat.cast_zero]), fun h => by
    rw [h, Nat.cast_zero]⟩

theorem k7_d3_lt (a b c x y z : ℕ) : d3 a b c x y z < 5 := by
  unfold d3
  exact Nat.mod_lt _ (by norm_num)

theorem k7_cast_d3 (a b c x y z : ℕ) :
    ((d3 a b c x y z : ℕ) : ZMod 5) = a * x + b * y + c * z := by
  simp only [d3, k7_nadd, k7_nmul, k7_nmod, k7_cast_mod, Nat.cast_add, Nat.cast_mul]

theorem k7_cast_inv5 (a : ℕ) : ((inv5 a : ℕ) : ZMod 5) = (a : ZMod 5) ^ 3 := by
  simp only [inv5, k7_nmul, k7_nmod, k7_cast_mod, Nat.cast_mul]
  ring

theorem k7_chiAt_lt (t c l : ℕ) : chiAt t c l < 5 := by
  unfold chiAt
  exact Nat.mod_lt _ (by norm_num)

theorem k7_cast_chiAt (t c l : ℕ) :
    ((chiAt t c l : ℕ) : ZMod 5) =
      (l : ZMod 5) ^ 3 - (t : ZMod 5) * (l : ZMod 5) ^ 2 + (c : ZMod 5) * l - 1 := by
  simp only [chiAt, k7_nadd, k7_nmul, k7_nmod, k7_cast_mod, Nat.cast_add, Nat.cast_mul,
    Nat.cast_ofNat, k7_four]
  ring

theorem k7_ent (M s : ℕ) : ent M s = M / 2 ^ s % 8 := by
  change (M >>> s) &&& (2 ^ 3 - 1) = _
  rw [Nat.and_two_pow_sub_one_eq_mod, Nat.shiftRight_eq_div_pow]

theorem k7_ent_pk3 {a0 a1 a2 : ℕ} (h0 : a0 < 8) (h1 : a1 < 8) (h2 : a2 < 8) :
    ent (pk3 a0 a1 a2) 0 = a0 ∧ ent (pk3 a0 a1 a2) 3 = a1 ∧ ent (pk3 a0 a1 a2) 6 = a2 := by
  simp only [k7_ent, pk3, k7_nadd, k7_shl, Nat.reducePow]
  refine ⟨?_, ?_, ?_⟩ <;> omega

theorem k7_e0 {a : ℕ} {R : ℕ} (ha : a < 8) : ent (a + 8 * R) 0 = a := by
  rw [k7_ent, pow_zero, Nat.div_one]
  omega

theorem k7_e3 {a R s : ℕ} (ha : a < 8) : ent (a + 8 * R) (s + 3) = ent R s := by
  have e : (a + 8 * R) / 2 ^ 3 = R := by
    simp only [Nat.reducePow]
    omega
  rw [k7_ent, k7_ent, pow_add, mul_comm (2 ^ s), ← Nat.div_div_eq_div_mul, e]

theorem k7_eL {a : ℕ} (ha : a < 8) : ent a 0 = a := by
  rw [k7_ent, pow_zero, Nat.div_one, Nat.mod_eq_of_lt ha]

theorem k7_pk9_nest (a0 a1 a2 a3 a4 a5 a6 a7 a8 : ℕ) : pk9 a0 a1 a2 a3 a4 a5 a6 a7 a8 =
    a0 + 8 * (a1 + 8 * (a2 + 8 * (a3 + 8 * (a4 + 8 * (a5 + 8 * (a6 + 8 * (a7 + 8 * a8))))))) := by
  change a0 + (a1 <<< 3 + (a2 <<< 6 + (a3 <<< 9 + (a4 <<< 12 + (a5 <<< 15 + (a6 <<< 18 +
    (a7 <<< 21 + a8 <<< 24))))))) = _
  rw [Nat.shiftLeft_eq, Nat.shiftLeft_eq, Nat.shiftLeft_eq, Nat.shiftLeft_eq, Nat.shiftLeft_eq,
    Nat.shiftLeft_eq, Nat.shiftLeft_eq, Nat.shiftLeft_eq]
  ring

theorem k7_ent_pk9 {x0 x1 x2 x3 x4 x5 x6 x7 x8 : ℕ} (h0 : x0 < 8) (h1 : x1 < 8) (h2 : x2 < 8)
    (h3 : x3 < 8) (h4 : x4 < 8) (h5 : x5 < 8) (h6 : x6 < 8) (h7 : x7 < 8) (h8 : x8 < 8) :
    ent (pk9 x0 x1 x2 x3 x4 x5 x6 x7 x8) 0 = x0 ∧ ent (pk9 x0 x1 x2 x3 x4 x5 x6 x7 x8) 3 = x1 ∧
      ent (pk9 x0 x1 x2 x3 x4 x5 x6 x7 x8) 6 = x2 ∧
      ent (pk9 x0 x1 x2 x3 x4 x5 x6 x7 x8) 9 = x3 ∧
      ent (pk9 x0 x1 x2 x3 x4 x5 x6 x7 x8) 12 = x4 ∧
      ent (pk9 x0 x1 x2 x3 x4 x5 x6 x7 x8) 15 = x5 ∧
      ent (pk9 x0 x1 x2 x3 x4 x5 x6 x7 x8) 18 = x6 ∧
      ent (pk9 x0 x1 x2 x3 x4 x5 x6 x7 x8) 21 = x7 ∧
      ent (pk9 x0 x1 x2 x3 x4 x5 x6 x7 x8) 24 = x8 := by
  rw [k7_pk9_nest]
  exact ⟨k7_e0 h0, (k7_e3 (s := 0) h0).trans (k7_e0 h1),
    (k7_e3 (s := 3) h0).trans ((k7_e3 (s := 0) h1).trans (k7_e0 h2)),
    (k7_e3 (s := 6) h0).trans ((k7_e3 (s := 3) h1).trans ((k7_e3 (s := 0) h2).trans (k7_e0 h3))),
    (k7_e3 (s := 9) h0).trans ((k7_e3 (s := 6) h1).trans ((k7_e3 (s := 3) h2).trans
      ((k7_e3 (s := 0) h3).trans (k7_e0 h4)))),
    (k7_e3 (s := 12) h0).trans ((k7_e3 (s := 9) h1).trans ((k7_e3 (s := 6) h2).trans
      ((k7_e3 (s := 3) h3).trans ((k7_e3 (s := 0) h4).trans (k7_e0 h5))))),
    (k7_e3 (s := 15) h0).trans ((k7_e3 (s := 12) h1).trans ((k7_e3 (s := 9) h2).trans
      ((k7_e3 (s := 6) h3).trans ((k7_e3 (s := 3) h4).trans ((k7_e3 (s := 0) h5).trans
        (k7_e0 h6)))))),
    (k7_e3 (s := 18) h0).trans ((k7_e3 (s := 15) h1).trans ((k7_e3 (s := 12) h2).trans
      ((k7_e3 (s := 9) h3).trans ((k7_e3 (s := 6) h4).trans ((k7_e3 (s := 3) h5).trans
        ((k7_e3 (s := 0) h6).trans (k7_e0 h7))))))),
    (k7_e3 (s := 21) h0).trans ((k7_e3 (s := 18) h1).trans ((k7_e3 (s := 15) h2).trans
      ((k7_e3 (s := 12) h3).trans ((k7_e3 (s := 9) h4).trans ((k7_e3 (s := 6) h5).trans
        ((k7_e3 (s := 3) h6).trans ((k7_e3 (s := 0) h7).trans (k7_eL h8))))))))⟩

theorem k7_land_lane (P s : ℕ) : P &&& 7 <<< s = 0 ↔ ent P s = 0 := by
  have e : P &&& 7 <<< s = ((P >>> s) &&& 7) <<< s := by
    apply Nat.eq_of_testBit_eq
    intro j
    simp only [Nat.testBit_and, Nat.testBit_shiftLeft, Nat.testBit_shiftRight]
    by_cases hj : s ≤ j
    · simp [hj, Nat.add_sub_cancel' hj]
    · simp [hj]
  rw [e, Nat.shiftLeft_eq_zero_iff]
  rfl

theorem k7_m1 (P : ℕ) :
    Nat.land P 16744896 = 0 ↔ ent P 6 = 0 ∧ ent P 15 = 0 ∧ ent P 18 = 0 ∧ ent P 21 = 0 := by
  have e : (16744896 : ℕ) = 7 <<< 6 ||| 7 <<< 15 ||| 7 <<< 18 ||| 7 <<< 21 := by decide +kernel
  rw [k7_land, e, Nat.and_or_distrib_left, Nat.and_or_distrib_left, Nat.and_or_distrib_left,
    Nat.or_eq_zero_iff, Nat.or_eq_zero_iff, Nat.or_eq_zero_iff, k7_land_lane, k7_land_lane,
    k7_land_lane, k7_land_lane]
  tauto

theorem k7_m2 (P : ℕ) : Nat.land P 3640 = 0 ↔ ent P 3 = 0 ∧ ent P 9 = 0 := by
  have e : (3640 : ℕ) = 7 <<< 3 ||| 7 <<< 9 := by decide +kernel
  rw [k7_land, e, Nat.and_or_distrib_left, Nat.or_eq_zero_iff, k7_land_lane, k7_land_lane]

theorem k7_m3 (P : ℕ) : Nat.land P 28679 = 0 ↔ ent P 0 = 0 ∧ ent P 12 = 0 := by
  have e : (28679 : ℕ) = 7 <<< 0 ||| 7 <<< 12 := by decide +kernel
  rw [k7_land, e, Nat.and_or_distrib_left, Nat.or_eq_zero_iff, k7_land_lane, k7_land_lane]

theorem k7_mulA_one (t c : ZMod 5) (a : Tri) : mulA t c a (1, 0, 0) = a := by
  refine Prod.ext ?_ (Prod.ext ?_ ?_) <;> simp only [mulA] <;> ring

theorem k7_mulA_assoc (t c : ZMod 5) (a b d : Tri) :
    mulA t c (mulA t c a b) d = mulA t c a (mulA t c b d) := by
  refine Prod.ext ?_ (Prod.ext ?_ ?_) <;> simp only [mulA] <;> ring

theorem k7_powA_add (t c : ZMod 5) (m n : ℕ) :
    powA t c (m + n) = mulA t c (powA t c m) (powA t c n) := by
  induction n with
  | zero => exact (k7_mulA_one t c _).symm
  | succ n ih =>
    change mulA t c (powA t c (m + n)) (0, 1, 0) =
      mulA t c (powA t c m) (mulA t c (powA t c n) (0, 1, 0))
    rw [ih, k7_mulA_assoc]

noncomputable def decT (P : ℕ) : Tri :=
  (((ent P 0 : ℕ) : ZMod 5), ((ent P 3 : ℕ) : ZMod 5), ((ent P 6 : ℕ) : ZMod 5))

theorem k7_decT_pk3 {a0 a1 a2 : ℕ} (h0 : a0 < 8) (h1 : a1 < 8) (h2 : a2 < 8) :
    decT (pk3 a0 a1 a2) = ((a0 : ZMod 5), (a1 : ZMod 5), (a2 : ZMod 5)) := by
  obtain ⟨e0, e1, e2⟩ := k7_ent_pk3 h0 h1 h2
  rw [decT, e0, e1, e2]

theorem k7_decT1 : decT 1 = (1, 0, 0) := by decide +kernel

theorem k7_decT8 : decT 8 = (0, 1, 0) := by decide +kernel

theorem k7_decT_mulQ (t c P Q : ℕ) :
    decT (mulQ t c P Q) = mulA t c (decT P) (decT Q) := by
  unfold mulQ mul3
  simp only [k7_strictN]
  rw [k7_decT_pk3 (k7_mod_lt8 _) (k7_mod_lt8 _) (k7_mod_lt8 _)]
  refine Prod.ext ?_ (Prod.ext ?_ ?_) <;>
    simp only [decT, mulA, k7_nadd, k7_nmul, k7_nmod, k7_cast_mod, Nat.cast_add, Nat.cast_mul,
      Nat.cast_ofNat, Nat.cast_one, k7_four] <;>
    ring

theorem k7_decT_subOne (P : ℕ) : decT (subOne P) = decT P - (1, 0, 0) := by
  have hs : P - P % 8 = 8 * (P / 8) := by omega
  have hr : (P % 8 + 4) % 5 < 8 := by omega
  have e : subOne P = (P % 8 + 4) % 5 + 8 * (P / 8) := by
    simp only [subOne, k7_ent, k7_nadd, k7_nmod, k7_nsub, pow_zero, Nat.div_one, hs]
  have e0 : ent (subOne P) 0 = (ent P 0 + 4) % 5 := by
    rw [e, k7_e0 hr, k7_ent, pow_zero, Nat.div_one]
  have e3 : ent (subOne P) 3 = ent P 3 := by
    rw [e, k7_e3 (s := 0) hr]
    simp only [k7_ent, pow_zero, Nat.div_one, Nat.reducePow]
  have e6 : ent (subOne P) 6 = ent P 6 := by
    rw [e, k7_e3 (s := 3) hr]
    simp only [k7_ent, Nat.div_div_eq_div_mul, Nat.reducePow, Nat.reduceMul]
  refine Prod.ext ?_ (Prod.ext ?_ ?_) <;>
    simp only [decT, e0, e3, e6, Prod.fst_sub, Prod.snd_sub, k7_cast_mod, Nat.cast_add,
      Nat.cast_ofNat, k7_four] <;>
    ring

@[expose] noncomputable def pq (t c : ℕ) (bits : List Bool) (r : ℕ) : ℕ :=
  List.rec (motive := fun _ => ℕ → ℕ) (fun r => r)
    (fun b _ ih r => ih (strictN (mulQ t c r r) fun s =>
      Bool.rec (motive := fun _ => ℕ) s (mulQ t c s 8) b)) bits r

@[expose] def binV : List Bool → ℕ → ℕ
  | [], n => n
  | b :: bs, n => binV bs (2 * n + b.toNat)

theorem k7_powQ (t c : ℕ) (bits : List Bool) : powQ t c bits = pq t c bits 1 := rfl

theorem k7_pq (t c : ℕ) : ∀ (bits : List Bool) (r n : ℕ),
    decT r = powA (t : ZMod 5) (c : ZMod 5) n →
      decT (pq t c bits r) = powA (t : ZMod 5) (c : ZMod 5) (binV bits n)
  | [], _, _, h => h
  | b :: bs, r, n, h => by
    have key := k7_pq t c bs (strictN (mulQ t c r r) fun s =>
      Bool.rec (motive := fun _ => ℕ) s (mulQ t c s 8) b) (2 * n + b.toNat)
    refine key ?_
    rw [k7_strictN]
    have hs : decT (mulQ t c r r) = powA (t : ZMod 5) (c : ZMod 5) (2 * n) := by
      rw [k7_decT_mulQ, h, two_mul, k7_powA_add]
    cases b
    · exact hs
    · change decT (mulQ t c (mulQ t c r r) 8) = powA (t : ZMod 5) (c : ZMod 5) (2 * n + 1)
      rw [k7_decT_mulQ, hs, k7_decT8]
      rfl

theorem k7_binV : binV bits11625 0 = 11625 := by decide

theorem k7_binV31 : binV bits31 0 = 31 := by decide

theorem bucketsOK_sound (h : bucketsOK bits11625 = true) (t c : ZMod 5) :
    (∃ u : Tri, mulA t c u (powA t c 11625 - (1, 0, 0)) = (0, -c, t)) ∨
      (powA t c 31 = (1, 0, 0) ∧ ∀ l : ZMod 5, l ^ 3 - t * l ^ 2 + c * l - 1 ≠ 0) ∨
      (t = 3 ∧ c = 3) := by
  have ht := ZMod.natCast_zmod_val t
  have hc := ZMod.natCast_zmod_val c
  have hb : bucketOK bits11625 t.val c.val = true :=
    k7_allN.1 (k7_allN.1 h t.val (ZMod.val_lt t)) c.val (ZMod.val_lt c)
  unfold bucketOK at hb
  simp only [k7_orB, k7_andB, k7_notB, k7_beq, k7_beq_false, k7_strictB, k7_anyN,
    k7_allN] at hb
  rcases hb with ⟨u0, -, u1, -, u2, -, hu⟩ | ⟨h31, hroot⟩ | ⟨h3, h3'⟩
  · left
    refine ⟨decT (pk3 u0 u1 u2), ?_⟩
    have e := congrArg decT hu
    rw [k7_decT_mulQ, k7_decT_subOne, k7_powQ, k7_pq t.val c.val bits11625 1 0 k7_decT1,
      k7_binV, k7_decT_pk3 (by norm_num) (k7_mod_lt8 _) (k7_lt8 (ZMod.val_lt t))] at e
    simp only [k7_nmod, k7_nmul, k7_cast_mod, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_zero, ht,
      hc, k7_four] at e
    rw [e, neg_one_mul]
  · right
    left
    refine ⟨?_, fun l hl => ?_⟩
    · have e := congrArg decT h31
      rw [k7_powQ, k7_pq t.val c.val bits31 1 0 k7_decT1, k7_binV31, k7_decT1, ht, hc] at e
      exact e
    · apply hroot l.val (ZMod.val_lt l)
      apply k7_natCast_inj (k7_chiAt_lt _ _ _) (by norm_num)
      rw [k7_cast_chiAt, ht, hc, ZMod.natCast_zmod_val, Nat.cast_zero]
      exact hl
  · right
    right
    exact ⟨ZMod.val_injective 5 (h3.trans rfl), ZMod.val_injective 5 (h3'.trans rfl)⟩

noncomputable def decM (M : ℕ) : Matrix (Fin 3) (Fin 3) (ZMod 5) :=
  !![((ent M 0 : ℕ) : ZMod 5), ((ent M 3 : ℕ) : ZMod 5), ((ent M 6 : ℕ) : ZMod 5);
    ((ent M 9 : ℕ) : ZMod 5), ((ent M 12 : ℕ) : ZMod 5), ((ent M 15 : ℕ) : ZMod 5);
    ((ent M 18 : ℕ) : ZMod 5), ((ent M 21 : ℕ) : ZMod 5), ((ent M 24 : ℕ) : ZMod 5)]

theorem k7_decM_pk9 {x0 x1 x2 x3 x4 x5 x6 x7 x8 : ℕ} (h0 : x0 < 8) (h1 : x1 < 8) (h2 : x2 < 8)
    (h3 : x3 < 8) (h4 : x4 < 8) (h5 : x5 < 8) (h6 : x6 < 8) (h7 : x7 < 8) (h8 : x8 < 8) :
    decM (pk9 x0 x1 x2 x3 x4 x5 x6 x7 x8) =
      !![(x0 : ZMod 5), (x1 : ZMod 5), (x2 : ZMod 5); (x3 : ZMod 5), (x4 : ZMod 5), (x5 : ZMod 5);
        (x6 : ZMod 5), (x7 : ZMod 5), (x8 : ZMod 5)] := by
  obtain ⟨e0, e1, e2, e3, e4, e5, e6, e7, e8⟩ := k7_ent_pk9 h0 h1 h2 h3 h4 h5 h6 h7 h8
  rw [decM, e0, e1, e2, e3, e4, e5, e6, e7, e8]

theorem k7_mulM_eq (A B : ℕ) : mulM A B = mul9 (ent A 0) (ent A 3) (ent A 6) (ent A 9)
    (ent A 12) (ent A 15) (ent A 18) (ent A 21) (ent A 24) (ent B 0) (ent B 3) (ent B 6)
    (ent B 9) (ent B 12) (ent B 15) (ent B 18) (ent B 21) (ent B 24) := by
  unfold mulM
  rw [k7_strictN, k7_strictN]

theorem k7_decM_mulM (A B : ℕ) : decM (mulM A B) = decM A * decM B := by
  rw [k7_mulM_eq, mul9, k7_decM_pk9 (k7_lt8 (k7_d3_lt _ _ _ _ _ _)) (k7_lt8 (k7_d3_lt _ _ _ _ _ _))
    (k7_lt8 (k7_d3_lt _ _ _ _ _ _)) (k7_lt8 (k7_d3_lt _ _ _ _ _ _))
    (k7_lt8 (k7_d3_lt _ _ _ _ _ _)) (k7_lt8 (k7_d3_lt _ _ _ _ _ _))
    (k7_lt8 (k7_d3_lt _ _ _ _ _ _)) (k7_lt8 (k7_d3_lt _ _ _ _ _ _))
    (k7_lt8 (k7_d3_lt _ _ _ _ _ _))]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [decM, Matrix.mul_apply, Fin.sum_univ_three, k7_cast_d3]

theorem k7_idM : idM = pk9 1 0 0 0 1 0 0 0 1 := by decide +kernel

theorem k7_decM_idM : decM idM = 1 := by
  rw [k7_idM, k7_decM_pk9 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.one_apply]

theorem k7_pow5M (A : ℕ) : pow5M A = mulM (mulM (mulM A A) (mulM A A)) A := by
  unfold pow5M
  rw [k7_strictN, k7_strictN]

theorem k7_decM_pow5M (A : ℕ) : decM (pow5M A) = decM A ^ 5 := by
  rw [k7_pow5M, k7_decM_mulM, k7_decM_mulM, k7_decM_mulM]
  simp only [pow_succ, pow_zero, one_mul, mul_assoc]

theorem k7_pk9_eq {x0 x1 x2 x3 x4 x5 x6 x7 x8 y0 y1 y2 y3 y4 y5 y6 y7 y8 : ℕ}
    (hx0 : x0 < 5) (hx1 : x1 < 5) (hx2 : x2 < 5) (hx3 : x3 < 5) (hx4 : x4 < 5)
    (hx5 : x5 < 5) (hx6 : x6 < 5) (hx7 : x7 < 5) (hx8 : x8 < 5)
    (hy0 : y0 < 5) (hy1 : y1 < 5) (hy2 : y2 < 5) (hy3 : y3 < 5) (hy4 : y4 < 5)
    (hy5 : y5 < 5) (hy6 : y6 < 5) (hy7 : y7 < 5) (hy8 : y8 < 5)
    (h : decM (pk9 x0 x1 x2 x3 x4 x5 x6 x7 x8) = decM (pk9 y0 y1 y2 y3 y4 y5 y6 y7 y8)) :
    pk9 x0 x1 x2 x3 x4 x5 x6 x7 x8 = pk9 y0 y1 y2 y3 y4 y5 y6 y7 y8 := by
  rw [k7_decM_pk9 (k7_lt8 hx0) (k7_lt8 hx1) (k7_lt8 hx2) (k7_lt8 hx3) (k7_lt8 hx4) (k7_lt8 hx5)
    (k7_lt8 hx6) (k7_lt8 hx7) (k7_lt8 hx8), k7_decM_pk9 (k7_lt8 hy0) (k7_lt8 hy1) (k7_lt8 hy2)
    (k7_lt8 hy3) (k7_lt8 hy4) (k7_lt8 hy5) (k7_lt8 hy6) (k7_lt8 hy7) (k7_lt8 hy8)] at h
  have q0 := k7_natCast_inj hx0 hy0 (congrFun (congrFun h 0) 0)
  have q1 := k7_natCast_inj hx1 hy1 (congrFun (congrFun h 0) 1)
  have q2 := k7_natCast_inj hx2 hy2 (congrFun (congrFun h 0) 2)
  have q3 := k7_natCast_inj hx3 hy3 (congrFun (congrFun h 1) 0)
  have q4 := k7_natCast_inj hx4 hy4 (congrFun (congrFun h 1) 1)
  have q5 := k7_natCast_inj hx5 hy5 (congrFun (congrFun h 1) 2)
  have q6 := k7_natCast_inj hx6 hy6 (congrFun (congrFun h 2) 0)
  have q7 := k7_natCast_inj hx7 hy7 (congrFun (congrFun h 2) 1)
  have q8 := k7_natCast_inj hx8 hy8 (congrFun (congrFun h 2) 2)
  rw [q0, q1, q2, q3, q4, q5, q6, q7, q8]

theorem k7_mulM_eq_idM {A B : ℕ} (h : decM (mulM A B) = 1) : mulM A B = idM := by
  have h' : decM (mulM A B) = decM idM := by rw [h, k7_decM_idM]
  rw [k7_mulM_eq, mul9, k7_idM] at h' ⊢
  exact k7_pk9_eq (k7_d3_lt _ _ _ _ _ _) (k7_d3_lt _ _ _ _ _ _) (k7_d3_lt _ _ _ _ _ _)
    (k7_d3_lt _ _ _ _ _ _) (k7_d3_lt _ _ _ _ _ _) (k7_d3_lt _ _ _ _ _ _) (k7_d3_lt _ _ _ _ _ _)
    (k7_d3_lt _ _ _ _ _ _) (k7_d3_lt _ _ _ _ _ _) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) h'

theorem k7_inT_pk9 {x0 x1 x2 x3 x4 x5 x6 x7 x8 : ℕ} (h0 : x0 < 5) (h1 : x1 < 5) (h2 : x2 < 5)
    (h3 : x3 < 5) (h4 : x4 < 5) (h5 : x5 < 5) (h6 : x6 < 5) (h7 : x7 < 5) (h8 : x8 < 5)
    (h : IsMon (decM (pk9 x0 x1 x2 x3 x4 x5 x6 x7 x8))) :
    inT (pk9 x0 x1 x2 x3 x4 x5 x6 x7 x8) = true := by
  obtain ⟨e0, e1, e2, e3, e4, e5, e6, e7, e8⟩ := k7_ent_pk9 (k7_lt8 h0) (k7_lt8 h1) (k7_lt8 h2)
    (k7_lt8 h3) (k7_lt8 h4) (k7_lt8 h5) (k7_lt8 h6) (k7_lt8 h7) (k7_lt8 h8)
  rw [k7_decM_pk9 (k7_lt8 h0) (k7_lt8 h1) (k7_lt8 h2) (k7_lt8 h3) (k7_lt8 h4) (k7_lt8 h5)
    (k7_lt8 h6) (k7_lt8 h7) (k7_lt8 h8)] at h
  obtain ⟨m02, m12, m20, m21, m22, hm⟩ := h
  have f2 := (k7_cast_eq_zero h2).1 m02
  have f5 := (k7_cast_eq_zero h5).1 m12
  have f6 := (k7_cast_eq_zero h6).1 m20
  have f7 := (k7_cast_eq_zero h7).1 m21
  have f8 : x8 ≠ 0 := fun e => m22 ((k7_cast_eq_zero h8).2 e)
  unfold inT
  simp only [k7_andB, k7_orB, k7_notB, k7_beq, k7_beq_false, k7_m1, k7_m2, k7_m3, e0, e1, e2, e3,
    e4, e5, e6, e7, e8]
  rcases hm with ⟨m01, m10, m00, m11⟩ | ⟨m00, m11, m01, m10⟩
  · have f1 := (k7_cast_eq_zero h1).1 m01
    have f3 := (k7_cast_eq_zero h3).1 m10
    have f0 : x0 ≠ 0 := fun e => m00 ((k7_cast_eq_zero h0).2 e)
    have f4 : x4 ≠ 0 := fun e => m11 ((k7_cast_eq_zero h4).2 e)
    simp [f0, f1, f2, f3, f4, f5, f6, f7, f8]
  · have f0 := (k7_cast_eq_zero h0).1 m00
    have f4 := (k7_cast_eq_zero h4).1 m11
    have f1 : x1 ≠ 0 := fun e => m01 ((k7_cast_eq_zero h1).2 e)
    have f3 : x3 ≠ 0 := fun e => m10 ((k7_cast_eq_zero h3).2 e)
    simp [f0, f1, f2, f3, f4, f5, f6, f7, f8]

theorem k7_inT_mulM (A B : ℕ) (h : IsMon (decM (mulM A B))) : inT (mulM A B) = true := by
  rw [k7_mulM_eq, mul9] at h ⊢
  exact k7_inT_pk9 (k7_d3_lt _ _ _ _ _ _) (k7_d3_lt _ _ _ _ _ _) (k7_d3_lt _ _ _ _ _ _)
    (k7_d3_lt _ _ _ _ _ _) (k7_d3_lt _ _ _ _ _ _) (k7_d3_lt _ _ _ _ _ _) (k7_d3_lt _ _ _ _ _ _)
    (k7_d3_lt _ _ _ _ _ _) (k7_d3_lt _ _ _ _ _ _) h

theorem k7_tC : ∀ n ∈ tC, IsMon (decM n) ∧ (decM n).det = 1 := by
  unfold IsMon
  simp only [Matrix.det_fin_three]
  decide +kernel

theorem k7_decM_iter (A G : ℕ) (i : ℕ) : decM ((mulM A)^[i] G) = decM A ^ i * decM G := by
  induction i with
  | zero => simp
  | succ i ih => rw [Function.iterate_succ_apply', k7_decM_mulM, ih, pow_succ', mul_assoc]

theorem k7_refAux (A u : ℕ) : ∀ (k G : ℕ), refAux A u k G = true →
    ∀ i < k, inT (mulM ((mulM A)^[i] G) u) = false
  | 0, _, _, i, hi => absurd hi (Nat.not_lt_zero i)
  | k + 1, G, h, i, hi => by
    change andB (notB (inT (mulM G u))) (refAux A u k (mulM A G)) = true at h
    rw [k7_andB, k7_notB] at h
    cases i with
    | zero => exact h.1
    | succ i =>
      rw [Function.iterate_succ_apply]
      exact k7_refAux A u k (mulM A G) h.2 i (Nat.lt_of_succ_lt_succ hi)

def nrm (v : Fin 3 → ZMod 5) : ℕ := 5 * (v 0 * v 2 ^ 3).val + (v 1 * v 2 ^ 3).val

theorem k7_img (M : ℕ) (x y : ZMod 5) : img M x.val y.val = nrm (decM M *ᵥ ![x, y, 1]) := by
  have hx := ZMod.natCast_zmod_val x
  have hy := ZMod.natCast_zmod_val y
  have v0 : (decM M *ᵥ ![x, y, 1]) 0 =
      ((d3 (ent M 0) (ent M 3) (ent M 6) x.val y.val 1 : ℕ) : ZMod 5) := by
    rw [k7_cast_d3, hx, hy, Nat.cast_one]
    simp [decM, Matrix.mulVec, dotProduct, Fin.sum_univ_three]
  have v1 : (decM M *ᵥ ![x, y, 1]) 1 =
      ((d3 (ent M 9) (ent M 12) (ent M 15) x.val y.val 1 : ℕ) : ZMod 5) := by
    rw [k7_cast_d3, hx, hy, Nat.cast_one]
    simp [decM, Matrix.mulVec, dotProduct, Fin.sum_univ_three]
  have v2 : (decM M *ᵥ ![x, y, 1]) 2 =
      ((d3 (ent M 18) (ent M 21) (ent M 24) x.val y.val 1 : ℕ) : ZMod 5) := by
    rw [k7_cast_d3, hx, hy, Nat.cast_one]
    simp [decM, Matrix.mulVec, dotProduct, Fin.sum_univ_three]
  unfold img nrm
  simp only [k7_strictN, k7_nadd, k7_nmul, k7_nmod, v0, v1, v2]
  rw [← k7_cast_inv5, ← Nat.cast_mul, ← Nat.cast_mul, ZMod.val_natCast, ZMod.val_natCast]

theorem k7_nrm_smul {v w : Fin 3 → ZMod 5} (h : Prop5 v w) : nrm w = nrm v := by
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  obtain ⟨μ, hμ, rfl⟩ := h
  have h4 : μ ^ 4 = 1 := ZMod.pow_card_sub_one_eq_one hμ
  have e : ∀ i : Fin 3, (μ • v) i * (μ • v) 2 ^ 3 = v i * v 2 ^ 3 := by
    intro i
    simp only [Pi.smul_apply, smul_eq_mul]
    linear_combination (v i * v 2 ^ 3) * h4
  simp only [nrm, e]

noncomputable def mkG (n : ℕ) : G35 := if h : (decM n).det = 1 then ⟨decM n, h⟩ else 1

theorem k7_coe_mkG {n : ℕ} (h : (decM n).det = 1) :
    ((mkG n : G35) : Matrix (Fin 3) (Fin 3) (ZMod 5)) = decM n := by
  unfold mkG
  first
    | exact congrArg Subtype.val (dif_pos h)
    | simp [h]

theorem k7_fin5 {q : Fin 5 → ℕ} (h01 : q 0 ≠ q 1) (h02 : q 0 ≠ q 2) (h03 : q 0 ≠ q 3)
    (h04 : q 0 ≠ q 4) (h12 : q 1 ≠ q 2) (h13 : q 1 ≠ q 3) (h14 : q 1 ≠ q 4) (h23 : q 2 ≠ q 3)
    (h24 : q 2 ≠ q 4) (h34 : q 3 ≠ q 4) : ∀ i j, i ≠ j → q i ≠ q j := by
  intro i j hij
  fin_cases i <;> fin_cases j
  all_goals first
    | exact absurd rfl hij
    | assumption
    | exact Ne.symm (by assumption)

noncomputable def k7L (u : ℕ) : Fin 5 → ℕ := ![idM, 67117058, 67121155, 16793604, u]

theorem ptOK_sound (h : ptOKL tC = true) (x y : ZMod 5) (hxy : x ≠ 0 ∨ y ≠ 0) :
    ∃ t : Fin 5 → G35, (∀ i, t i ∈ T0) ∧ ∀ i j, i ≠ j →
      ¬ Prop5 ((t i : Matrix (Fin 3) (Fin 3) (ZMod 5)) *ᵥ ![x, y, 1])
        ((t j : Matrix (Fin 3) (Fin 3) (ZMod 5)) *ᵥ ![x, y, 1]) := by
  have hp : ptElt tC x.val y.val = true :=
    k7_allN.1 (k7_allN.1 h x.val (ZMod.val_lt x)) y.val (ZMod.val_lt y)
  unfold ptElt at hp
  simp only [k7_orB, k7_andB, k7_beq, ZMod.val_eq_zero, k7_anyL] at hp
  rcases hp with ⟨hx, hy⟩ | ⟨u, hu, hd⟩
  · rcases hxy with hxy | hxy
    · exact absurd hx hxy
    · exact absurd hy hxy
  obtain ⟨c0, c1, c2, c3⟩ : idM ∈ tC ∧ (67117058 : ℕ) ∈ tC ∧ (67121155 : ℕ) ∈ tC ∧
      (16793604 : ℕ) ∈ tC := by decide +kernel
  have hL : ∀ i : Fin 5, k7L u i ∈ tC := by
    intro i
    fin_cases i
    exacts [c0, c1, c2, c3, hu]
  simp only [dist5, neB, k7_andB, k7_notB, k7_beq_false] at hd
  obtain ⟨⟨h01, h02, h03, h04⟩, ⟨h12, h13, h14⟩, ⟨h23, h24⟩, h34⟩ := hd
  have hne := k7_fin5 (q := fun i => img (k7L u i) x.val y.val) h01 h02 h03 h04 h12 h13 h14 h23
    h24 h34
  refine ⟨fun i => mkG (k7L u i), fun i => ?_, fun i j hij hP => hne i j hij ?_⟩
  · try dsimp only
    rw [mem_T0_iff, k7_coe_mkG (k7_tC _ (hL i)).2]
    exact (k7_tC _ (hL i)).1
  · try dsimp only at hP
    rw [k7_coe_mkG (k7_tC _ (hL i)).2, k7_coe_mkG (k7_tC _ (hL j)).2] at hP
    change img (k7L u i) x.val y.val = img (k7L u j) x.val y.val
    rw [k7_img, k7_img]
    exact (k7_nrm_smul hP).symm

theorem levOK_sound (h : levOKL tC = true) (g : G35)
    (h02 : (g : Matrix (Fin 3) (Fin 3) (ZMod 5)) 0 2 = 0)
    (h12 : (g : Matrix (Fin 3) (Fin 3) (ZMod 5)) 1 2 = 0)
    (h20 : (g : Matrix (Fin 3) (Fin 3) (ZMod 5)) 2 0 = 0)
    (h21 : (g : Matrix (Fin 3) (Fin 3) (ZMod 5)) 2 1 = 0) (h5 : g ^ 5 = 1) (h1 : g ≠ 1) :
    ∃ t ∈ T0, ∀ k < 5, g ^ k * t * g ∉ T0 := by
  set M := (g : Matrix (Fin 3) (Fin 3) (ZMod 5)) with hMdef
  have hM5 : M ^ 5 = 1 := by
    rw [hMdef, ← Matrix.SpecialLinearGroup.coe_pow, h5, Matrix.SpecialLinearGroup.coe_one]
  have h22 : ∀ n : ℕ, (M ^ n) 2 2 = M 2 2 ^ n := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [pow_succ, Matrix.mul_apply, Fin.sum_univ_three, h02, h12, ih]
      ring
  have hl : M 2 2 = 1 := by
    have e := congrFun (congrFun hM5 2) 2
    rw [h22, Matrix.one_apply_eq] at e
    have hf : ∀ z : ZMod 5, z ^ 5 = z := by decide
    rwa [hf] at e
  have hdet : M 0 0 * M 1 1 - M 0 1 * M 1 0 = 1 := by
    have e : M.det = 1 := g.2
    rw [Matrix.det_fin_three, h02, h12, h20, h21, hl] at e
    linear_combination e
  unfold levOKL at h
  have hc := k7_allN.1 (k7_allN.1 (k7_allN.1 (k7_allN.1 h _ (ZMod.val_lt (M 0 0))) _
    (ZMod.val_lt (M 0 1))) _ (ZMod.val_lt (M 1 0))) _ (ZMod.val_lt (M 1 1))
  simp only [levElt, k7_orB, k7_notB, k7_beq, k7_beq_false, k7_strictB] at hc
  set G := pk9 (M 0 0).val (M 0 1).val 0 (M 1 0).val (M 1 1).val 0 0 0 1 with hG
  have hGM : decM G = M := by
    rw [hG, k7_decM_pk9 (k7_lt8 (ZMod.val_lt _)) (k7_lt8 (ZMod.val_lt _)) (by norm_num)
      (k7_lt8 (ZMod.val_lt _)) (k7_lt8 (ZMod.val_lt _)) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num)]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [h02, h12, h20, h21, hl]
  rcases hc with k1 | k1 | k1 | k1
  · exfalso
    apply k1
    apply k7_natCast_inj (Nat.mod_lt _ (by norm_num)) (by norm_num : (1 : ℕ) < 5)
    simp only [k7_nadd, k7_nmul, k7_nmod, k7_cast_mod, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat,
      Nat.cast_one, ZMod.natCast_zmod_val, k7_four]
    linear_combination hdet
  · exfalso
    apply h1
    apply Subtype.ext
    rw [Matrix.SpecialLinearGroup.coe_one, ← hMdef, ← hGM, k1, k7_decM_idM]
  · exfalso
    apply k1
    rw [k7_pow5M]
    apply k7_mulM_eq_idM
    rw [← k7_pow5M, k7_decM_pow5M, hGM, hM5]
  · unfold refute at k1
    obtain ⟨t, ht, hr⟩ := k7_anyL.1 k1
    obtain ⟨hmon, hdt⟩ := k7_tC t ht
    refine ⟨mkG t, ?_, fun k hk hmem => ?_⟩
    · rw [mem_T0_iff, k7_coe_mkG hdt]
      exact hmon
    · have e := k7_refAux G (mulM t G) 5 idM hr k hk
      rw [mem_T0_iff, Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul,
        Matrix.SpecialLinearGroup.coe_pow, k7_coe_mkG hdt, ← hMdef] at hmem
      have hm : IsMon (decM (mulM ((mulM G)^[k] idM) (mulM t G))) := by
        rw [k7_decM_mulM, k7_decM_iter, k7_decM_idM, k7_decM_mulM, hGM, mul_one, ← mul_assoc]
        exact hmem
      rw [k7_inT_mulM _ _ hm] at e
      exact Bool.false_ne_true e.symm

@[expose] def c2 (M : Matrix (Fin 3) (Fin 3) (ZMod 5)) : ZMod 5 :=
  M 0 0 * M 1 1 - M 0 1 * M 1 0 + M 0 0 * M 2 2 - M 0 2 * M 2 0 + M 1 1 * M 2 2 - M 1 2 * M 2 1

@[expose] noncomputable def chi (t c : ZMod 5) : (ZMod 5)[X] := X ^ 3 - C t * X ^ 2 + C c * X - 1

@[expose] noncomputable def triP (a : Tri) : (ZMod 5)[X] := C a.1 + C a.2.1 * X + C a.2.2 * X ^ 2

theorem aeval_chi_eq (M : Matrix (Fin 3) (Fin 3) (ZMod 5)) (t c : ZMod 5) :
    aeval M (chi t c) = M ^ 3 - t • M ^ 2 + c • M - 1 := by
  simp only [chi, map_sub, map_add, map_mul, aeval_X_pow, aeval_C, aeval_X, map_one,
    Algebra.algebraMap_eq_smul_one, smul_mul_assoc, one_mul]

theorem aeval_triP (M : Matrix (Fin 3) (Fin 3) (ZMod 5)) (a : Tri) :
    aeval M (triP a) = a.1 • (1 : Matrix (Fin 3) (Fin 3) (ZMod 5)) + a.2.1 • M + a.2.2 • M ^ 2 := by
  simp only [triP, map_add, map_mul, aeval_X_pow, aeval_C, aeval_X,
    Algebra.algebraMap_eq_smul_one, smul_mul_assoc, one_mul]

theorem cayley_hamilton (M : Matrix (Fin 3) (Fin 3) (ZMod 5)) :
    M ^ 3 - M.trace • M ^ 2 + c2 M • M - M.det • (1 : Matrix (Fin 3) (Fin 3) (ZMod 5)) = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [pow_succ, Matrix.mul_apply, Fin.sum_univ_three, Matrix.det_fin_three,
      Matrix.trace_fin_three, c2] <;> ring

theorem aeval_chi (g : G35) :
    aeval (g : Matrix (Fin 3) (Fin 3) (ZMod 5))
      (chi (g : Matrix (Fin 3) (Fin 3) (ZMod 5)).trace (c2 g)) = 0 := by
  have h := cayley_hamilton (g : Matrix (Fin 3) (Fin 3) (ZMod 5))
  rw [g.2, one_smul] at h
  rw [aeval_chi_eq, h]

theorem triP_mulA (t c : ZMod 5) (a b : Tri) :
    triP (mulA t c a b) = triP a * triP b -
      (C (a.2.1 * b.2.2 + a.2.2 * b.2.1) + C (a.2.2 * b.2.2) * (X + C t)) * chi t c := by
  simp only [triP, mulA, chi, map_add, map_mul, map_sub, map_one]
  ring

theorem triP_sub (a b : Tri) : triP (a - b) = triP a - triP b := by
  simp only [triP, Prod.fst_sub, Prod.snd_sub, map_sub]
  ring

theorem aeval_triP_powA (M : Matrix (Fin 3) (Fin 3) (ZMod 5)) (t c : ZMod 5)
    (hM : aeval M (chi t c) = 0) (n : ℕ) : aeval M (triP (powA t c n)) = M ^ n := by
  induction n with
  | zero => simp [triP, powA]
  | succ n ih =>
    rw [powA, triP_mulA, map_sub, map_mul, map_mul, hM, mul_zero, sub_zero, ih, pow_succ]
    simp [triP]

theorem pow_mulVec_of_eigen {M : Matrix (Fin 3) (Fin 3) (ZMod 5)} {v : Fin 3 → ZMod 5}
    {μ : ZMod 5} (h : M *ᵥ v = μ • v) (n : ℕ) : M ^ n *ᵥ v = μ ^ n • v := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, ← mulVec_mulVec, h, mulVec_smul, ih, smul_smul, pow_succ, mul_comm]

theorem bucket_sound (h : bucketsOK bits11625 = true) (g : G35) :
    (g ^ 11625 = 1 → g ^ 3 = 1) ∨
      (g ^ 31 = 1 ∧ ∀ v : Fin 3 → ZMod 5, v ≠ 0 → ∀ μ : ZMod 5,
        (g : Matrix (Fin 3) (Fin 3) (ZMod 5)) *ᵥ v ≠ μ • v) ∨
      (g ^ 5 = 1 ∧ ∀ v : Fin 3 → ZMod 5, (g : Matrix (Fin 3) (Fin 3) (ZMod 5)) ^ 3 *ᵥ v -
        (3 : ZMod 5) • ((g : Matrix (Fin 3) (Fin 3) (ZMod 5)) ^ 2 *ᵥ v) +
        (3 : ZMod 5) • ((g : Matrix (Fin 3) (Fin 3) (ZMod 5)) *ᵥ v) - v = 0) := by
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  set M := (g : Matrix (Fin 3) (Fin 3) (ZMod 5)) with hMdef
  have hM := aeval_chi g
  rw [← hMdef] at hM
  have hCH := hM
  rw [aeval_chi_eq] at hCH
  have hpow := aeval_triP_powA M _ _ hM
  have hgeq : ∀ n, g ^ n = 1 ↔ M ^ n = 1 := by
    intro n
    rw [hMdef, ← Matrix.SpecialLinearGroup.coe_pow]
    constructor
    · intro hn
      rw [hn, Matrix.SpecialLinearGroup.coe_one]
    · intro hn
      exact Subtype.ext (by rw [hn, Matrix.SpecialLinearGroup.coe_one])
  rcases bucketsOK_sound h M.trace (c2 M) with ⟨u, hu⟩ | ⟨h31, hroot⟩ | ⟨ht, hc⟩
  · left
    intro h11625
    rw [hgeq] at h11625 ⊢
    have h1 := congrArg (fun a => aeval M (triP a)) hu
    try dsimp only at h1
    rw [triP_mulA, map_sub, map_mul, map_mul, hM, mul_zero, sub_zero, triP_sub, map_sub, hpow,
      h11625] at h1
    have h0 : aeval M (triP ((1, 0, 0) : Tri)) = 1 := by rw [aeval_triP]; simp
    rw [h0, sub_self, mul_zero, aeval_triP] at h1
    simp only [zero_smul, zero_add] at h1
    calc M ^ 3 = (M ^ 3 - M.trace • M ^ 2 + c2 M • M - 1) + (-c2 M • M + M.trace • M ^ 2) + 1 := by
          rw [neg_smul]
          abel
      _ = 1 := by rw [hCH, ← h1, zero_add, zero_add]
  · right
    left
    refine ⟨(hgeq 31).mpr ?_, ?_⟩
    · rw [← hpow, h31, aeval_triP]
      simp
    · intro v hv μ hμ
      have h1 : aeval M (chi M.trace (c2 M)) *ᵥ v =
          (μ ^ 3 - M.trace * μ ^ 2 + c2 M * μ - 1) • v := by
        rw [aeval_chi_eq, sub_mulVec, add_mulVec, sub_mulVec, one_mulVec, smul_mulVec,
          smul_mulVec, pow_mulVec_of_eigen hμ, pow_mulVec_of_eigen hμ, hμ, smul_smul,
          smul_smul, sub_smul, add_smul, sub_smul, one_smul]
      rw [hM, zero_mulVec] at h1
      exact hroot μ ((smul_eq_zero.mp h1.symm).resolve_right hv)
  · right
    right
    rw [ht, hc] at hM
    have h0 : (5 : (ZMod 5)[X]) = 0 := by exact_mod_cast CharP.cast_eq_zero (ZMod 5)[X] 5
    have h5 : (X ^ 5 - 1 : (ZMod 5)[X]) = chi 3 3 * (X ^ 2 + 3 * X + 1) := by
      simp only [chi, map_ofNat]
      linear_combination (X ^ 3 - X ^ 2) * h0
    have h6 := congrArg (aeval M) h5
    rw [map_mul, hM, zero_mul, map_sub, aeval_X_pow, map_one, sub_eq_zero] at h6
    refine ⟨(hgeq 5).mpr h6, fun v => ?_⟩
    have h7 := congrArg (fun A => A *ᵥ v) hCH
    try simp only at h7
    rw [ht, hc, sub_mulVec, add_mulVec, sub_mulVec, smul_mulVec, smul_mulVec, one_mulVec,
      zero_mulVec] at h7
    exact h7

end CFSG.KC.C7155

end

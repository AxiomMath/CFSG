module

public import CFSG.Certificates.Kernel.F3PlanesSound

public section

namespace CFSG.F3.Planes

@[expose] noncomputable def fp3RepN (P n : Nat) : Nat :=
  Nat.div (Nat.sub (Nat.shiftLeft 1 (Nat.mul P n)) 1) (Nat.sub (Nat.shiftLeft 1 P) 1)

@[expose] noncomputable def fp3MskK (w e N h o : Nat) (K : Nat → Bool) : Bool :=
  fp3SB (Nat.mul (Nat.shiftLeft (Nat.sub (Nat.shiftLeft 1 (Nat.mul h e)) 1) o)
    (fp3RepN (Nat.mul (Nat.add h h) w)
      (Nat.div (Nat.sub (Nat.add N (Nat.add h h)) 1) (Nat.add h h)))) K

@[expose] noncomputable def fp3GathK (w e N : Nat) : Nat → Nat → Nat → (Nat → Bool) → Bool :=
  Nat.rec (motive := fun _ => Nat → Nat → (Nat → Bool) → Bool) (fun _ x K => K x)
    (fun _ ih l x K =>
      fp3SB (Nat.shiftLeft 1 l) fun h =>
      fp3MskK w e N h (Nat.mul h w) fun M =>
      fp3SB (Nat.land x M) fun a =>
      fp3SB (Nat.xor x a) fun b =>
      fp3SB (Nat.lor b (Nat.shiftRight a (Nat.mul h (Nat.sub w e)))) fun x1 =>
      ih (Nat.succ l) x1 K)

@[expose] noncomputable def fp3ScatK (w e N : Nat) : Nat → Nat → (Nat → Bool) → Bool :=
  Nat.rec (motive := fun _ => Nat → (Nat → Bool) → Bool) (fun x K => K x)
    (fun l ih x K =>
      fp3SB (Nat.shiftLeft 1 l) fun h =>
      fp3MskK w e N h (Nat.mul h e) fun M =>
      fp3SB (Nat.land x M) fun a =>
      fp3SB (Nat.xor x a) fun b =>
      fp3SB (Nat.lor b (Nat.shiftLeft a (Nat.mul h (Nat.sub w e)))) fun x1 =>
      ih x1 K)

@[expose] noncomputable def fp3OfPK (w N L p m : Nat) (K : Nat → Bool) : Bool :=
  fp3ScatK 2 1 N L p fun a => fp3ScatK 2 1 N L m fun b =>
  fp3SB (Nat.lor a (Nat.shiftLeft b 1)) fun i => fp3ScatK w 2 N L i K

@[expose] noncomputable def fp3ToPK (w N L X : Nat) (K : Nat → Nat → Bool) : Bool :=
  fp3GathK w 2 N L 0 X fun G => fp3SB (fp3RepN 2 N) fun R =>
  fp3SB (Nat.land G R) fun a => fp3SB (Nat.land (Nat.shiftRight G 1) R) fun b =>
  fp3GathK 2 1 N L 0 a fun p => fp3GathK 2 1 N L 0 b fun m => K p m

@[expose] def fp3Geo (P : Nat) : Nat → Nat
  | 0 => 0
  | n + 1 => fp3Geo P n + 2 ^ (P * n)

theorem fp3Geo_mul (P : Nat) : ∀ n, fp3Geo P n * (2 ^ P - 1) = 2 ^ (P * n) - 1
  | 0 => by simp [fp3Geo]
  | n + 1 => by
    have ih := fp3Geo_mul P n
    have h1 : 1 ≤ 2 ^ P := Nat.one_le_two_pow
    have h2 : 1 ≤ 2 ^ (P * n) := Nat.one_le_two_pow
    have e : 2 ^ (P * (n + 1)) = 2 ^ (P * n) * 2 ^ P := by rw [Nat.mul_succ, Nat.pow_add]
    rw [fp3Geo, Nat.add_mul, ih, e, Nat.mul_sub, Nat.mul_one]
    have h3 : 2 ^ (P * n) ≤ 2 ^ (P * n) * 2 ^ P := Nat.le_mul_of_pos_right _ (by omega)
    omega

theorem fp3RepN_eq {P : Nat} (hP : 0 < P) (n : Nat) : fp3RepN P n = fp3Geo P n := by
  have h : 0 < 2 ^ P - 1 := by
    have := Nat.one_lt_two_pow (Nat.pos_iff_ne_zero.1 hP)
    omega
  unfold fp3RepN
  change (1 <<< (P * n) - 1) / (1 <<< P - 1) = _
  rw [Nat.shiftLeft_eq, Nat.shiftLeft_eq, Nat.one_mul, Nat.one_mul, ← fp3Geo_mul P n,
    Nat.mul_div_cancel _ h]

theorem fp3Geo_mul_lt {P a : Nat} (ha : a < 2 ^ P) (n : Nat) : a * fp3Geo P n < 2 ^ (P * n) := by
  have h1 : a * fp3Geo P n ≤ (2 ^ P - 1) * fp3Geo P n := Nat.mul_le_mul_right _ (by omega)
  rw [Nat.mul_comm (2 ^ P - 1), fp3Geo_mul] at h1
  have := Nat.one_le_two_pow (n := P * n)
  omega

theorem testBit_mul_fp3Geo {P a : Nat} (ha : a < 2 ^ P) (n j : Nat) :
    (a * fp3Geo P n).testBit j = (decide (j < P * n) && a.testBit (j % P)) := by
  induction n with
  | zero => simp [fp3Geo]
  | succ n ih =>
    have hs := fp3Geo_mul_lt ha n
    have e : a * fp3Geo P (n + 1) = a <<< (P * n) ||| a * fp3Geo P n := by
      rw [fp3Geo, Nat.mul_add, Nat.add_comm, ← Nat.shiftLeft_add_eq_or_of_lt hs, Nat.shiftLeft_eq]
    rw [e, Nat.testBit_or, Nat.testBit_shiftLeft, ih]
    have e2 : P * (n + 1) = P * n + P := Nat.mul_succ P n
    by_cases h1 : j < P * n
    · have : ¬ P * n ≤ j := by omega
      simp [h1, this, show j < P * (n + 1) by omega]
    · have h2 : P * n ≤ j := by omega
      obtain ⟨r, rfl⟩ : ∃ r, j = P * n + r := ⟨j - P * n, by omega⟩
      have em : (P * n + r) % P = r % P := by
        rw [Nat.add_comm, Nat.mul_comm, Nat.add_mul_mod_self_right]
      simp only [h1, decide_false, Bool.false_and, Bool.or_false, h2, decide_true, Bool.true_and,
        Nat.add_sub_cancel_left, em]
      by_cases h3 : r < P
      · rw [Nat.mod_eq_of_lt h3]
        simp [show P * n + r < P * (n + 1) by omega]
      · rw [Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le ha (Nat.pow_le_pow_right (by omega)
          (by omega)))]
        simp [show ¬ P * n + r < P * (n + 1) by omega]

@[expose] def fp3LayB (w e N h : Nat) (B : Nat → Nat → Bool) (j : Nat) : Bool :=
  decide (j % (h * w) < h * e) && decide (j / (h * w) * h + j % (h * w) / e < N) &&
    B (j / (h * w) * h + j % (h * w) / e) (j % (h * w) % e)

theorem fp3DM {j D q r : Nat} (h : j = q * D + r) (hr : r < D) : j / D = q ∧ j % D = r := by
  subst h
  have hD : 0 < D := by omega
  constructor
  · rw [Nat.add_comm, Nat.add_mul_div_right _ _ hD, Nat.div_eq_of_lt hr, Nat.zero_add]
  · rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hr]

theorem testBit_fp3Msk {w e h : Nat} (hew : e ≤ w) (n i : Nat) :
    (((2 ^ (h * e) - 1) <<< (h * e)) * fp3Geo ((h + h) * w) n).testBit i =
      (decide (i < (h + h) * w * n) && decide (h * e ≤ i % ((h + h) * w)) &&
        decide (i % ((h + h) * w) < h * e + h * e)) := by
  have ha : (2 ^ (h * e) - 1) <<< (h * e) < 2 ^ ((h + h) * w) := by
    rw [Nat.shiftLeft_eq]
    have h1 : 2 ^ (h * e) - 1 < 2 ^ (h * e) := Nat.sub_lt (Nat.two_pow_pos _) Nat.one_pos
    have h2 : (2 ^ (h * e) - 1) * 2 ^ (h * e) < 2 ^ (h * e) * 2 ^ (h * e) :=
      Nat.mul_lt_mul_of_pos_right h1 (Nat.two_pow_pos _)
    have h3 : 2 ^ (h * e) * 2 ^ (h * e) ≤ 2 ^ ((h + h) * w) := by
      rw [← Nat.pow_add]
      refine Nat.pow_le_pow_right (by omega) ?_
      rw [Nat.add_mul]
      exact Nat.add_le_add (Nat.mul_le_mul_left h hew) (Nat.mul_le_mul_left h hew)
    omega
  rw [testBit_mul_fp3Geo ha, Nat.testBit_shiftLeft, Nat.testBit_two_pow_sub_one]
  apply Bool.eq_iff_iff.2
  simp only [Bool.and_eq_true, decide_eq_true_eq]
  omega

theorem fp3LtMul {a b r D : Nat} (hr : r < D) : a * D + r < D * b ↔ a < b := by
  rw [Nat.mul_comm D b]
  constructor
  · intro h
    refine Nat.lt_of_not_le fun hc => ?_
    have := Nat.mul_le_mul_right D hc
    omega
  · intro h
    have := Nat.mul_le_mul_right D (Nat.succ_le_of_lt h)
    rw [Nat.succ_mul] at this
    omega

theorem fp3Scat_step {w e N h n : Nat} (hew : e ≤ w) (he : 0 < e) (hh : 0 < h)
    (hn : N ≤ n * (h + h)) {B : Nat → Nat → Bool} {x M : Nat}
    (hx : ∀ j, x.testBit j = fp3LayB w e N (h + h) B j)
    (hM : ∀ i, M.testBit i = (decide (i < (h + h) * w * n) && decide (h * e ≤ i % ((h + h) * w)) &&
      decide (i % ((h + h) * w) < h * e + h * e))) (j : Nat) :
    ((x ^^^ (x &&& M)) ||| ((x &&& M) <<< (h * (w - e)))).testBit j = fp3LayB w e N h B j := by
  simp only [Nat.testBit_or, Nat.testBit_xor, Nat.testBit_and, Nat.testBit_shiftLeft, hx, hM,
    fp3LayB]
  have hHw : (h + h) * w = h * w + h * w := Nat.add_mul h h w
  have hHe : (h + h) * e = h * e + h * e := Nat.add_mul h h e
  have hs : h * (w - e) = h * w - h * e := Nat.mul_sub h w e
  have hEH : h * e ≤ h * w := Nat.mul_le_mul_left h hew
  have hE0 : 0 < h * e := Nat.mul_pos hh he
  rw [hHw, hHe, hs]
  generalize hE : h * e = E at *
  generalize hH : h * w = H at *
  have hNq : ∀ a, n ≤ a → N ≤ a * (h + h) := fun a ha =>
    Nat.le_trans hn (Nat.mul_le_mul_right _ ha)
  obtain ⟨q, r, rfl, hr⟩ : ∃ q r, j = q * (H + H) + r ∧ r < H + H :=
    ⟨j / (H + H), j % (H + H), by rw [Nat.mul_comm, Nat.div_add_mod], Nat.mod_lt _ (by omega)⟩
  obtain ⟨d1, m1⟩ := fp3DM (rfl : q * (H + H) + r = _) hr
  have l1 := fp3LtMul (b := n) hr (a := q)
  rw [d1, m1]
  simp only [l1]
  rcases Nat.lt_or_ge r H with hrH | hrH
  · have e1 : q * (H + H) + r = (q + q) * H + r := by rw [Nat.mul_add, Nat.add_mul]
    obtain ⟨d2, m2⟩ := fp3DM e1 hrH
    have e2 : (q + q) * h = q * (h + h) := by rw [Nat.mul_add, Nat.add_mul]
    rw [d2, m2, e2]
    have hz : (decide (q * (H + H) + r ≥ H - E) &&
        ((decide ((q * (H + H) + r - (H - E)) % (H + H) < E + E) &&
          decide ((q * (H + H) + r - (H - E)) / (H + H) * (h + h) +
            (q * (H + H) + r - (H - E)) % (H + H) / e < N) &&
          B ((q * (H + H) + r - (H - E)) / (H + H) * (h + h) +
            (q * (H + H) + r - (H - E)) % (H + H) / e)
            ((q * (H + H) + r - (H - E)) % (H + H) % e)) &&
        (decide (q * (H + H) + r - (H - E) < (H + H) * n) &&
          decide (E ≤ (q * (H + H) + r - (H - E)) % (H + H)) &&
          decide ((q * (H + H) + r - (H - E)) % (H + H) < E + E)))) = false := by
      rcases Nat.lt_or_ge r (H - E) with h1 | h1
      · rcases q with _ | q
        · simp only [Nat.zero_mul, Nat.zero_add]
          rw [decide_eq_false (by omega), Bool.false_and]
        · have e3 : (q + 1) * (H + H) + r - (H - E) = q * (H + H) + (H + E + r) := by
            rw [Nat.succ_mul]
            omega
          obtain ⟨_, m3⟩ := fp3DM e3 (by omega)
          rw [m3, decide_eq_false (by omega : ¬ (H + E + r < E + E))]
          simp
      · have e3 : q * (H + H) + r - (H - E) = q * (H + H) + (r - (H - E)) := by omega
        obtain ⟨_, m3⟩ := fp3DM e3 (by omega)
        rw [m3, decide_eq_false (by omega : ¬ (E ≤ r - (H - E)))]
        simp
    rw [hz, Bool.or_false]
    rcases Nat.lt_or_ge r E with h1 | h1
    · rw [decide_eq_false (by omega : ¬ (E ≤ r))]
      simp [h1, (by omega : r < E + E)]
    · rw [decide_eq_false (by omega : ¬ (r < E))]
      rcases Nat.lt_or_ge q n with h2 | h2
      · simp only [h1, h2, decide_true, Bool.true_and, Bool.and_true]
        cases decide (r < E + E) <;> simp
      · rw [decide_eq_false (Nat.not_lt.2 (Nat.le_trans (hNq q h2) (Nat.le_add_right _ _)))]
        simp
  · obtain ⟨o, rfl⟩ : ∃ o, r = H + o := ⟨r - H, by omega⟩
    have hoH : o < H := by omega
    have e1 : q * (H + H) + (H + o) = (q + q + 1) * H + o := by
      rw [Nat.mul_add, Nat.add_mul, Nat.add_mul, Nat.one_mul]
      omega
    obtain ⟨d2, m2⟩ := fp3DM e1 hoH
    have e3 : q * (H + H) + (H + o) - (H - E) = q * (H + H) + (E + o) := by omega
    obtain ⟨d3, m3⟩ := fp3DM e3 (by omega)
    have l3 := fp3LtMul (b := n) (by omega : E + o < H + H) (a := q)
    have q1 : (E + o) / e = o / e + h := by
      rw [← hE, Nat.add_comm, Nat.add_mul_div_right _ _ he]
    have q2 : (E + o) % e = o % e := by
      rw [← hE, Nat.add_comm, Nat.add_mul_mod_self_right]
    have e4 : (q + q + 1) * h + o / e = q * (h + h) + (o / e + h) := by
      rw [Nat.add_mul, Nat.add_mul, Nat.mul_add, Nat.one_mul]
      omega
    rw [d2, m2, d3, m3, e3]
    simp only [l3]
    rw [q1, q2, e4, decide_eq_true (by omega : q * (H + H) + (H + o) ≥ H - E),
      decide_eq_true (by omega : E ≤ H + o), decide_eq_true (by omega : E ≤ E + o)]
    rcases Nat.lt_or_ge q n with h2 | h2
    · by_cases h1 : H + o < E + E
      · simp [h1, h2, (by omega : o < E)]
      · by_cases h3 : o < E <;> simp [h1, h2, h3]
    · have hN := Nat.not_lt.2 (Nat.le_trans (hNq q h2) (Nat.le_add_right _ (o / e + h)))
      have hN2 := Nat.not_lt.2 (Nat.le_trans (hNq q h2) (Nat.le_add_right _ ((H + o) / e)))
      simp [hN, hN2]

theorem fp3Ceil (N : Nat) {D : Nat} (hD : 0 < D) : N ≤ (N + D - 1) / D * D := by
  have h1 := Nat.div_add_mod (N + D - 1) D
  have h2 := Nat.mod_lt (N + D - 1) hD
  rw [Nat.mul_comm]
  omega

theorem fp3ScatK_succ (w e N l x : Nat) (K : Nat → Bool) :
    fp3ScatK w e N (l + 1) x K = fp3ScatK w e N l
      ((x ^^^ (x &&& ((1 <<< ((1 <<< l) * e) - 1) <<< ((1 <<< l) * e)) *
          fp3RepN ((1 <<< l + 1 <<< l) * w) ((N + (1 <<< l + 1 <<< l) - 1) / (1 <<< l + 1 <<< l)))) |||
        ((x &&& ((1 <<< ((1 <<< l) * e) - 1) <<< ((1 <<< l) * e)) *
          fp3RepN ((1 <<< l + 1 <<< l) * w) ((N + (1 <<< l + 1 <<< l) - 1) / (1 <<< l + 1 <<< l)))
          <<< ((1 <<< l) * (w - e)))) K := by
  simp only [fp3ScatK, fp3MskK, fp3SB_eq]
  rfl

theorem fp3ScatK_eq {w e N : Nat} (hew : e ≤ w) (he : 0 < e) {B : Nat → Nat → Bool} :
    ∀ (l x : Nat), ∃ y, (∀ K : Nat → Bool, fp3ScatK w e N l x K = K y) ∧
      ((∀ j, x.testBit j = fp3LayB w e N (2 ^ l) B j) → ∀ j, y.testBit j = fp3LayB w e N 1 B j)
  | 0, x => ⟨x, fun _ => rfl, fun hx => by simpa using hx⟩
  | l + 1, x => by
    obtain ⟨y, ey, hy⟩ := fp3ScatK_eq hew he l _
    refine ⟨y, fun K => by rw [fp3ScatK_succ, ey K], fun hx => hy ?_⟩
    have h0 : ∀ k, 1 <<< k = 2 ^ k := fun k => by rw [Nat.shiftLeft_eq, Nat.one_mul]
    have hP : 0 < (2 ^ l + 2 ^ l) * w :=
      Nat.mul_pos (Nat.add_pos_left (Nat.two_pow_pos l) _) (Nat.lt_of_lt_of_le he hew)
    simp only [h0]
    rw [fp3RepN_eq hP]
    exact fp3Scat_step hew he (Nat.two_pow_pos l) (fp3Ceil N (Nat.add_pos_left (Nat.two_pow_pos l) _))
      (fun j => by rw [hx, Nat.pow_succ, Nat.mul_two]) (fun i => testBit_fp3Msk hew _ i)

theorem fp3LayB_top {w e N h : Nat} (hew : e ≤ w) (he : 0 < e) (hh : 0 < h) (hN : N ≤ h)
    (B : Nat → Nat → Bool) (j : Nat) :
    fp3LayB w e N h B j = (decide (j / e < N) && B (j / e) (j % e)) := by
  have hEH : h * e ≤ h * w := Nat.mul_le_mul_left _ hew
  have hE0 : 0 < h * e := Nat.mul_pos hh he
  unfold fp3LayB
  rcases Nat.lt_or_ge j (h * w) with h1 | h1
  · rw [Nat.div_eq_of_lt h1, Nat.mod_eq_of_lt h1, Nat.zero_mul, Nat.zero_add]
    by_cases h2 : j < h * e
    · simp [h2]
    · have h3 : h ≤ j / e := (Nat.le_div_iff_mul_le he).2 (by omega)
      simp [h2, Nat.not_lt.2 (Nat.le_trans hN h3)]
  · have h3 : h ≤ j / e := (Nat.le_div_iff_mul_le he).2 (by omega)
    have h4 : 1 ≤ j / (h * w) := (Nat.le_div_iff_mul_le (by omega)).2 (by omega)
    have h5 : h ≤ j / (h * w) * h := by
      have := Nat.mul_le_mul_right h h4
      rwa [Nat.one_mul] at this
    simp [Nat.not_lt.2 (Nat.le_trans hN h3),
      Nat.not_lt.2 (Nat.le_trans hN (Nat.le_trans h5 (Nat.le_add_right _ (j % (h * w) / e))))]

theorem fp3LayB_one {w e N : Nat} (B : Nat → Nat → Bool) (j : Nat) :
    fp3LayB w e N 1 B j = (decide (j % w < e) && decide (j / w < N) && B (j / w) (j % w)) := by
  unfold fp3LayB
  simp only [Nat.one_mul, Nat.mul_one]
  by_cases h : j % w < e
  · simp [h, Nat.div_eq_of_lt h, Nat.mod_eq_of_lt h]
  · simp [h]

@[expose] def fp3PB (p m t b : Nat) : Bool := if b = 0 then p.testBit t else m.testBit t

theorem fp3ScatK_plane {N L : Nat} (hN : N ≤ 2 ^ L) (p : Nat) :
    ∃ a, (∀ K : Nat → Bool, fp3ScatK 2 1 N L p K = K a) ∧ (p < 2 ^ N →
      ∀ j, a.testBit j = (decide (j % 2 < 1) && decide (j / 2 < N) && p.testBit (j / 2))) := by
  obtain ⟨a, ea, ha⟩ := fp3ScatK_eq (w := 2) (e := 1) (N := N) (B := fun t _ => p.testBit t)
    (by omega) Nat.one_pos L p
  refine ⟨a, ea, fun hp j => ?_⟩
  rw [ha (fun j => ?_), fp3LayB_one]
  rw [fp3LayB_top (by omega) Nat.one_pos (Nat.two_pow_pos L) hN, Nat.div_one]
  by_cases hj : j < N
  · simp [hj]
  · simp [hj, Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hp
      (Nat.pow_le_pow_right (by omega) (Nat.le_of_not_lt hj)))]

theorem fp3OfPK_eq {w N L : Nat} (hw : 2 ≤ w) (hN : N ≤ 2 ^ L) (p m : Nat) :
    ∃ y, (∀ K : Nat → Bool, fp3OfPK w N L p m K = K y) ∧ (p < 2 ^ N → m < 2 ^ N → ∀ j,
      y.testBit j = (decide (j % w < 2) && decide (j / w < N) && fp3PB p m (j / w) (j % w))) := by
  obtain ⟨a, ea, ha⟩ := fp3ScatK_plane hN p
  obtain ⟨b, eb, hb⟩ := fp3ScatK_plane hN m
  obtain ⟨y, ey, hy⟩ := fp3ScatK_eq (w := w) (e := 2) (N := N) (B := fp3PB p m) hw (by omega) L
    (a ||| b <<< 1)
  refine ⟨y, fun K => ?_, fun hp hm j => ?_⟩
  · unfold fp3OfPK
    rw [ea, eb, fp3SB_eq]
    exact ey K
  have hi : ∀ j, (a ||| b <<< 1).testBit j = (decide (j / 2 < N) && fp3PB p m (j / 2) (j % 2)) := by
    intro j
    rw [Nat.testBit_or, Nat.testBit_shiftLeft, ha hp]
    obtain ⟨k, rfl | rfl⟩ : ∃ k, j = 2 * k ∨ j = 2 * k + 1 := ⟨j / 2, by omega⟩
    · rcases k with _ | k
      · simp [fp3PB]
      · rw [hb hm]
        simp [fp3PB, (by omega : (2 * (k + 1) - 1) % 2 = 1), (by omega : 2 * (k + 1) % 2 = 0),
          (by omega : 2 * (k + 1) / 2 = k + 1)]
    · rw [hb hm]
      simp [fp3PB, (by omega : (2 * k + 1) % 2 = 1), (by omega : (2 * k + 1) / 2 = k),
        (by omega : 2 * k + 1 - 1 = 2 * k), (by omega : 2 * k % 2 = 0),
        (by omega : 2 * k / 2 = k)]
  rw [hy (fun j => by rw [hi, fp3LayB_top hw (by omega) (Nat.two_pow_pos L) hN]), fp3LayB_one]

theorem fp3GathK_ex (w e N : Nat) :
    ∀ (n l x : Nat), ∃ y, ∀ K : Nat → Bool, fp3GathK w e N n l x K = K y
  | 0, _, x => ⟨x, fun _ => rfl⟩
  | n + 1, l, x => by
    obtain ⟨y, ey⟩ := fp3GathK_ex w e N n (l + 1)
      ((x ^^^ (x &&& ((1 <<< ((1 <<< l) * e) - 1) <<< ((1 <<< l) * w)) *
          fp3RepN ((1 <<< l + 1 <<< l) * w) ((N + (1 <<< l + 1 <<< l) - 1) / (1 <<< l + 1 <<< l)))) |||
        ((x &&& ((1 <<< ((1 <<< l) * e) - 1) <<< ((1 <<< l) * w)) *
          fp3RepN ((1 <<< l + 1 <<< l) * w) ((N + (1 <<< l + 1 <<< l) - 1) / (1 <<< l + 1 <<< l)))
          >>> ((1 <<< l) * (w - e))))
    refine ⟨y, fun K => ?_⟩
    rw [← ey K]
    simp only [fp3GathK, fp3MskK, fp3SB_eq]
    rfl

theorem fp3ToPK_ex (w N L X : Nat) : ∃ p m, ∀ K : Nat → Nat → Bool, fp3ToPK w N L X K = K p m := by
  obtain ⟨G, eG⟩ := fp3GathK_ex w 2 N L 0 X
  obtain ⟨p, ep⟩ := fp3GathK_ex 2 1 N L 0 (Nat.land G (fp3RepN 2 N))
  obtain ⟨m, em⟩ := fp3GathK_ex 2 1 N L 0 (Nat.land (Nat.shiftRight G 1) (fp3RepN 2 N))
  refine ⟨p, m, fun K => ?_⟩
  unfold fp3ToPK
  rw [eG]
  simp only [fp3SB_eq]
  rw [ep, em]

end CFSG.F3.Planes

end

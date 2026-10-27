module

public import Certificates.Data.Kernel.ExcIns.Grow
public import CFSG.Certificates.Kernel.ExcExt.Sound
public import Certificates.Data.CFSGNative.ExcCensus.Inside
public import CFSG.LocalAnalysis.StandardType.GGQ2ExcRaw

public section

noncomputable section

namespace CFSG.ExcInsK

open CFSG.ExcExtK CFSG.StandardType.GGQ2Frame.ExcRaw

theorem ln7_rowK (K : KT) {u t : Nat} (ht : t < K.r) : ln7 (rowK K u) t = rtK K u t := by
  have em : Nat.sub (Nat.shiftLeft 1 (Nat.mul 7 K.r)) 1 = 2 ^ (7 * K.r) - 1 := by
    change 1 <<< (7 * K.r) - 1 = _
    rw [Nat.shiftLeft_eq, Nat.one_mul]
  unfold rtK rowK ln7
  rw [em]
  change ((K.rt >>> (7 * (K.r * u)) &&& (2 ^ (7 * K.r) - 1)) >>> (7 * t) &&& 2 ^ 7 - 1) =
    (K.rt >>> (7 * (K.r * u + t)) &&& 2 ^ 7 - 1)
  apply Nat.eq_of_testBit_eq
  intro i
  simp only [Nat.testBit_and, Nat.testBit_shiftRight, Nat.testBit_two_pow_sub_one]
  by_cases hi : i < 7
  · have h1 : 7 * t + i < 7 * K.r := by omega
    have h2 : 7 * (K.r * u) + (7 * t + i) = 7 * (K.r * u + t) + i := by ring
    simp [hi, h1, h2]
  · simp [hi]

theorem imgK_eq {m : Fin 6} {K : KT} {fx hx fx' hx' : Nat} (h : TabsOK m K fx hx fx' hx')
    {u : Nat} (hu : u < nroots m) (c : Nat) :
    imgK (rowK K u) K.r c = Chk.imgN (tabsK m K) (nroots m) u c := by
  have key : ∀ n, n ≤ K.r → Nat.rec (motive := fun _ => Nat) 0
      (fun t acc => nif (bit c t) (Nat.lor acc (Nat.shiftLeft 1 (ln7 (rowK K u) t))) acc) n =
      Nat.fold n (fun t _ acc =>
        if c.testBit t then acc ||| 1 <<< ((tabsK m K).rt[u]!)[t]! else acc) 0 := by
    intro n
    induction n with
    | zero =>
      intro _
      rw [Nat.fold_zero]
      rfl
    | succ n ih =>
      intro hn
      simp only [Nat.fold_succ]
      rw [← ih (by omega)]
      have ht : n < nroots m := by rw [← h.hr]; omega
      rw [tabsK_rt hu ht, ← ln7_rowK K (by omega : n < K.r)]
      change nif (bit c n) _ _ = _
      rw [nif_eq, bit_eq]
      rfl
  rw [imgK, key K.r le_rfl, Chk.imgN, ← h.hr]

theorem wordK_eq {m : Fin 6} {K : KT} {fx hx fx' hx' : Nat} (h : TabsOK m K fx hx fx' hx')
    (w : List Nat) (hw : ∀ u ∈ w, u < nroots m) (c : Nat) :
    wordK K w c = w.foldr (fun u acc => Chk.imgN (tabsK m K) (nroots m) u acc) c := by
  induction w with
  | nil => rfl
  | cons u w ih =>
    have e : wordK K (u :: w) c = imgK (rowK K u) K.r (wordK K w c) := rfl
    rw [e, ih (fun v hv => hw v (List.mem_cons_of_mem _ hv)), List.foldr_cons,
      imgK_eq h (hw u (by simp)) _]

theorem geo_sum (Q : Nat) : ∀ N, Q * (∑ j ∈ Finset.range N, (Q + 1) ^ j) + 1 = (Q + 1) ^ N
  | 0 => by simp
  | N + 1 => by
    rw [Finset.sum_range_succ, Nat.mul_add, Nat.add_right_comm, geo_sum Q N, pow_succ]
    ring

theorem testBit_rep {B L : Nat} (hB : B < 2 ^ L) : ∀ N v,
    (B * ∑ j ∈ Finset.range N, (2 ^ L) ^ j).testBit v =
      (decide (v < L * N) && B.testBit (v % L))
  | 0, v => by simp
  | N + 1, v => by
    have e1 : ∑ j ∈ Finset.range (N + 1), (2 ^ L) ^ j =
        2 ^ L * ∑ j ∈ Finset.range N, (2 ^ L) ^ j + 1 := by
      rw [Finset.sum_range_succ', Finset.mul_sum]
      simp [pow_succ, Nat.mul_comm]
    have e : B * ∑ j ∈ Finset.range (N + 1), (2 ^ L) ^ j =
        2 ^ L * (B * ∑ j ∈ Finset.range N, (2 ^ L) ^ j) + B := by
      rw [e1]
      ring
    rw [e, Nat.testBit_two_pow_mul_add _ hB, testBit_rep hB N]
    by_cases hv : v < L
    · have h1 : v < L * (N + 1) := by rw [Nat.mul_succ]; omega
      rw [if_pos hv, Nat.mod_eq_of_lt hv, decide_eq_true h1, Bool.true_and]
    · rw [if_neg hv]
      have hL : (v - L) % L = v % L := by
        conv_rhs => rw [show v = (v - L) + L by omega]
        rw [Nat.add_mod_right]
      have h2 : (v - L < L * N) ↔ (v < L * (N + 1)) := by rw [Nat.mul_succ]; omega
      rw [hL, decide_eq_decide.mpr h2]

theorem testBit_digP {W k a d : Nat} (hW : W = 3 ^ d) (hk : k < d) (ha : a < 3) (v : Nat) :
    (digP W k a).testBit v = (decide (v < W) && digK v k == a) := by
  have hq : 0 < 3 ^ k := Nat.pos_of_ne_zero (by positivity)
  have hL : W = (3 * 3 ^ k) * 3 ^ (d - k - 1) := by
    rw [hW, ← pow_succ', ← pow_add]
    congr 1
    omega
  have e1 : Nat.sub (Nat.shiftLeft 1 (Nat.pow 3 k)) 1 = 2 ^ 3 ^ k - 1 := by
    change 1 <<< 3 ^ k - 1 = _
    rw [Nat.shiftLeft_eq, Nat.one_mul]
  have e2 : Nat.sub (Nat.shiftLeft 1 W) 1 = 2 ^ W - 1 := by
    change 1 <<< W - 1 = _
    rw [Nat.shiftLeft_eq, Nat.one_mul]
  have e3 : Nat.sub (Nat.shiftLeft 1 (Nat.mul 3 (Nat.pow 3 k))) 1 = 2 ^ (3 * 3 ^ k) - 1 := by
    change 1 <<< (3 * 3 ^ k) - 1 = _
    rw [Nat.shiftLeft_eq, Nat.one_mul]
  have hpos : 0 < 2 ^ (3 * 3 ^ k) - 1 := by
    have : 2 ≤ 2 ^ (3 * 3 ^ k) :=
      calc 2 = 2 ^ 1 := rfl
        _ ≤ 2 ^ (3 * 3 ^ k) := Nat.pow_le_pow_right (by decide) (by omega)
    omega
  have hG : (2 ^ W - 1) / (2 ^ (3 * 3 ^ k) - 1) =
      ∑ j ∈ Finset.range (3 ^ (d - k - 1)), (2 ^ (3 * 3 ^ k)) ^ j := by
    have hP : 2 ^ (3 * 3 ^ k) - 1 + 1 = 2 ^ (3 * 3 ^ k) := Nat.sub_add_cancel Nat.one_le_two_pow
    have hgeo := geo_sum (2 ^ (3 * 3 ^ k) - 1) (3 ^ (d - k - 1))
    rw [hP] at hgeo
    rw [hL, pow_mul, ← hgeo, Nat.add_sub_cancel, Nat.mul_div_cancel_left _ hpos]
  have hB : (2 ^ 3 ^ k - 1) <<< (a * 3 ^ k) < 2 ^ (3 * 3 ^ k) := by
    rw [Nat.shiftLeft_eq]
    have h1 : 2 ^ 3 ^ k - 1 < 2 ^ 3 ^ k := Nat.sub_lt Nat.one_le_two_pow (by decide)
    calc (2 ^ 3 ^ k - 1) * 2 ^ (a * 3 ^ k) < 2 ^ 3 ^ k * 2 ^ (a * 3 ^ k) :=
          Nat.mul_lt_mul_of_pos_right h1 (Nat.two_pow_pos _)
      _ = 2 ^ ((a + 1) * 3 ^ k) := by rw [← Nat.pow_add]; congr 1; ring
      _ ≤ 2 ^ (3 * 3 ^ k) := Nat.pow_le_pow_right (by decide) (Nat.mul_le_mul_right _ (by omega))
  unfold digP
  rw [e1, e2, e3]
  change (((2 ^ 3 ^ k - 1) <<< (a * 3 ^ k)) * ((2 ^ W - 1) / (2 ^ (3 * 3 ^ k) - 1))).testBit v = _
  rw [hG]
  change ((2 ^ 3 ^ k - 1) <<< (a * 3 ^ k) * ∑ j ∈ Finset.range (3 ^ (d - k - 1)),
    (2 ^ (3 * 3 ^ k)) ^ j).testBit v = _
  rw [testBit_rep hB, ← hL, Nat.testBit_shiftLeft, Nat.testBit_two_pow_sub_one]
  have hdig : digK v k = v % (3 ^ k * 3) / 3 ^ k := by
    rw [Nat.mod_mul_right_div_self]
    rfl
  rw [hdig, Nat.mul_comm (3 ^ k) 3]
  generalize hx : v % (3 * 3 ^ k) = x
  have hiff : (x ≥ a * 3 ^ k ∧ x - a * 3 ^ k < 3 ^ k) ↔ x / 3 ^ k = a := by
    rw [show x / 3 ^ k = a ↔ a ≤ x / 3 ^ k ∧ x / 3 ^ k < a + 1 by omega,
      Nat.le_div_iff_mul_le hq, Nat.div_lt_iff_lt_mul hq, Nat.add_mul, Nat.one_mul]
    omega
  cases hv : decide (v < W)
  · rfl
  · rw [Bool.true_and, Bool.true_and, ← Bool.decide_and, Bool.eq_iff_iff, decide_eq_true_eq,
      beq_iff_eq]
    exact hiff

theorem testBit_termP {W k d f t : Nat} (hW : W = 3 ^ d) (hk : k < d) (v : Nat) :
    (termP W k f t).testBit v = (decide (v < W) && (f * digK v k) % 3 == t % 3) := by
  have hdig : digK v k < 3 := Nat.mod_lt _ (by decide)
  unfold termP
  change ((nif _ _ 0) ||| ((nif _ _ 0) ||| (nif _ _ 0))).testBit v = _
  rw [Nat.testBit_or, Nat.testBit_or, nif_eq, nif_eq, nif_eq]
  simp only [nbeq_eq, xk_mod, xk_mul]
  have hd0 := testBit_digP hW hk (a := 0) (by decide) v
  have hd1 := testBit_digP hW hk (a := 1) (by decide) v
  have hd2 := testBit_digP hW hk (a := 2) (by decide) v
  rcases (by omega : digK v k = 0 ∨ digK v k = 1 ∨ digK v k = 2) with hd | hd | hd <;>
    rw [hd] at hd0 hd1 hd2 ⊢ <;>
    by_cases h0 : t % 3 = 0 <;> by_cases h1 : f % 3 = t % 3 <;> by_cases h2 : 2 * f % 3 = t % 3 <;>
    cases hv : decide (v < W) <;>
    simp_all [Nat.zero_testBit] <;> omega

theorem stepP_spec {W k d f : Nat} (hW : W = 3 ^ d) (hk : k < d) {Z O T : Nat} {g : Nat → Nat}
    (hg : ∀ v, g v < 3)
    (hZ : ∀ v, Z.testBit v = (decide (v < W) && g v == 0))
    (hO : ∀ v, O.testBit v = (decide (v < W) && g v == 1))
    (hT : ∀ v, T.testBit v = (decide (v < W) && g v == 2)) :
    ∃ Z' O' T', stepP W k f (Z ||| ((O <<< W) ||| (T <<< (2 * W)))) =
        Z' ||| ((O' <<< W) ||| (T' <<< (2 * W))) ∧
      (∀ v, Z'.testBit v = (decide (v < W) && (g v + f * digK v k) % 3 == 0)) ∧
      (∀ v, O'.testBit v = (decide (v < W) && (g v + f * digK v k) % 3 == 1)) ∧
      (∀ v, T'.testBit v = (decide (v < W) && (g v + f * digK v k) % 3 == 2)) := by
  have em : Nat.sub (Nat.shiftLeft 1 W) 1 = 2 ^ W - 1 := by
    change 1 <<< W - 1 = _
    rw [Nat.shiftLeft_eq, Nat.one_mul]
  have hZ' : ∀ u, W ≤ u → Z.testBit u = false := fun u hu => by
    rw [hZ, decide_eq_false (by omega), Bool.false_and]
  have hO' : ∀ u, W ≤ u → O.testBit u = false := fun u hu => by
    rw [hO, decide_eq_false (by omega), Bool.false_and]
  have u1 : (Z ||| ((O <<< W) ||| (T <<< (2 * W)))) &&& (2 ^ W - 1) = Z := by
    apply Nat.eq_of_testBit_eq
    intro u
    simp only [Nat.testBit_and, Nat.testBit_or, Nat.testBit_shiftLeft, Nat.testBit_two_pow_sub_one]
    by_cases hu : u < W
    · simp [hu, show ¬ (u ≥ W) by omega, show ¬ (u ≥ 2 * W) by omega]
    · simp [hu, hZ' u (by omega)]
  have u2 : ((Z ||| ((O <<< W) ||| (T <<< (2 * W)))) >>> W) &&& (2 ^ W - 1) = O := by
    apply Nat.eq_of_testBit_eq
    intro u
    simp only [Nat.testBit_and, Nat.testBit_or, Nat.testBit_shiftLeft, Nat.testBit_shiftRight,
      Nat.testBit_two_pow_sub_one]
    by_cases hu : u < W
    · simp [hu, hZ' (W + u) (by omega), show ¬ (W + u ≥ 2 * W) by omega]
    · simp [hu, hO' u (by omega)]
  have u3 : (Z ||| ((O <<< W) ||| (T <<< (2 * W)))) >>> (2 * W) = T := by
    apply Nat.eq_of_testBit_eq
    intro u
    simp only [Nat.testBit_or, Nat.testBit_shiftLeft, Nat.testBit_shiftRight]
    simp [hZ' (2 * W + u) (by omega), hO' (2 * W + u - W) (by omega),
      show 2 * W + u - 2 * W = u by omega]
  have hE : ∀ t v, (termP W k f t).testBit v = (decide (v < W) && (f * digK v k) % 3 == t % 3) :=
    fun t v => testBit_termP hW hk v
  refine ⟨Nat.lor (Nat.lor (Nat.land Z (termP W k f 0)) (Nat.land O (termP W k f 2)))
      (Nat.land T (termP W k f 1)),
    Nat.lor (Nat.lor (Nat.land Z (termP W k f 1)) (Nat.land O (termP W k f 0)))
      (Nat.land T (termP W k f 2)),
    Nat.lor (Nat.lor (Nat.land Z (termP W k f 2)) (Nat.land O (termP W k f 1)))
      (Nat.land T (termP W k f 0)), ?_, ?_, ?_, ?_⟩
  · unfold stepP
    rw [em]
    change addP W ((Z ||| ((O <<< W) ||| (T <<< (2 * W)))) &&& (2 ^ W - 1))
      (((Z ||| ((O <<< W) ||| (T <<< (2 * W)))) >>> W) &&& (2 ^ W - 1))
      ((Z ||| ((O <<< W) ||| (T <<< (2 * W)))) >>> (2 * W)) _ _ _ = _
    rw [u1, u2, u3]
    rfl
  all_goals
    intro v
    change ((((_ : Nat) &&& (_ : Nat)) ||| ((_ : Nat) &&& (_ : Nat))) |||
      ((_ : Nat) &&& (_ : Nat))).testBit v = _
    simp only [Nat.testBit_or, Nat.testBit_and, hZ, hO, hT, hE]
    have hgv := hg v
    have hb : f * digK v k % 3 < 3 := Nat.mod_lt _ (by decide)
    rw [show (g v + f * digK v k) % 3 = (g v + f * digK v k % 3) % 3 by omega]
    generalize g v = a at hgv ⊢
    generalize f * digK v k % 3 = b at hb ⊢
    cases decide (v < W) <;> interval_cases a <;> interval_cases b <;> rfl

theorem planeRec_spec {W d : Nat} (hW : W = 3 ^ d) (K : KT) (s : Nat) : ∀ k, k ≤ d →
    ∃ Z O T, Nat.rec (motive := fun _ => Nat) (Nat.sub (Nat.shiftLeft 1 W) 1)
        (fun k st => stepP W k (fK K s k) st) k = Z ||| ((O <<< W) ||| (T <<< (2 * W))) ∧
      (∀ v, Z.testBit v = (decide (v < W) &&
        (sumN k fun k' => Nat.mul (fK K s k') (digK v k')) % 3 == 0)) ∧
      (∀ v, O.testBit v = (decide (v < W) &&
        (sumN k fun k' => Nat.mul (fK K s k') (digK v k')) % 3 == 1)) ∧
      (∀ v, T.testBit v = (decide (v < W) &&
        (sumN k fun k' => Nat.mul (fK K s k') (digK v k')) % 3 == 2))
  | 0, _ => by
    refine ⟨2 ^ W - 1, 0, 0, ?_, ?_, ?_, ?_⟩
    · change 1 <<< W - 1 = _
      rw [Nat.shiftLeft_eq, Nat.one_mul]
      simp
    · intro v
      rw [Nat.testBit_two_pow_sub_one, sumN_zero]
      simp
    · intro v
      simp [sumN_zero]
    · intro v
      simp [sumN_zero]
  | k + 1, hk => by
    obtain ⟨Z, O, T, e, hZ, hO, hT⟩ := planeRec_spec hW K s k (by omega)
    obtain ⟨Z', O', T', e', hZ', hO', hT'⟩ := stepP_spec (f := fK K s k) hW (by omega : k < d)
      (g := fun v => (sumN k fun k' => Nat.mul (fK K s k') (digK v k')) % 3)
      (fun v => Nat.mod_lt _ (by decide)) hZ hO hT
    have hs : ∀ v, ((sumN k fun k' => Nat.mul (fK K s k') (digK v k')) % 3 + fK K s k * digK v k) % 3 =
        (sumN (k + 1) fun k' => Nat.mul (fK K s k') (digK v k')) % 3 := fun v => by
      rw [sumN_succ, Nat.mod_add_mod]
      rfl
    refine ⟨Z', O', T', ?_, fun v => by rw [hZ', hs], fun v => by rw [hO', hs],
      fun v => by rw [hT', hs]⟩
    change stepP W k (fK K s k) (Nat.rec (motive := fun _ => Nat) (Nat.sub (Nat.shiftLeft 1 W) 1)
      (fun k st => stepP W k (fK K s k) st) k) = _
    rw [e, e']

theorem testBit_maskK (p : Nat → Bool) (j : Nat) :
    ∀ n, (maskK n p).testBit j = (decide (j < n) && p j)
  | 0 => by
    change (0 : Nat).testBit j = _
    simp
  | n + 1 => by
    change (nif (p n) (Nat.lor (maskK n p) (Nat.shiftLeft 1 n)) (maskK n p)).testBit j = _
    rw [nif_eq]
    have hb : (Nat.lor (maskK n p) (Nat.shiftLeft 1 n)).testBit j =
        ((maskK n p).testBit j || decide (n = j)) := by
      change ((maskK n p) ||| 1 <<< n).testBit j = _
      rw [Nat.testBit_or, Nat.shiftLeft_eq, Nat.one_mul, Nat.testBit_two_pow]
    by_cases hj : j = n
    · subst hj
      cases hpn : p j
      · simp [testBit_maskK p j j]
      · simp [hb, testBit_maskK p j j]
    · have hne : n ≠ j := fun e => hj e.symm
      have hlt : (j < n + 1) ↔ j < n := by omega
      split
      · rw [hb, testBit_maskK p j n]
        simp [hne, hlt]
      · rw [testBit_maskK p j n]
        simp [hlt]

theorem testBit_planeK {m : Fin 6} {K : KT} {fx hx fx' hx' : Nat} (h : TabsOK m K fx hx fx' hx')
    {s : Nat} (hs : s < nroots m) (v : Nat) :
    (ExcInsK.planeK K (3 ^ dim m) s).testBit v =
      (decide (v < 3 ^ dim m) && ((tabsK m K).zm[v]!).testBit s) := by
  obtain ⟨Z, O, T, e, hZ, -, -⟩ := planeRec_spec (W := 3 ^ dim m) rfl K s K.d (by rw [h.hd])
  have em : Nat.sub (Nat.shiftLeft 1 (3 ^ dim m)) 1 = 2 ^ 3 ^ dim m - 1 := by
    change 1 <<< 3 ^ dim m - 1 = _
    rw [Nat.shiftLeft_eq, Nat.one_mul]
  have hP : ExcInsK.planeK K (3 ^ dim m) s = Z := by
    unfold ExcInsK.planeK
    rw [e, em]
    apply Nat.eq_of_testBit_eq
    intro u
    change ((Z ||| ((O <<< 3 ^ dim m) ||| (T <<< (2 * 3 ^ dim m)))) &&& (2 ^ 3 ^ dim m - 1)).testBit u = _
    simp only [Nat.testBit_and, Nat.testBit_or, Nat.testBit_shiftLeft, Nat.testBit_two_pow_sub_one]
    by_cases hu : u < 3 ^ dim m
    · simp [hu, show ¬ (u ≥ 3 ^ dim m) by omega, show ¬ (u ≥ 2 * 3 ^ dim m) by omega]
    · simp [hu, hZ u]
  rw [hP, hZ v]
  by_cases hv : v < 3 ^ dim m
  · rw [decide_eq_true hv, Bool.true_and, Bool.true_and, tabsK_zm hv]
    have hz := h.hzm v hv
    rw [Nat.beq_eq] at hz
    have hsr : s < K.r := by rw [h.hr]; exact hs
    rw [hz, testBit_maskK, decide_eq_true hsr, Bool.true_and]
    unfold zBitK
    rw [nbeq_eq]
    rfl
  · rw [decide_eq_false hv]
    rfl

theorem planesFrom_sound {K : KT} {W : Nat} : ∀ (PL : List Nat) (s : Nat),
    planesFrom K W PL s = true →
      s + PL.length = K.r ∧ ∀ p (hp : p < PL.length), PL[p] = ExcInsK.planeK K W (s + p)
  | [], s, hL => by
    refine ⟨?_, fun p hp => absurd hp (Nat.not_lt_zero p)⟩
    have e : planesFrom K W [] s = Nat.beq s K.r := rfl
    rw [e, Nat.beq_eq] at hL
    simpa using hL
  | q :: PL, s, hL => by
    have e : planesFrom K W (q :: PL) s =
        band (Nat.beq q (ExcInsK.planeK K W s)) (planesFrom K W PL (Nat.succ s)) := rfl
    rw [e, band_eq_true, Nat.beq_eq] at hL
    obtain ⟨h1, h2⟩ := planesFrom_sound PL (Nat.succ s) hL.2
    refine ⟨by simp only [List.length_cons]; omega, fun p hp => ?_⟩
    rcases p with _ | p
    · simpa using hL.1
    · have := h2 p (by simpa using hp)
      rw [show s + (p + 1) = Nat.succ s + p by omega]
      simpa using this

theorem testBit_meetK {c : Nat} : ∀ (PL : List Nat) (s A v : Nat),
    (meetK PL c s A).testBit v = true ↔
      A.testBit v = true ∧ ∀ p (hp : p < PL.length), c.testBit (s + p) = true → PL[p].testBit v = true
  | [], s, A, v => by
    change A.testBit v = true ↔ _
    simp
  | q :: PL, s, A, v => by
    change (meetK PL c (Nat.succ s) (nif (bit c s) (Nat.land A q) A)).testBit v = true ↔ _
    rw [testBit_meetK PL (Nat.succ s), nif_eq, bit_eq]
    constructor
    · rintro ⟨h1, h2⟩
      have hA : A.testBit v = true := by
        split at h1
        · change (A &&& q).testBit v = true at h1
          rw [Nat.testBit_and, Bool.and_eq_true] at h1
          exact h1.1
        · exact h1
      refine ⟨hA, fun p hp hc => ?_⟩
      rcases p with _ | p
      · rw [Nat.add_zero] at hc
        rw [if_pos hc] at h1
        change (A &&& q).testBit v = true at h1
        rw [Nat.testBit_and, Bool.and_eq_true] at h1
        rw [List.getElem_cons_zero]
        exact h1.2
      · have := h2 p (by simpa using hp) (by rw [show Nat.succ s + p = s + (p + 1) by omega]; exact hc)
        rw [List.getElem_cons_succ]
        exact this
    · rintro ⟨h1, h2⟩
      refine ⟨?_, fun p hp hc => ?_⟩
      · split
        · rename_i hcs
          change (A &&& q).testBit v = true
          rw [Nat.testBit_and, Bool.and_eq_true]
          have := h2 0 (by simp) (by rw [Nat.add_zero]; exact hcs)
          rw [List.getElem_cons_zero] at this
          exact ⟨h1, this⟩
        · exact h1
      · have := h2 (p + 1) (by simpa using hp) (by rw [show s + (p + 1) = Nat.succ s + p by omega]; exact hc)
        rw [List.getElem_cons_succ] at this
        exact this

theorem testBit_overK {A : Nat} : ∀ (PL : List Nat) (s acc u : Nat),
    (overK PL A s acc).testBit u = true ↔
      acc.testBit u = true ∨ ∃ p, ∃ hp : p < PL.length, u = s + p ∧ A &&& PL[p] = A
  | [], s, acc, u => by
    change acc.testBit u = true ↔ _
    simp
  | q :: PL, s, acc, u => by
    change (overK PL A (Nat.succ s)
      (nif (Nat.beq (Nat.land A q) A) (Nat.lor acc (Nat.shiftLeft 1 s)) acc)).testBit u = true ↔ _
    rw [testBit_overK PL (Nat.succ s), nif_eq, nbeq_eq]
    have hb : ∀ x, (Nat.lor x (Nat.shiftLeft 1 s)).testBit u = (x.testBit u || decide (s = u)) := by
      intro x
      change (x ||| 1 <<< s).testBit u = _
      rw [Nat.testBit_or, Nat.shiftLeft_eq, Nat.one_mul, Nat.testBit_two_pow]
    constructor
    · rintro (h1 | ⟨p, hp, rfl, h2⟩)
      · split at h1
        · rename_i hq
          rw [hb, Bool.or_eq_true, decide_eq_true_eq] at h1
          rcases h1 with h1 | h1
          · exact Or.inl h1
          · subst h1
            refine Or.inr ⟨0, by simp, by simp, ?_⟩
            rw [List.getElem_cons_zero]
            exact beq_iff_eq.mp hq
        · exact Or.inl h1
      · refine Or.inr ⟨p + 1, by simpa using hp, by omega, ?_⟩
        rw [List.getElem_cons_succ]
        exact h2
    · rintro (h1 | ⟨p, hp, rfl, h2⟩)
      · left
        split
        · rw [hb, h1, Bool.true_or]
        · exact h1
      · rcases p with _ | p
        · left
          rw [List.getElem_cons_zero] at h2
          have hq : (Nat.land A q == A) = true := beq_iff_eq.mpr h2
          rw [if_pos hq, hb]
          simp
        · right
          rw [List.getElem_cons_succ] at h2
          exact ⟨p, by simpa using hp, by omega, h2⟩

theorem testBit_closN_fold (T : Chk.Tabs) (c u : Nat) : ∀ (n init : Nat),
    (Nat.fold n (fun v _ acc => if Chk.subN c T.zm[v]! then acc &&& T.zm[v]! else acc) init).testBit u
      = true ↔ init.testBit u = true ∧ ∀ v < n, Chk.subN c T.zm[v]! = true → (T.zm[v]!).testBit u = true
  | 0, init => by simp
  | n + 1, init => by
    rw [Nat.fold_succ]
    constructor
    · intro h1
      have key : (Nat.fold n (fun v _ acc => if Chk.subN c T.zm[v]! then acc &&& T.zm[v]! else acc)
          init).testBit u = true ∧ (Chk.subN c T.zm[n]! = true → (T.zm[n]!).testBit u = true) := by
        split at h1
        · rw [Nat.testBit_and, Bool.and_eq_true] at h1
          exact ⟨h1.1, fun _ => h1.2⟩
        · rename_i hs
          exact ⟨h1, fun h' => absurd h' hs⟩
      obtain ⟨h2, h3⟩ := (testBit_closN_fold T c u n init).mp key.1
      refine ⟨h2, fun v hv hs => ?_⟩
      rcases Nat.lt_succ_iff_lt_or_eq.mp hv with hv | rfl
      · exact h3 v hv hs
      · exact key.2 hs
    · rintro ⟨h1, h2⟩
      have hf := (testBit_closN_fold T c u n init).mpr ⟨h1, fun v hv => h2 v (by omega)⟩
      split
      · rename_i hs
        rw [Nat.testBit_and, Bool.and_eq_true]
        exact ⟨hf, h2 n (by omega) hs⟩
      · exact hf

theorem closK_eq {m : Fin 6} {K : KT} {fx hx fx' hx' : Nat} (h : TabsOK m K fx hx fx' hx')
    {PL : List Nat} (hP : planesOK K (3 ^ dim m) PL = true) {c : Nat} (hc : c < 2 ^ nroots m) :
    closK PL (3 ^ dim m) c = Chk.closN (tabsK m K) (dim m) (nroots m) c := by
  obtain ⟨hlen, hPL⟩ := planesFrom_sound PL 0 hP
  rw [Nat.zero_add, h.hr] at hlen
  have hPL' : ∀ p (hp : p < PL.length) v, PL[p].testBit v =
      (decide (v < 3 ^ dim m) && ((tabsK m K).zm[v]!).testBit p) := fun p hp v => by
    rw [hPL p hp, Nat.zero_add, testBit_planeK h (by omega) v]
  have em : Nat.sub (Nat.shiftLeft 1 (3 ^ dim m)) 1 = 2 ^ 3 ^ dim m - 1 := by
    change 1 <<< 3 ^ dim m - 1 = _
    rw [Nat.shiftLeft_eq, Nat.one_mul]
  have hc' : ∀ p, c.testBit p = true → p < nroots m := fun p hp => by
    by_contra hpr
    rw [Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hc (Nat.pow_le_pow_right (by decide) (by omega)))]
      at hp
    exact Bool.false_ne_true hp
  have hmeet : ∀ v, (meetK PL c 0 (Nat.sub (Nat.shiftLeft 1 (3 ^ dim m)) 1)).testBit v = true ↔
      v < 3 ^ dim m ∧ Chk.subN c (tabsK m K).zm[v]! = true := by
    intro v
    rw [testBit_meetK, em, Nat.testBit_two_pow_sub_one, decide_eq_true_eq, Chk.subN, beq_iff_eq]
    constructor
    · rintro ⟨hv, h2⟩
      refine ⟨hv, Nat.eq_of_testBit_eq fun p => ?_⟩
      rw [Nat.testBit_and]
      cases hcp : c.testBit p
      · rfl
      · have := h2 p (by rw [hlen]; exact hc' p hcp) (by rw [Nat.zero_add]; exact hcp)
        rw [hPL' p _ v, Bool.and_eq_true] at this
        rw [this.2]
        rfl
    · rintro ⟨hv, h2⟩
      refine ⟨hv, fun p hp hcp => ?_⟩
      rw [Nat.zero_add] at hcp
      rw [hPL' p hp v, decide_eq_true hv, Bool.true_and]
      have := congrArg (fun x => x.testBit p) h2
      simp only [Nat.testBit_and, hcp, Bool.true_and] at this
      exact this
  apply Nat.eq_of_testBit_eq
  intro u
  apply Bool.eq_iff_iff.mpr
  unfold closK
  rw [testBit_overK, Chk.closN, testBit_closN_fold, Nat.testBit_two_pow_sub_one, decide_eq_true_eq]
  simp only [Nat.zero_testBit, Bool.false_eq_true, false_or, Nat.zero_add]
  constructor
  · rintro ⟨p, hp, hup, h2⟩
    rw [hup]
    refine ⟨by omega, fun v hv hs => ?_⟩
    have hmv := (hmeet v).mpr ⟨hv, hs⟩
    have := congrArg (fun x => x.testBit v) h2
    simp only [Nat.testBit_and, hmv, Bool.true_and] at this
    rw [hPL' p hp v, Bool.and_eq_true] at this
    exact this.2
  · rintro ⟨hu, h2⟩
    refine ⟨u, by omega, rfl, Nat.eq_of_testBit_eq fun v => ?_⟩
    rw [Nat.testBit_and]
    cases hmv : (meetK PL c 0 (Nat.sub (Nat.shiftLeft 1 (3 ^ dim m)) 1)).testBit v
    · rfl
    · obtain ⟨hv, hs⟩ := (hmeet v).mp hmv
      rw [hPL' u (by omega) v, decide_eq_true hv, Bool.true_and, h2 v hv hs]
      rfl

theorem stepK_eq {m : Fin 6} {K : KT} {fx hx fx' hx' : Nat} (h : TabsOK m K fx hx fx' hx')
    (M S : Nat) : stepK K M S = Chk.growN (tabsK m K) (nroots m) M S := by
  have key : ∀ n, n ≤ K.r → Nat.rec (motive := fun _ => Nat) S
      (fun t acc => nif (bit S t) (Nat.lor acc (Nat.land (adjK K t) M)) acc) n =
      Nat.fold n (fun t _ acc =>
        if S.testBit t then acc ||| ((tabsK m K).adj[t]! &&& M) else acc) S := by
    intro n
    induction n with
    | zero =>
      intro _
      rw [Nat.fold_zero]
      rfl
    | succ n ih =>
      intro hn
      simp only [Nat.fold_succ]
      rw [← ih (by omega), tabsK_adj (by rw [← h.hr]; omega : n < nroots m)]
      change nif (bit S n) _ _ = _
      rw [nif_eq, bit_eq]
      rfl
  rw [stepK, key K.r le_rfl, Chk.growN, ← h.hr]

theorem repeat_comm (f : Nat → Nat) : ∀ n S, Nat.repeat f n (f S) = f (Nat.repeat f n S)
  | 0, _ => rfl
  | n + 1, S => by
    change f (Nat.repeat f n (f S)) = f (f (Nat.repeat f n S))
    rw [repeat_comm f n S]

theorem growIt_eq (K : KT) (M : Nat) (f : Nat → Nat) (hf : ∀ S, stepK K M S = f S) :
    ∀ n S, growIt K M n S = Nat.repeat f n S
  | 0, _ => rfl
  | n + 1, S => by
    have e : growIt K M (n + 1) S = nextK (growIt K M n) S (stepK K M S) := rfl
    rw [e, nextK, nif_eq, hf, nbeq_eq]
    by_cases hS : f S = S
    · have hfix : ∀ k, Nat.repeat f k S = S := by
        intro k
        induction k with
        | zero => rfl
        | succ k ih =>
          change f (Nat.repeat f k S) = S
          rw [ih, hS]
      rw [if_pos (by simp [hS]), hfix]
    · rw [if_neg (by simpa using hS), growIt_eq K M f hf n (f S), repeat_comm]
      rfl

theorem growCK_eq {m : Fin 6} {K : KT} {fx hx fx' hx' : Nat} (h : TabsOK m K fx hx fx' hx')
    {PL : List Nat} (hP : planesOK K (3 ^ dim m) PL = true) {c : Nat} (hc : c < 2 ^ nroots m) :
    growCK K PL (3 ^ dim m) c = Chk.growC (tabsK m K) (dim m) (nroots m) c := by
  rw [growCK, growIt_eq K _ _ (stepK_eq h _), Chk.growC, closK_eq h hP hc, h.hr]

theorem recsFrom_sound {K : KT} {PL : List Nat} {W gm R nr : Nat} {skip : Bool} {c : Nat} :
    ∀ (L : List (Nat × List Nat)) (j : Nat), recsFrom K PL W gm R nr skip c L j = true →
      j + L.length = K.r ∧ ∀ i (hi : i < L.length), recK K PL W gm R nr skip c (j + i) L[i] = true
  | [], j, hL => by
    refine ⟨?_, fun i hi => absurd hi (Nat.not_lt_zero i)⟩
    have e : recsFrom K PL W gm R nr skip c [] j = Nat.beq j K.r := rfl
    rw [e, Nat.beq_eq] at hL
    simpa using hL
  | yw :: L, j, hL => by
    have e : recsFrom K PL W gm R nr skip c (yw :: L) j =
        band (recK K PL W gm R nr skip c j yw) (recsFrom K PL W gm R nr skip c L (Nat.succ j)) := rfl
    rw [e, band_eq_true] at hL
    obtain ⟨h1, h2⟩ := recsFrom_sound L (Nat.succ j) hL.2
    refine ⟨by simp only [List.length_cons]; omega, fun i hi => ?_⟩
    rcases i with _ | i
    · simpa using hL.1
    · have := h2 i (by simpa using hi)
      rw [show j + (i + 1) = Nat.succ j + i by omega]
      simpa using this

theorem recK_sound {K : KT} {PL : List Nat} {W gm R nr : Nat} {skip : Bool} {c j : Nat}
    {yw : Nat × List Nat} (h : recK K PL W gm R nr skip c j yw = true) :
    (skip = true ∧ (c.testBit j = true ∨ adjK K j &&& c = 0)) ∨
      (yw.1 < nr ∧ (∀ u ∈ yw.2, gm.testBit u = true) ∧ c ||| 1 <<< j < 2 ^ K.r ∧
        growCK K PL W (c ||| 1 <<< j) = wordK K yw.2 (ln128 R yw.1)) := by
  obtain ⟨y, w⟩ := yw
  have e : recK K PL W gm R nr skip c j (y, w) =
      bor (band skip (bor (bit c j) (Nat.beq (Nat.land (adjK K j) c) 0)))
        (band (Nat.blt y nr) <| band (gensW gm w) <|
          band (Nat.blt (Nat.lor c (Nat.shiftLeft 1 j)) (Nat.shiftLeft 1 K.r))
            (Nat.beq (growCK K PL W (Nat.lor c (Nat.shiftLeft 1 j))) (wordK K w (ln128 R y)))) := rfl
  rw [e, bor_iff] at h
  rcases h with h | h
  · rw [band_eq_true, bor_iff, bit_eq, Nat.beq_eq] at h
    exact Or.inl ⟨h.1, h.2⟩
  · simp only [band_eq_true, Nat.blt_eq, Nat.beq_eq] at h
    obtain ⟨hy, hw, hlt, hg⟩ := h
    refine Or.inr ⟨hy, ?_, ?_, hg⟩
    · clear hg hlt e
      induction w with
      | nil => simp
      | cons u w ih =>
        have e2 : gensW gm (u :: w) = band (bit gm u) (gensW gm w) := rfl
        rw [e2, band_eq_true, bit_eq] at hw
        intro v hv
        rcases List.mem_cons.mp hv with rfl | hv
        · exact hw.1
        · exact ih hw.2 v hv
    · have e3 : Nat.shiftLeft 1 K.r = 2 ^ K.r := by
        change 1 <<< K.r = _
        rw [Nat.shiftLeft_eq, Nat.one_mul]
      rw [e3] at hlt
      exact hlt

theorem recsK_sound {K : KT} {PL : List Nat} {W gm R nr : Nat} {skip : Bool} {c : Nat}
    {L : List (Nat × List Nat)} (h : recsK K PL W gm R nr skip c L = true) {j : Nat} (hj : j < K.r) :
    (skip = true ∧ (c.testBit j = true ∨ adjK K j &&& c = 0)) ∨
      ∃ y < nr, ∃ w : List Nat, (∀ u ∈ w, gm.testBit u = true) ∧ c ||| 1 <<< j < 2 ^ K.r ∧
        growCK K PL W (c ||| 1 <<< j) = wordK K w (ln128 R y) := by
  obtain ⟨hlen, hall⟩ := recsFrom_sound L 0 h
  have hj' : j < L.length := by omega
  have := recK_sound (by simpa using hall j hj')
  rcases this with h1 | ⟨hy, hw, hlt, hg⟩
  · exact Or.inl h1
  · exact Or.inr ⟨_, hy, _, hw, hlt, hg⟩

theorem repsOK_sound {R nr r : Nat} (h : repsOK R nr r = true) {x : Nat} (hx : x < nr) :
    ln128 R x < 2 ^ r := by
  have := allN_iff.mp h x hx
  have e3 : Nat.shiftLeft 1 r = 2 ^ r := by
    change 1 <<< r = _
    rw [Nat.shiftLeft_eq, Nat.one_mul]
  rw [Nat.blt_eq, e3] at this
  exact this

theorem foldr_pmap {m : Fin 6} (T : Chk.Tabs) (w : List Nat) (hw : ∀ u ∈ w, u < nroots m) (c : Nat) :
    (w.pmap (fun u hu => (⟨u, hu⟩ : Root m)) hw).foldr
      (fun u acc => Chk.imgN T (nroots m) u.val acc) c =
      w.foldr (fun u acc => Chk.imgN T (nroots m) u acc) c := by
  induction w with
  | nil => rfl
  | cons u w ih =>
    simp only [List.pmap, List.foldr_cons]
    rw [ih]

theorem growth_of_recsK {m : Fin 6} {K : KT} {fx hx fx' hx' : Nat} (h : TabsOK m K fx hx fx' hx')
    {PL : List Nat} (hP : planesOK K (3 ^ dim m) PL = true) {gm ng R nr : Nat}
    (hgm : gm = 2 ^ ng - 1) (hng : ng ≤ nroots m) {skip : Bool} {c : Nat}
    {L : List (Nat × List Nat)} (hL : recsK K PL (3 ^ dim m) gm R nr skip c L = true) (j : Root m)
    (hskip : skip = true → c.testBit j.val = false ∧ (tabsK m K).adj[j.val]! &&& c ≠ 0) :
    ∃ y < nr, ∃ w : List (Root m), (∀ u ∈ w, u.val < ng) ∧
      Chk.growC (tabsK m K) (dim m) (nroots m) (c ||| 1 <<< j.val) =
        w.foldr (fun u acc => Chk.imgN (tabsK m K) (nroots m) u.val acc) (ln128 R y) := by
  have hj : j.val < K.r := by rw [h.hr]; exact j.isLt
  rcases recsK_sound hL hj with ⟨hs, hb⟩ | ⟨y, hy, w, hw, hlt, hg⟩
  · obtain ⟨h1, h2⟩ := hskip hs
    rw [tabsK_adj j.isLt] at h2
    rcases hb with hb | hb
    · rw [h1] at hb
      exact absurd hb Bool.false_ne_true
    · exact absurd hb h2
  · have hw' : ∀ u ∈ w, u < ng := fun u hu => by
      have := hw u hu
      rw [hgm, Nat.testBit_two_pow_sub_one] at this
      exact of_decide_eq_true this
    have hwr : ∀ u ∈ w, u < nroots m := fun u hu => lt_of_lt_of_le (hw' u hu) hng
    rw [h.hr] at hlt
    refine ⟨y, hy, w.pmap (fun u hu => (⟨u, hu⟩ : Root m)) hwr, ?_, ?_⟩
    · intro u hu
      obtain ⟨v, hv, rfl⟩ := List.mem_pmap.mp hu
      exact hw' v hv
    · rw [foldr_pmap, ← growCK_eq h hP hlt, hg, wordK_eq h w hwr]

theorem forall_lt_zero (P : Nat → Prop) : ∀ x < 0, P x := fun x hx => absurd hx (Nat.not_lt_zero x)

theorem forall_lt_succ {P : Nat → Prop} {n : Nat} (h : ∀ x < n, P x) (hn : P n) :
    ∀ x < n + 1, P x := fun x hx => by
  rcases Nat.lt_succ_iff_lt_or_eq.mp hx with hx | rfl
  · exact h x hx
  · exact hn

theorem hGrow_of {m : Fin 6} {K : KT} {fx hx fx' hx' : Nat} (h : TabsOK m K fx hx fx' hx')
    {PL : List Nat} {W : Nat} (hW : W = 3 ^ dim m) (hP : planesOK K W PL = true) {gm ng R nr n : Nat}
    (hgm : gm = 2 ^ ng - 1) (hng : ng ≤ nroots m) (hnr : nr = n) {c : Nat}
    {L : List (Nat × List Nat)} (hL : recsK K PL W gm R nr true c L = true) :
    ∀ j : Root m, c.testBit j.val = false → (tabsK m K).adj[j.val]! &&& c ≠ 0 →
      ∃ y : Fin n, ∃ w : List (Root m), (∀ u ∈ w, u.val < ng) ∧
        Chk.growC (tabsK m K) (dim m) (nroots m) (c ||| 1 <<< j.val) =
          w.foldr (fun u acc => Chk.imgN (tabsK m K) (nroots m) u.val acc) (ln128 R y.val) := by
  subst hW hnr
  intro j h1 h2
  obtain ⟨y, hy, w, hw, he⟩ := growth_of_recsK h hP hgm hng hL j fun _ => ⟨h1, h2⟩
  exact ⟨⟨y, hy⟩, w, hw, he⟩

theorem hSeed_of {m : Fin 6} {K : KT} {fx hx fx' hx' : Nat} (h : TabsOK m K fx hx fx' hx')
    {PL : List Nat} {W : Nat} (hW : W = 3 ^ dim m) (hP : planesOK K W PL = true) {gm ng R nr n : Nat}
    (hgm : gm = 2 ^ ng - 1) (hng : ng ≤ nroots m) (hnr : nr = n)
    {L : List (Nat × List Nat)} (hL : recsK K PL W gm R nr false 0 L = true) :
    ∀ i : Root m, ∃ y : Fin n, ∃ w : List (Root m), (∀ u ∈ w, u.val < ng) ∧
      Chk.growC (tabsK m K) (dim m) (nroots m) (1 <<< i.val) =
        w.foldr (fun u acc => Chk.imgN (tabsK m K) (nroots m) u.val acc) (ln128 R y.val) := by
  subst hW hnr
  intro i
  obtain ⟨y, hy, w, hw, he⟩ := growth_of_recsK h hP hgm hng hL i fun h => absurd h Bool.false_ne_true
  rw [Nat.zero_or] at he
  exact ⟨⟨y, hy⟩, w, hw, he⟩

end CFSG.ExcInsK

end

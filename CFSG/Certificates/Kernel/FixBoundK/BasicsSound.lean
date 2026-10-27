module

public import CFSG.Certificates.Kernel.FixBoundK.FixSpan
public import CFSG.Sporadic.Schreier.J4SSylowBase

public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.KC.FixBoundK

open CFSG.Monster CFSG.Monster.Code CFSG.Monster.Lifts CFSG.Monster.VisQuot
  CFSG.Quasithin.H.Mathieu

theorem add_eq_xor_of_and (a b : Nat) (h : a &&& b = 0) : a + b = a ^^^ b := by
  induction a using Nat.strong_induction_on generalizing b with
  | _ a ih =>
  rcases Nat.eq_zero_or_pos a with rfl | ha
  · simp
  have h2 : a / 2 &&& b / 2 = 0 := by
    apply Nat.eq_of_testBit_eq
    intro i
    have := congrArg (fun x => Nat.testBit x (i + 1)) h
    simpa only [Nat.testBit_and, Nat.testBit_div_two, Nat.zero_testBit] using this
  have h0 : ¬ (a % 2 = 1 ∧ b % 2 = 1) := by
    intro hab
    have := congrArg (fun x => Nat.testBit x 0) h
    simp [Nat.testBit_and, hab.1, hab.2] at this
  have hlt : a % 2 + b % 2 < 2 ^ 1 := by
    rw [Nat.pow_one]
    omega
  have e : a + b = 2 ^ 1 * (a / 2 ^^^ b / 2) + (a % 2 + b % 2) := by
    rw [← ih (a / 2) (by omega) (b / 2) h2, Nat.pow_one]
    omega
  apply Nat.eq_of_testBit_eq
  intro i
  rw [e, Nat.testBit_two_pow_mul_add _ hlt]
  rcases i with _ | i
  · rw [if_pos Nat.zero_lt_one, Nat.testBit_zero, Nat.testBit_xor, Nat.testBit_zero,
      Nat.testBit_zero]
    rcases Nat.mod_two_eq_zero_or_one a with ha2 | ha2 <;>
      rcases Nat.mod_two_eq_zero_or_one b with hb2 | hb2 <;> simp [ha2, hb2]
  · rw [if_neg (by omega), Nat.add_sub_cancel, Nat.testBit_xor, Nat.testBit_xor,
      Nat.testBit_div_two, Nat.testBit_div_two]

theorem testBit_mul_iff (x : Nat) : ∀ y : Nat,
    (∀ i j i' j', x.testBit i = true → y.testBit j = true → x.testBit i' = true →
      y.testBit j' = true → i + j = i' + j' → j = j') →
    ∀ n, (x * y).testBit n = true ↔ ∃ j ≤ n, y.testBit j = true ∧ x.testBit (n - j) = true := by
  intro y
  induction y using Nat.strong_induction_on with
  | _ y ih =>
  intro hu
  rcases Nat.eq_zero_or_pos y with rfl | hy
  · intro n
    simp
  have hu' : ∀ i j i' j', x.testBit i = true → (y / 2).testBit j = true → x.testBit i' = true →
      (y / 2).testBit j' = true → i + j = i' + j' → j = j' := by
    intro i j i' j' hi hj hi' hj' e
    rw [Nat.testBit_div_two] at hj hj'
    have := hu i (j + 1) i' (j' + 1) hi hj hi' hj' (by omega)
    omega
  have ih' := ih (y / 2) (by omega) hu'
  have e : x * y = x * (y % 2) + 2 * (x * (y / 2)) := by
    conv_lhs => rw [← Nat.div_add_mod y 2]
    ring
  have h2 : ∀ z n, (2 * z).testBit n = (decide (n ≥ 1) && z.testBit (n - 1)) := fun z n => by
    have := Nat.testBit_two_pow_mul (i := 1) (a := z) (j := n)
    rwa [Nat.pow_one] at this
  have hshift : ∀ n, (∃ j ≤ n, y.testBit j = true ∧ x.testBit (n - j) = true ∧ 1 ≤ j) ↔
      (2 * (x * (y / 2))).testBit n = true := by
    intro n
    rw [h2, Bool.and_eq_true, decide_eq_true_iff, ih']
    constructor
    · rintro ⟨j, hjn, hj, hx, hj1⟩
      refine ⟨by omega, j - 1, by omega, ?_, ?_⟩
      · rw [Nat.testBit_div_two, Nat.sub_add_cancel hj1]
        exact hj
      · have e1 : n - 1 - (j - 1) = n - j := by omega
        rw [e1]
        exact hx
    · rintro ⟨hn, j, hjn, hj, hx⟩
      refine ⟨j + 1, by omega, ?_, ?_, by omega⟩
      · rw [← Nat.testBit_div_two]
        exact hj
      · have e1 : n - (j + 1) = n - 1 - j := by omega
        rw [e1]
        exact hx
  intro n
  rcases Nat.mod_two_eq_zero_or_one y with h0 | h1
  · rw [e, h0, Nat.mul_zero, Nat.zero_add, ← hshift]
    constructor
    · rintro ⟨j, hjn, hj, hx, _⟩
      exact ⟨j, hjn, hj, hx⟩
    · rintro ⟨j, hjn, hj, hx⟩
      refine ⟨j, hjn, hj, hx, ?_⟩
      rcases j with _ | j
      · rw [Nat.testBit_zero, h0] at hj
        simp at hj
      · omega
  · have hy0 : y.testBit 0 = true := by
      rw [Nat.testBit_zero, h1]
      rfl
    have hdis : ∀ n, ¬ (x.testBit n = true ∧ (2 * (x * (y / 2))).testBit n = true) := by
      rintro n ⟨hx, hz⟩
      obtain ⟨j, hjn, hj, hxj, hj1⟩ := (hshift n).2 hz
      have := hu n 0 (n - j) j hx hy0 hxj hj (by omega)
      omega
    have hand : x &&& 2 * (x * (y / 2)) = 0 := by
      apply Nat.eq_of_testBit_eq
      intro k
      by_contra hne
      rw [Nat.zero_testBit, Bool.not_eq_false, Nat.testBit_and, Bool.and_eq_true] at hne
      exact hdis k hne
    rw [e, h1, Nat.mul_one, add_eq_xor_of_and _ _ hand, Nat.testBit_xor]
    constructor
    · intro hxor
      cases hxn : x.testBit n
      · rw [hxn, Bool.false_xor] at hxor
        obtain ⟨j, hjn, hj, hxj, _⟩ := (hshift n).2 hxor
        exact ⟨j, hjn, hj, hxj⟩
      · exact ⟨0, Nat.zero_le n, hy0, by rw [Nat.sub_zero]; exact hxn⟩
    · rintro ⟨j, hjn, hj, hxj⟩
      rcases j with _ | j
      · rw [Nat.sub_zero] at hxj
        have hz : (2 * (x * (y / 2))).testBit n = false := by
          cases hz : (2 * (x * (y / 2))).testBit n
          · rfl
          · exact absurd ⟨hxj, hz⟩ (hdis n)
        rw [hxj, hz]
        rfl
      · have hz := (hshift n).1 ⟨j + 1, hjn, hj, hxj, by omega⟩
        have hxn : x.testBit n = false := by
          cases hxn : x.testBit n
          · rfl
          · exact absurd ⟨hxn, hz⟩ (hdis n)
        rw [hxn, hz]
        rfl

theorem grid_inj {W a b c d : Nat} (hc : c < W) (hd : d < W) (h : a * W + c = b * W + d) :
    a = b ∧ c = d := by
  have hW : 0 < W := by omega
  have h1 : (c + a * W) / W = (d + b * W) / W := by rw [Nat.add_comm c, Nat.add_comm d, h]
  rw [Nat.add_mul_div_right _ _ hW, Nat.add_mul_div_right _ _ hW, Nat.div_eq_of_lt hc,
    Nat.div_eq_of_lt hd, Nat.zero_add, Nat.zero_add] at h1
  subst h1
  exact ⟨rfl, Nat.add_left_cancel h⟩

theorem grid2_inj {m W b j k b' j' k' : Nat} (hW : W = m * m) (hj : j < m) (hk : k < m)
    (hj' : j' < m) (hk' : k' < m) (h : b * W + (m * j + k) = b' * W + (m * j' + k')) :
    b = b' ∧ j = j' ∧ k = k' := by
  have hlt : ∀ j k, j < m → k < m → m * j + k < W := fun j k hj hk => by
    rw [hW]
    calc m * j + k < m * j + m := by omega
      _ = m * (j + 1) := by ring
      _ ≤ m * m := Nat.mul_le_mul_left _ hj
  obtain ⟨rfl, h2⟩ := grid_inj (hlt j k hj hk) (hlt j' k' hj' hk') h
  have h3 : j * m + k = j' * m + k' := by
    rw [Nat.mul_comm j, Nat.mul_comm j']
    exact h2
  obtain ⟨rfl, rfl⟩ := grid_inj hk hk' h3
  exact ⟨rfl, rfl, rfl⟩

theorem lt_two_pow_of_testBit {x B : Nat} (h : ∀ p, x.testBit p = true → p < B) : x < 2 ^ B :=
  Nat.lt_pow_two_of_testBit x fun i hi => by
    cases hx : x.testBit i
    · rfl
    · exact absurd (h i hx) (by omega)

theorem testBit_iff_shr (k t : Nat) : k.testBit t = true ↔ (k >>> t) % 2 = 1 := by
  have := Nat.testBit_shiftRight (i := t) (j := 0) k
  rw [Nat.add_zero] at this
  rw [← this, Nat.testBit_zero, decide_eq_true_iff]

theorem dblS_zero (x w : Nat) : dblS x w 0 = x := rfl

theorem dblS_succ (x w n : Nat) : dblS x w (n + 1) = dblS (x ||| x <<< w) (2 * w) n := by
  have e : Nat.shiftLeft w 1 = 2 * w := by
    change w <<< 1 = 2 * w
    rw [Nat.shiftLeft_eq, Nat.pow_one, Nat.mul_comm]
  change dblS (x ||| x <<< w) (Nat.shiftLeft w 1) n = _
  rw [e]

theorem testBit_dblS : ∀ (n x w : Nat), x < 2 ^ w → ∀ p,
    (dblS x w n).testBit p = true ↔ ∃ i < 2 ^ n, ∃ r < w, x.testBit r = true ∧ p = w * i + r
  | 0, x, w, hx, p => by
    rw [dblS_zero]
    constructor
    · intro hp
      have hpw : p < w := by
        by_contra hpw
        rw [Nat.testBit_lt_two_pow (lt_of_lt_of_le hx
          (Nat.pow_le_pow_right (by norm_num) (by omega)))] at hp
        exact absurd hp (by simp)
      exact ⟨0, by norm_num, p, hpw, hp, by ring⟩
    · rintro ⟨i, hi, r, _, hr, rfl⟩
      have : i = 0 := by simpa using hi
      subst this
      simpa using hr
  | n + 1, x, w, hx, p => by
    have hx' : x ||| x <<< w < 2 ^ (2 * w) := by
      apply Nat.or_lt_two_pow
      · exact lt_of_lt_of_le hx (Nat.pow_le_pow_right (by norm_num) (by omega))
      · rw [Nat.shiftLeft_eq, two_mul, Nat.pow_add]
        exact Nat.mul_lt_mul_of_pos_right hx (Nat.two_pow_pos w)
    have hxw : ∀ r, w ≤ r → x.testBit r = false := fun r hr =>
      Nat.testBit_lt_two_pow (lt_of_lt_of_le hx (Nat.pow_le_pow_right (by norm_num) hr))
    rw [dblS_succ, testBit_dblS n _ _ hx' p]
    constructor
    · rintro ⟨i, hi, r, hr, hxr, rfl⟩
      rw [Nat.testBit_or, Nat.testBit_shiftLeft, Bool.or_eq_true, Bool.and_eq_true,
        decide_eq_true_iff] at hxr
      rcases hxr with hxr | ⟨hwr, hxr⟩
      · have hrw : r < w := by
          by_contra h
          rw [hxw r (by omega)] at hxr
          exact absurd hxr (by simp)
        exact ⟨2 * i, by rw [Nat.pow_succ]; omega, r, hrw, hxr, by ring⟩
      · refine ⟨2 * i + 1, by rw [Nat.pow_succ]; omega, r - w, by omega, hxr, ?_⟩
        have e : r = w + (r - w) := by omega
        conv_lhs => rw [e]
        ring
    · rintro ⟨i, hi, r, hr, hxr, rfl⟩
      rcases Nat.even_or_odd' i with ⟨i', rfl | rfl⟩
      · refine ⟨i', by rw [Nat.pow_succ] at hi; omega, r, by omega, ?_, by ring⟩
        rw [Nat.testBit_or, hxr, Bool.true_or]
      · refine ⟨i', by rw [Nat.pow_succ] at hi; omega, r + w, by omega, ?_, by ring⟩
        rw [Nat.testBit_or, Nat.testBit_shiftLeft, Nat.add_sub_cancel, hxr]
        simp

theorem genD_eq (K t w : Nat) : genD K t w =
    dblS (dblS 1 w t <<< (w * 2 ^ t)) (w * 2 ^ (t + 1)) (K - (t + 1)) := rfl

theorem testBit_genD {K t w : Nat} (ht : t < K) (hw : 0 < w) (p : Nat) :
    (genD K t w).testBit p = true ↔ ∃ q < 2 ^ K, q.testBit t = true ∧ p = w * q := by
  have h1 : 1 < 2 ^ w := Nat.one_lt_two_pow (by omega)
  have hI : ∀ p, (dblS 1 w t).testBit p = true ↔ ∃ i < 2 ^ t, p = w * i := by
    intro p
    rw [testBit_dblS t 1 w h1 p]
    constructor
    · rintro ⟨i, hi, r, _, hr, rfl⟩
      rw [Nat.testBit_one_eq_true_iff_self_eq_zero] at hr
      exact ⟨i, hi, by rw [hr, Nat.add_zero]⟩
    · rintro ⟨i, hi, rfl⟩
      exact ⟨i, hi, 0, hw, Nat.testBit_one_zero, by rw [Nat.add_zero]⟩
  have hX : ∀ p, (dblS 1 w t <<< (w * 2 ^ t)).testBit p = true ↔
      ∃ i < 2 ^ t, p = w * (2 ^ t + i) := by
    intro p
    rw [Nat.testBit_shiftLeft, Bool.and_eq_true, decide_eq_true_iff, hI]
    constructor
    · rintro ⟨hp, i, hi, he⟩
      refine ⟨i, hi, ?_⟩
      rw [Nat.mul_add, ← he]
      omega
    · rintro ⟨i, hi, rfl⟩
      refine ⟨by rw [Nat.mul_add]; omega, i, hi, by rw [Nat.mul_add]; omega⟩
  have hXlt : dblS 1 w t <<< (w * 2 ^ t) < 2 ^ (w * 2 ^ (t + 1)) := by
    apply lt_two_pow_of_testBit
    intro p hp
    obtain ⟨i, hi, rfl⟩ := (hX p).1 hp
    apply Nat.mul_lt_mul_of_pos_left _ hw
    rw [Nat.pow_succ]
    omega
  rw [genD_eq, testBit_dblS _ _ _ hXlt p]
  constructor
  · rintro ⟨i', hi', r, hr, hXr, rfl⟩
    obtain ⟨i, hi, rfl⟩ := (hX r).1 hXr
    refine ⟨2 ^ (t + 1) * i' + 2 ^ t + i, ?_, ?_, by ring⟩
    · have hK : 2 ^ K = 2 ^ (t + 1) * 2 ^ (K - (t + 1)) := by
        rw [← Nat.pow_add, Nat.add_sub_cancel' ht]
      rw [hK]
      calc 2 ^ (t + 1) * i' + 2 ^ t + i < 2 ^ (t + 1) * i' + 2 ^ (t + 1) := by
            rw [Nat.pow_succ]; omega
        _ = 2 ^ (t + 1) * (i' + 1) := by ring
        _ ≤ _ := Nat.mul_le_mul_left _ hi'
    · have e : 2 ^ (t + 1) * i' + 2 ^ t + i = 2 ^ t * (2 * i' + 1) + i := by ring
      rw [e, Nat.testBit_two_pow_mul_add _ hi, if_neg (Nat.lt_irrefl t), Nat.sub_self,
        Nat.testBit_zero]
      simp
  · rintro ⟨q, hq, hqt, rfl⟩
    refine ⟨q / 2 ^ (t + 1), ?_, w * (q % 2 ^ (t + 1)), ?_, ?_, ?_⟩
    · rw [Nat.div_lt_iff_lt_mul (Nat.two_pow_pos _), ← Nat.pow_add, Nat.sub_add_cancel ht]
      exact hq
    · exact Nat.mul_lt_mul_of_pos_left (Nat.mod_lt _ (Nat.two_pow_pos _)) hw
    · rw [hX]
      have hge : 2 ^ t ≤ q % 2 ^ (t + 1) := by
        by_contra hlt
        have := Nat.testBit_lt_two_pow (Nat.lt_of_not_le hlt)
        rw [Nat.testBit_mod_two_pow, hqt] at this
        simp at this
      refine ⟨q % 2 ^ (t + 1) - 2 ^ t, ?_, by rw [Nat.add_sub_cancel' hge]⟩
      have := Nat.mod_lt q (Nat.two_pow_pos (t + 1))
      rw [Nat.pow_succ] at this
      omega
    · conv_lhs => rw [← Nat.div_add_mod q (2 ^ (t + 1))]
      ring

@[expose] def sprL (W : Nat) (l : List Nat) (s : Nat) : Nat :=
  List.rec (motive := fun _ => Nat → Nat) (fun _ => nat_lit 0)
    (fun b _ ih s => Nat.lor (nIf(bitS s, Nat.shiftLeft (nat_lit 1) (Nat.mul b W), nat_lit 0))
      (ih (Nat.shiftRight s (nat_lit 1))))
    l s

theorem idx12_eq : idx12 = List.range' 0 12 := by decide

theorem idx12_mem {b : Nat} : b ∈ idx12 ↔ b < 12 := by
  rw [idx12_eq, List.mem_range'_1]
  omega

theorem sprS_eq (s W : Nat) : sprS s W = sprL W idx12 s := rfl

theorem sprL_cons (W b : Nat) (l : List Nat) (s : Nat) :
    sprL W (b :: l) s = (if s % 2 = 1 then 2 ^ (b * W) else 0) ||| sprL W l (s / 2) := by
  change Nat.lor (nIf(bitS s, Nat.shiftLeft 1 (Nat.mul b W), 0)) (sprL W l (Nat.shiftRight s 1)) = _
  rw [nIf_eq, bitS_eq, shiftRight_one]
  simp only [decide_eq_true_eq]
  change (if s % 2 = 1 then 1 <<< (b * W) else 0) ||| _ = _
  rw [Nat.one_shiftLeft]

theorem testBit_sprL (W : Nat) : ∀ (n b₀ s p : Nat),
    (sprL W (List.range' b₀ n) s).testBit p = true ↔
      ∃ b < n, s.testBit b = true ∧ p = (b₀ + b) * W
  | 0, b₀, s, p => by
    change (0 : Nat).testBit p = true ↔ _
    simp
  | n + 1, b₀, s, p => by
    rw [List.range'_succ, sprL_cons, Nat.testBit_or, Bool.or_eq_true,
      testBit_sprL W n (b₀ + 1) (s / 2) p]
    constructor
    · rintro (h | ⟨b, hb, hs, rfl⟩)
      · split_ifs at h with hs
        · rw [Nat.testBit_two_pow, decide_eq_true_iff] at h
          refine ⟨0, by omega, ?_, by rw [Nat.add_zero, h]⟩
          rw [Nat.testBit_zero, hs]
          rfl
        · simp at h
      · refine ⟨b + 1, by omega, ?_, by ring⟩
        rw [← Nat.testBit_div_two]
        exact hs
    · rintro ⟨b, hb, hs, rfl⟩
      rcases b with _ | b
      · left
        rw [Nat.testBit_zero, decide_eq_true_iff] at hs
        rw [if_pos hs, Nat.testBit_two_pow, Nat.add_zero]
        simp
      · right
        refine ⟨b, by omega, ?_, by ring⟩
        rw [Nat.testBit_div_two]
        exact hs

theorem testBit_sprS (s W p : Nat) :
    (sprS s W).testBit p = true ↔ ∃ b < 12, s.testBit b = true ∧ p = b * W := by
  rw [sprS_eq, idx12_eq, testBit_sprL]
  simp only [Nat.zero_add]

theorem actS_nil (x : Nat) : actS [] x = 0 := rfl

theorem actS_cons (c : Nat) (cs : List Nat) (x : Nat) :
    actS (c :: cs) x = (if x % 2 = 1 then c else 0) ^^^ actS cs (x / 2) := by
  rw [actS_eq, actS_eq, actM]

theorem map_actS {f : Nat → Nat} (h0 : f 0 = 0) (hx : ∀ a b, f (a ^^^ b) = f a ^^^ f b) :
    ∀ (L : List Nat) (k : Nat), f (actS L k) = actS (L.map f) k
  | [], _ => h0
  | c :: L, k => by
    rw [actS_cons, hx, map_actS h0 hx L, List.map_cons, actS_cons]
    congr 1
    by_cases hk : k % 2 = 1 <;> simp [hk, h0]

theorem synS_zero : synS 0 = 0 := actS_zero synK

theorem synS_xor (a b : Nat) : synS (a ^^^ b) = synS a ^^^ synS b := actS_xor synK a b

theorem actS_map_and_right (c : Nat) (L : List Nat) (k : Nat) :
    actS (L.map fun a => synS (a &&& c)) k = synS (actS L k &&& c) :=
  (map_actS (f := fun a => synS (a &&& c)) (by simp only [Nat.zero_and, synS_zero])
    (fun a b => by simp only [Nat.and_xor_distrib_right, synS_xor]) L k).symm

theorem actS_map_and_left (a : Nat) (L : List Nat) (j : Nat) :
    actS (L.map fun c => synS (a &&& c)) j = synS (a &&& actS L j) :=
  (map_actS (f := fun c => synS (a &&& c)) (by simp only [Nat.and_zero, synS_zero])
    (fun b c => by simp only [Nat.and_xor_distrib_left, synS_xor]) L j).symm

theorem testBit_rowTerm {K W t s : Nat} (ht : t < K) (hKW : 2 ^ K ≤ W) (p : Nat) :
    (genD K t 1 * sprS s W).testBit p = true ↔
      ∃ b < 12, ∃ k < 2 ^ K, p = b * W + k ∧ s.testBit b = true ∧ k.testBit t = true := by
  have huniq : ∀ i j i' j', (genD K t 1).testBit i = true → (sprS s W).testBit j = true →
      (genD K t 1).testBit i' = true → (sprS s W).testBit j' = true → i + j = i' + j' →
      j = j' := by
    intro i j i' j' hi hj hi' hj' e
    obtain ⟨b, _, _, rfl⟩ := (testBit_sprS s W j).1 hj
    obtain ⟨b', _, _, rfl⟩ := (testBit_sprS s W j').1 hj'
    obtain ⟨k, hk, _, rfl⟩ := (testBit_genD ht Nat.one_pos i).1 hi
    obtain ⟨k', hk', _, rfl⟩ := (testBit_genD ht Nat.one_pos i').1 hi'
    obtain ⟨rfl, -⟩ := grid_inj (lt_of_lt_of_le hk hKW) (lt_of_lt_of_le hk' hKW)
      (by omega : b * W + k = b' * W + k')
    rfl
  rw [testBit_mul_iff _ _ huniq]
  constructor
  · rintro ⟨j, hjp, hj, hx⟩
    obtain ⟨b, hb, hsb, rfl⟩ := (testBit_sprS s W j).1 hj
    obtain ⟨k, hk, hkt, hke⟩ := (testBit_genD ht Nat.one_pos _).1 hx
    exact ⟨b, hb, k, hk, by omega, hsb, hkt⟩
  · rintro ⟨b, hb, k, hk, rfl, hsb, hkt⟩
    refine ⟨b * W, by omega, (testBit_sprS s W _).2 ⟨b, hb, hsb, rfl⟩,
      (testBit_genD ht Nat.one_pos _).2 ⟨k, hk, hkt, by omega⟩⟩

theorem rowU_nil (K W c t : Nat) : rowU K W [] c t = 0 := rfl

theorem rowU_cons (K W a c t : Nat) (B : List Nat) :
    rowU K W (a :: B) c t = genD K t 1 * sprS (synS (a &&& c)) W ^^^ rowU K W B c (t + 1) := rfl

theorem rowU_supp {K W c : Nat} (hKW : 2 ^ K ≤ W) : ∀ (B : List Nat) (t₀ : Nat),
    t₀ + B.length ≤ K → ∀ p, (rowU K W B c t₀).testBit p = true →
      ∃ b < 12, ∃ k < 2 ^ K, p = b * W + k
  | [], _, _, p, h => by
    rw [rowU_nil, Nat.zero_testBit] at h
    exact absurd h (by simp)
  | a :: B, t₀, hl, p, h => by
    rw [List.length_cons] at hl
    rw [rowU_cons, Nat.testBit_xor] at h
    cases h1 : (genD K t₀ 1 * sprS (synS (a &&& c)) W).testBit p
    · rw [h1, Bool.false_xor] at h
      exact rowU_supp hKW B (t₀ + 1) (by omega) p h
    · obtain ⟨b, hb, k, hk, e, _⟩ := (testBit_rowTerm (by omega) hKW p).1 h1
      exact ⟨b, hb, k, hk, e⟩

theorem rowU_val {K W c : Nat} (hKW : 2 ^ K ≤ W) : ∀ (B : List Nat) (t₀ : Nat),
    t₀ + B.length ≤ K → ∀ b < 12, ∀ k < 2 ^ K, (rowU K W B c t₀).testBit (b * W + k) =
      (actS (B.map fun a => synS (a &&& c)) (k >>> t₀)).testBit b
  | [], _, _, b, _, k, _ => by simp [rowU_nil, actS_nil]
  | a :: B, t₀, hl, b, hb, k, hk => by
    rw [List.length_cons] at hl
    rw [rowU_cons, Nat.testBit_xor, rowU_val hKW B (t₀ + 1) (by omega) b hb k hk, List.map_cons,
      actS_cons, Nat.testBit_xor, Nat.shiftRight_succ]
    congr 1
    rw [Bool.eq_iff_iff, testBit_rowTerm (by omega) hKW]
    constructor
    · rintro ⟨b', _, k', hk', e, hs, hkt⟩
      obtain ⟨rfl, rfl⟩ := grid_inj (lt_of_lt_of_le hk hKW) (lt_of_lt_of_le hk' hKW) e
      rw [if_pos ((testBit_iff_shr _ _).1 hkt)]
      exact hs
    · intro h
      by_cases hkt : (k >>> t₀) % 2 = 1
      · rw [if_pos hkt] at h
        exact ⟨b, hb, k, hk, rfl, h, (testBit_iff_shr _ _).2 hkt⟩
      · rw [if_neg hkt, Nat.zero_testBit] at h
        exact absurd h (by simp)

theorem testBit_matTerm {K m W u x : Nat} (hu : u < K) (hm : m = 2 ^ K) (hW : W = m * m)
    (hx : ∀ p, x.testBit p = true → ∃ b < 12, ∃ k < m, p = b * W + k) (p : Nat) :
    (x * genD K u m).testBit p = true ↔ ∃ b < 12, ∃ j < m, ∃ k < m,
      p = b * W + (m * j + k) ∧ j.testBit u = true ∧ x.testBit (b * W + k) = true := by
  have hm0 : 0 < m := hm ▸ Nat.two_pow_pos K
  have hg : ∀ p, (genD K u m).testBit p = true ↔ ∃ q < m, q.testBit u = true ∧ p = m * q := by
    intro p
    rw [testBit_genD hu hm0, ← hm]
  have huniq : ∀ i j i' j', x.testBit i = true → (genD K u m).testBit j = true →
      x.testBit i' = true → (genD K u m).testBit j' = true → i + j = i' + j' → j = j' := by
    intro i j i' j' hi hj hi' hj' e
    obtain ⟨q, hq, _, rfl⟩ := (hg j).1 hj
    obtain ⟨q', hq', _, rfl⟩ := (hg j').1 hj'
    obtain ⟨b, _, k, hk, rfl⟩ := hx i hi
    obtain ⟨b', _, k', hk', rfl⟩ := hx i' hi'
    obtain ⟨-, rfl, -⟩ := grid2_inj hW hq hk hq' hk'
      (by omega : b * W + (m * q + k) = b' * W + (m * q' + k'))
    rfl
  rw [testBit_mul_iff x _ huniq]
  constructor
  · rintro ⟨j, hjp, hj, hxj⟩
    obtain ⟨q, hq, hqu, rfl⟩ := (hg j).1 hj
    obtain ⟨b, hb, k, hk, e⟩ := hx _ hxj
    refine ⟨b, hb, q, hq, k, hk, by omega, hqu, ?_⟩
    rw [← e]
    exact hxj
  · rintro ⟨b, hb, j, hj, k, hk, rfl, hju, hxb⟩
    refine ⟨m * j, by omega, (hg _).2 ⟨j, hj, hju, rfl⟩, ?_⟩
    have e : b * W + (m * j + k) - m * j = b * W + k := by omega
    rw [e]
    exact hxb

@[expose] def synL (K m W : Nat) (B l : List Nat) (u₀ : Nat) : Nat :=
  List.rec (motive := fun _ => Nat → Nat) (fun _ => nat_lit 0)
    (fun c _ ih u => Nat.xor (Nat.mul (rowU K W B c (nat_lit 0)) (genD K u m)) (ih (Nat.succ u)))
    l u₀

theorem synMat_eq (K m W : Nat) (B : List Nat) (u₀ : Nat) :
    synMat K m W B u₀ = synL K m W B B u₀ := rfl

theorem synL_nil (K m W : Nat) (B : List Nat) (u : Nat) : synL K m W B [] u = 0 := rfl

theorem synL_cons (K m W : Nat) (B : List Nat) (c : Nat) (l : List Nat) (u : Nat) :
    synL K m W B (c :: l) u = rowU K W B c 0 * genD K u m ^^^ synL K m W B l (u + 1) := rfl

theorem synL_val {K m W : Nat} {B : List Nat} (hB : B.length = K) (hm : m = 2 ^ K)
    (hW : W = m * m) : ∀ (l : List Nat) (u₀ : Nat), u₀ + l.length ≤ K →
    ∀ b < 12, ∀ j < m, ∀ k < m, (synL K m W B l u₀).testBit (b * W + (m * j + k)) =
      (actS (l.map fun c => synS (actS B k &&& c)) (j >>> u₀)).testBit b
  | [], _, _, b, _, j, _, k, _ => by simp [synL_nil, actS_nil]
  | c :: l, u₀, hl, b, hb, j, hj, k, hk => by
    rw [List.length_cons] at hl
    have hm0 : 0 < m := hm ▸ Nat.two_pow_pos K
    have hKW : 2 ^ K ≤ W := by
      rw [hW, ← hm]
      exact Nat.le_mul_of_pos_left m hm0
    rw [synL_cons, Nat.testBit_xor, synL_val hB hm hW l (u₀ + 1) (by omega) b hb j hj k hk,
      List.map_cons, actS_cons, Nat.testBit_xor, Nat.shiftRight_succ]
    congr 1
    have hsupp : ∀ p, (rowU K W B c 0).testBit p = true → ∃ b < 12, ∃ k < m, p = b * W + k := by
      intro p hp
      obtain ⟨b, hb, k, hk, e⟩ := rowU_supp hKW B 0 (by omega) p hp
      exact ⟨b, hb, k, by omega, e⟩
    have hrow : (rowU K W B c 0).testBit (b * W + k) = (synS (actS B k &&& c)).testBit b := by
      rw [rowU_val hKW B 0 (by omega) b hb k (by omega), Nat.shiftRight_zero,
        actS_map_and_right]
    rw [Bool.eq_iff_iff, testBit_matTerm (by omega) hm hW hsupp]
    constructor
    · rintro ⟨b', _, j', hj', k', hk', e, hju, hx⟩
      obtain ⟨rfl, rfl, rfl⟩ := grid2_inj hW hj hk hj' hk' e
      rw [if_pos ((testBit_iff_shr _ _).1 hju), ← hrow]
      exact hx
    · intro h
      by_cases hju : (j >>> u₀) % 2 = 1
      · rw [if_pos hju, ← hrow] at h
        exact ⟨b, hb, j, hj, k, hk, rfl, (testBit_iff_shr _ _).2 hju, h⟩
      · rw [if_neg hju, Nat.zero_testBit] at h
        exact absurd h (by simp)

@[expose] def orL (x W : Nat) (l : List Nat) : Nat :=
  List.rec (motive := fun _ => Nat) (nat_lit 0)
    (fun b _ ih => Nat.lor (Nat.land (Nat.shiftRight x (Nat.mul b W))
      (Nat.sub (Nat.shiftLeft (nat_lit 1) W) (nat_lit 1))) ih)
    l

theorem orLanes_eq (x W : Nat) : orLanes x W = orL x W idx12 := rfl

theorem testBit_orL (x W i : Nat) (hi : i < W) : ∀ l : List Nat,
    (orL x W l).testBit i = true ↔ ∃ b ∈ l, x.testBit (b * W + i) = true
  | [] => by
    change (0 : Nat).testBit i = true ↔ _
    simp
  | b :: l => by
    change (((x >>> (b * W)) &&& (1 <<< W - 1)) ||| orL x W l).testBit i = true ↔ _
    rw [Nat.testBit_or, Bool.or_eq_true, Nat.testBit_and, Nat.one_shiftLeft,
      Nat.testBit_two_pow_sub_one, Nat.testBit_shiftRight, testBit_orL x W i hi l]
    simp [hi]

theorem packS_nil (m j : Nat) : packS [] m j = 0 := rfl

theorem packS_cons (b : Nat) (bs : List Nat) (m j : Nat) :
    packS (b :: bs) m j = b <<< (m * j) ||| packS bs m (j + 1) := rfl

theorem packS_low {m : Nat} : ∀ (bs : List Nat) (j₀ p : Nat), p < m * j₀ →
    (packS bs m j₀).testBit p = false
  | [], _, p, _ => by rw [packS_nil, Nat.zero_testBit]
  | b :: bs, j₀, p, hp => by
    rw [packS_cons, Nat.testBit_or, Nat.testBit_shiftLeft,
      packS_low bs (j₀ + 1) p (lt_of_lt_of_le hp (Nat.mul_le_mul_left _ (Nat.le_succ _))),
      Bool.or_false]
    have : ¬ p ≥ m * j₀ := by omega
    simp [this]

theorem packS_val {m : Nat} : ∀ (bs : List Nat), (∀ b ∈ bs, b < 2 ^ m) → ∀ (j₀ j k : Nat),
    j < bs.length → k < m → (packS bs m j₀).testBit (m * (j₀ + j) + k) = (bs.getD j 0).testBit k
  | [], _, _, _, _, hj, _ => absurd hj (Nat.not_lt_zero _)
  | b :: bs, hbs, j₀, j, k, hj, hk => by
    rw [packS_cons, Nat.testBit_or, Nat.testBit_shiftLeft]
    rcases j with _ | j
    · have hlow : m * (j₀ + 0) + k < m * (j₀ + 1) := by
        rw [Nat.add_zero, Nat.mul_succ]
        omega
      rw [packS_low bs (j₀ + 1) _ hlow, Bool.or_false, List.getD_cons_zero]
      have e : m * (j₀ + 0) + k - m * j₀ = k := by simp
      simp [e]
    · rw [List.getD_cons_succ]
      have e : m * (j₀ + (j + 1)) + k = m * (j₀ + 1 + j) + k := by ring_nf
      rw [e, packS_val bs (fun b hb => hbs b (List.mem_cons_of_mem _ hb)) (j₀ + 1) j k
        (by simpa using hj) hk]
      have hge : m ≤ m * (j₀ + 1 + j) + k - m * j₀ := by
        have : m * (j₀ + 1 + j) = m * j₀ + m + m * j := by ring
        omega
      rw [Nat.testBit_lt_two_pow (lt_of_lt_of_le (hbs b List.mem_cons_self)
        (Nat.pow_le_pow_right (by norm_num) hge)), Bool.and_false, Bool.false_or]

theorem synS_lt (x : Nat) : synS x < 2 ^ 12 := by
  rw [synS, actS_eq]
  exact actM_lt (by decide +kernel) x

theorem synS_ne_zero_iff (x : Nat) : synS x ≠ 0 ↔ ∃ b < 12, (synS x).testBit b = true := by
  constructor
  · intro h
    by_contra hne
    apply h
    apply Nat.eq_of_testBit_eq
    intro i
    rw [Nat.zero_testBit]
    by_cases hi : i < 12
    · cases hb : (synS x).testBit i
      · rfl
      · exact absurd ⟨i, hi, hb⟩ hne
    · exact Nat.testBit_lt_two_pow (lt_of_lt_of_le (synS_lt x)
        (Nat.pow_le_pow_right (by norm_num) (by omega)))
  · rintro ⟨b, _, hb⟩ h
    rw [h, Nat.zero_testBit] at hb
    exact absurd hb (by simp)

theorem basicsOK_bit {B bs : List Nat} (h : basicsOK B bs = true) :
    bs.length = 2 ^ B.length ∧ ∀ j < 2 ^ B.length, ∀ k, (bs.getD j 0).testBit k = true ↔
      k < 2 ^ B.length ∧ bvec 24 (actS B k) * bvec 24 (actS B j) ∈ C := by
  have e : basicsOK B bs =
      basicsW B bs B.length (2 ^ B.length) (2 ^ B.length * 2 ^ B.length) := by
    simp only [basicsOK, withN_eq, TrivSound.lenS_eq]
    rfl
  rw [e] at h
  set K := B.length with hK
  set m := 2 ^ K with hm
  set W := m * m with hW
  simp only [basicsW, TrivSound.bAnd_eq, Bool.and_eq_true, withN_eq] at h
  obtain ⟨h1, h2, h3⟩ := h
  have hlen : bs.length = m := by
    rw [← TrivSound.lenS_eq]
    exact (beqT _ _).1 h1
  have hbs : ∀ b ∈ bs, b < 2 ^ m := by
    intro b hb
    have h2b := (beqT _ _).1 ((TrivSound.allS_iff _ bs).1 h2 b hb)
    have e2 : b &&& (2 ^ m - 1) = b := by
      rw [← Nat.one_shiftLeft]
      exact h2b
    rw [Nat.and_two_pow_sub_one_eq_mod] at e2
    rw [← e2]
    exact Nat.mod_lt _ (Nat.two_pow_pos m)
  have hcmp : packS bs m 0 ^^^ orLanes (synMat K m W B 0) W = 2 ^ W - 1 := by
    rw [← Nat.one_shiftLeft]
    exact (beqT _ _).1 h3
  refine ⟨hlen, fun j hj k => ?_⟩
  have hjl : j < bs.length := by
    rw [hlen]
    exact hj
  have hbj : bs.getD j 0 < 2 ^ m :=
    hbs _ (by rw [List.getD_eq_getElem _ _ hjl]; exact List.getElem_mem hjl)
  by_cases hk : k < m
  swap
  · refine iff_of_false ?_ fun h => hk h.1
    rw [Nat.testBit_lt_two_pow (lt_of_lt_of_le hbj (Nat.pow_le_pow_right (by norm_num)
      (by omega)))]
    simp
  have hi : m * j + k < W := by
    rw [hW]
    calc m * j + k < m * j + m := by omega
      _ = m * (j + 1) := by ring
      _ ≤ m * m := Nat.mul_le_mul_left _ hj
  have hc := congrArg (fun x => x.testBit (m * j + k)) hcmp
  simp only [Nat.testBit_xor, Nat.testBit_two_pow_sub_one, decide_eq_true hi] at hc
  have hp := packS_val bs hbs 0 j k hjl hk
  rw [Nat.zero_add] at hp
  rw [hp] at hc
  have ho : (orLanes (synMat K m W B 0) W).testBit (m * j + k) = true ↔
      synS (actS B k &&& actS B j) ≠ 0 := by
    rw [orLanes_eq, testBit_orL _ _ _ hi, synS_ne_zero_iff]
    constructor
    · rintro ⟨b, hb, hx⟩
      rw [idx12_mem] at hb
      rw [synMat_eq, synL_val hK.symm hm hW B 0 (by omega) b hb j hj k hk, Nat.shiftRight_zero,
        actS_map_and_left] at hx
      exact ⟨b, hb, hx⟩
    · rintro ⟨b, hb, hx⟩
      refine ⟨b, idx12_mem.2 hb, ?_⟩
      rw [synMat_eq, synL_val hK.symm hm hW B 0 (by omega) b hb j hj k hk, Nat.shiftRight_zero,
        actS_map_and_left]
      exact hx
  have key : ∀ a c : Bool, (a ^^ c) = true → (a = true ↔ ¬ c = true) := by decide
  rw [key _ _ hc, ho, not_not, ← bvec_and, ← synS_eq_zero_iff, and_iff_right hk]

end CFSG.KC.FixBoundK

end

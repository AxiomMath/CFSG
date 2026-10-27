module

public import CFSG.Certificates.Kernel.YModel.SchSem
public import CFSG.YGroups.Exact.Model
public import Mathlib.Data.LawfulXor.Basic
public import Mathlib.Order.CompletePartialOrder
public import Mathlib.Tactic.Monotonicity.Lemmas
public import Mathlib.Topology.Sheaves.Presheaf
public import Std.Tactic.BVDecide.Normalize.BitVec

public section

namespace CFSG.KC.YModel.Sch

open CFSG.KC CFSG.KC.MonsterConv.Perm CFSG.KC.Loop CFSG.KC.Benes CFSG.KC.YModel CFSG.KC.YModel.Sem

noncomputable def cnt (X b q : Nat) : Nat :=
  ∑ r ∈ Finset.range (2 ^ b), (X.testBit (q * 2 ^ b + r)).toNat

theorem cnt_lt (X b q : Nat) : cnt X b q < 2 ^ 2 ^ b := by
  have : cnt X b q ≤ 2 ^ b := by
    unfold cnt
    calc _ ≤ ∑ _r ∈ Finset.range (2 ^ b), 1 := Finset.sum_le_sum fun r _ => Bool.toNat_le _
      _ = 2 ^ b := by simp
  exact lt_of_le_of_lt this Nat.lt_two_pow_self

theorem cnt_succ (X b q : Nat) : cnt X (b + 1) q = cnt X b (2 * q) + cnt X b (2 * q + 1) := by
  unfold cnt
  rw [pow_succ, mul_two, Finset.sum_range_add]
  congr 1
  · apply Finset.sum_congr rfl
    intro r _
    congr 2
    ring
  · apply Finset.sum_congr rfl
    intro r _
    congr 2
    ring

noncomputable def bsum (s : Nat) (c : Nat → Nat) (Q : Nat) : Nat :=
  ∑ q ∈ Finset.range Q, c q * 2 ^ (q * s)

theorem split_blk {s p Q : Nat} (hs : 0 < s) (hp : Q * s ≤ p) (hp2 : p < (Q + 1) * s) :
    p / s = Q ∧ p % s = p - Q * s := by
  obtain ⟨r, rfl⟩ : ∃ r, p = Q * s + r := ⟨p - Q * s, by omega⟩
  have hr : r < s := by rw [Nat.succ_mul] at hp2; omega
  rw [Nat.add_comm, Nat.mul_comm, Nat.add_mul_div_left _ _ hs, Nat.div_eq_of_lt hr, Nat.zero_add,
    Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hr]
  omega

theorem testBit_bsum {s : Nat} {c : Nat → Nat} (hs : 0 < s) (hc : ∀ q, c q < 2 ^ s) : ∀ Q,
    (∀ p, (bsum s c Q).testBit p = (decide (p < Q * s) && (c (p / s)).testBit (p % s))) ∧
      bsum s c Q < 2 ^ (Q * s)
  | 0 => ⟨fun p => by simp [bsum], by simp [bsum]⟩
  | Q + 1 => by
    obtain ⟨ih1, ih2⟩ := testBit_bsum hs hc Q
    have e : bsum s c (Q + 1) = 2 ^ (Q * s) * c Q + bsum s c Q := by
      unfold bsum
      rw [Finset.sum_range_succ, Nat.add_comm, Nat.mul_comm]
    refine ⟨fun p => ?_, ?_⟩
    · rw [e, Nat.testBit_two_pow_mul_add _ ih2]
      by_cases h1 : p < Q * s
      · rw [if_pos h1, ih1, decide_eq_true h1, decide_eq_true (by rw [Nat.succ_mul]; omega)]
      · rw [if_neg h1]
        by_cases h2 : p < (Q + 1) * s
        · obtain ⟨d1, d2⟩ := split_blk hs (by omega) h2
          rw [decide_eq_true h2, Bool.true_and, d1, d2]
        · rw [decide_eq_false h2, Bool.false_and, Nat.testBit_lt_two_pow
            (lt_two_pow_mono (hc Q) (by rw [Nat.succ_mul] at h2; omega))]
    · rw [e]
      have h3 : (c Q + 1) * 2 ^ (Q * s) ≤ 2 ^ s * 2 ^ (Q * s) :=
        Nat.mul_le_mul_right _ (hc Q)
      rw [Nat.succ_mul, ← Nat.pow_add] at h3
      rw [show (Q + 1) * s = s + Q * s by rw [Nat.succ_mul, Nat.add_comm], Nat.mul_comm]
      omega

noncomputable def Sb (k X b : Nat) : Nat := bsum (2 ^ b) (cnt X b) (2 ^ (k - b))

theorem testBit_Sb (k X b p : Nat) :
    (Sb k X b).testBit p = (decide (p < 2 ^ (k - b) * 2 ^ b) &&
      (cnt X b (p / 2 ^ b)).testBit (p % 2 ^ b)) :=
  (testBit_bsum (Nat.two_pow_pos b) (cnt_lt X b) _).1 p

theorem testBit_eq_parity {p b : Nat} : p.testBit b = decide (p / 2 ^ b % 2 = 1) :=
  Nat.testBit_eq_decide_div_mod_eq

theorem lt_blk {Q q r m : Nat} (hr : r < m) : q * m + r < Q * m ↔ q < Q := by
  constructor
  · intro h
    by_contra hc
    have : Q * m ≤ q * m := Nat.mul_le_mul_right _ (by omega)
    omega
  · intro h
    have : (q + 1) * m ≤ Q * m := Nat.mul_le_mul_right _ h
    rw [Nat.succ_mul] at this
    omega

theorem step_eq {k X b a : Nat} (hb : b < k)
    (ha : ∀ p < 2 ^ k, a.testBit p = (Sb k X b).testBit p) :
    Nat.add (Nat.land a (Nat.xor (ones (wid k)) (idPlane (wid k) b)))
      (Nat.land (Nat.shiftRight a (Nat.shiftLeft 1 b)) (Nat.xor (ones (wid k)) (idPlane (wid k) b))) =
      Sb k X (b + 1) := by
  rw [wid_eq, shl1, nadd]
  simp only [nland, nxor, nshr]
  set s := 2 ^ b with hs
  have hs0 : 0 < s := Nat.two_pow_pos b
  have hQ : 2 ^ (k - b) = 2 * 2 ^ (k - (b + 1)) := by
    rw [← Nat.pow_succ']
    congr 1
    omega
  have hW1 : 2 ^ k = 2 ^ (k - (b + 1)) * (2 * s) := by
    rw [hs, ← Nat.pow_succ', ← Nat.pow_add]
    congr 1
    omega
  have hW0 : 2 ^ (k - b) * s = 2 ^ (k - (b + 1)) * (2 * s) := by
    rw [hQ]
    ring
  set Q := 2 ^ (k - (b + 1))
  have hmsk : ∀ p, (ones (2 ^ k) ^^^ idPlane (2 ^ k) b).testBit p =
      (decide (p < 2 ^ k) && !p.testBit b) := by
    intro p
    rw [Nat.testBit_xor, testBit_ones', idPlane_testBit hb]
    cases decide (p < 2 ^ k) <;> cases p.testBit b <;> rfl
  have hc2 : ∀ q, cnt X b (2 * q) < 2 ^ (2 * s) := fun q =>
    lt_two_pow_mono (cnt_lt X b _) (by omega)
  have hc3 : ∀ q, cnt X b (2 * q + 1) < 2 ^ (2 * s) := fun q =>
    lt_two_pow_mono (cnt_lt X b _) (by omega)
  have hA := (testBit_bsum (by omega : 0 < 2 * s) hc2 Q).1
  have hB := (testBit_bsum (by omega : 0 < 2 * s) hc3 Q).1
  have hS : Sb k X (b + 1) = bsum (2 * s) (fun q => cnt X b (2 * q)) Q +
      bsum (2 * s) (fun q => cnt X b (2 * q + 1)) Q := by
    unfold Sb bsum
    rw [← Finset.sum_add_distrib, show 2 ^ (b + 1) = 2 * s by rw [hs, Nat.pow_succ, Nat.mul_comm]]
    apply Finset.sum_congr rfl
    intro q _
    rw [cnt_succ, Nat.add_mul]
  rw [hS]
  have dec : ∀ p, ∃ q r, p = q * (2 * s) + r ∧ r < 2 * s := fun p =>
    ⟨p / (2 * s), p % (2 * s), (Nat.div_add_mod' p (2 * s)).symm, Nat.mod_lt _ (by omega)⟩
  have dv : ∀ q r, r < 2 * s → (q * (2 * s) + r) / (2 * s) = q ∧ (q * (2 * s) + r) % (2 * s) = r :=
    fun q r hr => by
      rw [Nat.add_comm, Nat.mul_comm, Nat.add_mul_div_left _ _ (by omega), Nat.div_eq_of_lt hr,
        Nat.zero_add, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hr]
      exact ⟨rfl, rfl⟩
  have ds : ∀ q r, (q * (2 * s) + r) / s = 2 * q + r / s ∧ (q * (2 * s) + r) % s = r % s :=
    fun q r => by
      rw [show q * (2 * s) + r = r + s * (2 * q) by ring, Nat.add_mul_div_left _ _ hs0,
        Nat.add_mul_mod_self_left]
      exact ⟨by ring, rfl⟩
  congr 1
  ·
    apply Nat.eq_of_testBit_eq
    intro p
    obtain ⟨q, r, rfl, hr⟩ := dec p
    have e1 := (dv q r hr).1
    have e2 := (dv q r hr).2
    have e3 := (ds q r).1
    have e4 := (ds q r).2
    rw [Nat.testBit_and, hmsk, hA]
    beta_reduce
    rw [e1, e2, testBit_eq_parity (p := q * (2 * s) + r) (b := b), ← hs, e3]
    by_cases hp : q * (2 * s) + r < 2 ^ k
    · have hp' : q * (2 * s) + r < 2 ^ (k - b) * s := by rw [hW0, ← hW1]; exact hp
      have hp'' : q * (2 * s) + r < Q * (2 * s) := by rw [← hW1]; exact hp
      rw [ha _ hp, testBit_Sb, ← hs, e3, e4]
      simp only [decide_eq_true hp, decide_eq_true hp', decide_eq_true hp'', Bool.true_and]
      by_cases hrs : r < s
      · have h0 : r / s = 0 := Nat.div_eq_of_lt hrs
        have h5 : (2 * q + 0) % 2 = 0 := by omega
        rw [h0, Nat.mod_eq_of_lt hrs, h5, Nat.add_zero]
        simp
      · have h1 : r / s = 1 := Nat.div_eq_of_lt_le (by omega) (by omega)
        have h5 : (2 * q + 1) % 2 = 1 := by omega
        rw [h1, h5, Nat.testBit_lt_two_pow (lt_two_pow_mono (cnt_lt X b (2 * q)) (by omega : s ≤ r))]
        simp
    · have hp'' : ¬ q * (2 * s) + r < Q * (2 * s) := by rw [← hW1]; exact hp
      simp [hp, hp'']
  ·
    apply Nat.eq_of_testBit_eq
    intro p
    obtain ⟨q, r, rfl, hr⟩ := dec p
    have e1 := (dv q r hr).1
    have e2 := (dv q r hr).2
    have e3 := (ds q r).1
    rw [Nat.testBit_and, hmsk, hB]
    beta_reduce
    rw [e1, e2, testBit_eq_parity (p := q * (2 * s) + r) (b := b), ← hs, e3, Nat.testBit_shiftRight]
    by_cases hp : q * (2 * s) + r < 2 ^ k
    · have hp'' : q * (2 * s) + r < Q * (2 * s) := by rw [← hW1]; exact hp
      simp only [decide_eq_true hp, decide_eq_true hp'', Bool.true_and]
      by_cases hrs : r < s
      · have hq : q < Q := (lt_blk hr).1 hp''
        have e5 : s + (q * (2 * s) + r) = q * (2 * s) + (r + s) := by ring
        have hp2 : q * (2 * s) + (r + s) < 2 ^ k := by
          rw [hW1]
          exact (lt_blk (by omega)).2 hq
        have hp3 : q * (2 * s) + (r + s) < 2 ^ (k - b) * s := by rw [hW0, ← hW1]; exact hp2
        have h0 : r / s = 0 := Nat.div_eq_of_lt hrs
        have h1 : (r + s) / s = 1 := by rw [Nat.add_div_right _ hs0, h0]
        have h2 : (r + s) % s = r := by rw [Nat.add_mod_right, Nat.mod_eq_of_lt hrs]
        have h5 : (2 * q + 0) % 2 = 0 := by omega
        rw [e5, ha _ hp2, testBit_Sb, ← hs, (ds q (r + s)).1, (ds q (r + s)).2, decide_eq_true hp3,
          h1, h2, h0, h5]
        simp
      · have h1 : r / s = 1 := Nat.div_eq_of_lt_le (by omega) (by omega)
        have h5 : (2 * q + 1) % 2 = 1 := by omega
        rw [h1, h5, Nat.testBit_lt_two_pow
          (lt_two_pow_mono (cnt_lt X b (2 * q + 1)) (by omega : s ≤ r))]
        simp
    · have hp'' : ¬ q * (2 * s) + r < Q * (2 * s) := by rw [← hW1]; exact hp
      simp [hp, hp'']

noncomputable def pIter (k X b : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) X
    (fun b acc => strictN acc (fun a =>
      (fun s msk => Nat.add (Nat.land a msk) (Nat.land (Nat.shiftRight a s) msk))
        (Nat.shiftLeft (nat_lit 1) b) (Nat.xor (ones (wid k)) (idPlane (wid k) b)))) b

theorem pIter_succ (k X b : Nat) : pIter k X (b + 1) =
    Nat.add (Nat.land (pIter k X b) (Nat.xor (ones (wid k)) (idPlane (wid k) b)))
      (Nat.land (Nat.shiftRight (pIter k X b) (Nat.shiftLeft 1 b))
        (Nat.xor (ones (wid k)) (idPlane (wid k) b))) := by
  show strictN (pIter k X b) (fun a =>
      (fun s msk => Nat.add (Nat.land a msk) (Nat.land (Nat.shiftRight a s) msk))
        (Nat.shiftLeft (nat_lit 1) b) (Nat.xor (ones (wid k)) (idPlane (wid k) b))) = _
  rw [Benes.strictN_eq]

theorem Sb_zero_bits (k X p : Nat) (hp : p < 2 ^ k) : X.testBit p = (Sb k X 0).testBit p := by
  rw [testBit_Sb, Nat.pow_zero, Nat.mul_one, Nat.sub_zero, decide_eq_true hp, Bool.true_and,
    Nat.div_one, Nat.mod_one]
  unfold cnt
  simp only [Nat.pow_zero, Finset.range_one, Finset.sum_singleton, Nat.mul_one, Nat.add_zero]
  cases X.testBit p <;> rfl

theorem popc_eq (k X : Nat) (hX : X < 2 ^ 2 ^ k) :
    popc k X = ∑ r ∈ Finset.range (2 ^ k), (X.testBit r).toNat := by
  have key : ∀ b, 1 ≤ b → b ≤ k → pIter k X b = Sb k X b := by
    intro b
    induction b with
    | zero => intro h; omega
    | succ b ih =>
      intro _ hb
      rw [pIter_succ]
      apply step_eq (by omega)
      intro p hp
      rcases Nat.eq_zero_or_pos b with rfl | hb1
      · exact Sb_zero_bits k X p hp
      · rw [ih hb1 (by omega)]
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · change X = _
    simp only [Nat.pow_zero, Finset.range_one, Finset.sum_singleton]
    have : X < 2 := by simpa using hX
    interval_cases X <;> rfl
  · change pIter k X k = _
    rw [key k hk le_rfl]
    unfold Sb bsum cnt
    simp

theorem ptsRec_testBit (TT : Nat → Nat) (r : Nat) : ∀ Z,
    (Nat.rec (motive := fun _ => Nat) 0 (fun a acc => strictN acc
      (fun s => Nat.lor s (Nat.shiftLeft (nat_lit 1) (ptX (TT a))))) Z).testBit r = true ↔
      ∃ a < Z, ptX (TT a) = r
  | 0 => by
    change Nat.testBit 0 r = true ↔ _
    simp
  | Z + 1 => by
    change (strictN (Nat.rec (motive := fun _ => Nat) 0 (fun a acc => strictN acc
      (fun s => Nat.lor s (Nat.shiftLeft (nat_lit 1) (ptX (TT a))))) Z)
        (fun s => Nat.lor s (Nat.shiftLeft (nat_lit 1) (ptX (TT Z))))).testBit r = true ↔ _
    rw [Benes.strictN_eq, nlor, nshl, Nat.testBit_or, Bool.or_eq_true, ptsRec_testBit TT r Z, Nat.one_shiftLeft,
      Nat.testBit_two_pow, decide_eq_true_eq]
    constructor
    · rintro (⟨a, ha, h⟩ | h)
      · exact ⟨a, by omega, h⟩
      · exact ⟨Z, by omega, h⟩
    · rintro ⟨a, ha, h⟩
      rcases Nat.lt_succ_iff_lt_or_eq.1 ha with ha | rfl
      · exact Or.inl ⟨a, ha, h⟩
      · exact Or.inr h

theorem points_inj {k Z : Nat} {TT : Nat → Nat} (h : pointsOK k TT Z = true)
    (hx : ∀ a < Z, ptX (TT a) < 2 ^ k) :
    ∀ a < Z, ∀ a' < Z, ptX (TT a) = ptX (TT a') → a = a' := by
  classical
  unfold pointsOK at h
  have e := Nat.eq_of_beq_eq_true h
  set X := Nat.rec (motive := fun _ => Nat) 0 (fun a acc => strictN acc
      (fun s => Nat.lor s (Nat.shiftLeft (nat_lit 1) (ptX (TT a))))) Z with hXd
  have hb : ∀ r, X.testBit r = true ↔ ∃ a < Z, ptX (TT a) = r := fun r => ptsRec_testBit TT r Z
  have hX : X < 2 ^ 2 ^ k := Nat.lt_pow_two_of_testBit _ fun r hr => by
    cases hc : X.testBit r
    · rfl
    · obtain ⟨a, ha, h⟩ := (hb r).1 hc
      have := hx a ha
      omega
  rw [popc_eq k X hX] at e
  have hsum : ∑ r ∈ Finset.range (2 ^ k), (X.testBit r).toNat =
      ((Finset.range (2 ^ k)).filter fun r => X.testBit r = true).card := by
    rw [Finset.card_filter]
    apply Finset.sum_congr rfl
    intro r _
    cases X.testBit r <;> rfl
  have himg : ((Finset.range (2 ^ k)).filter fun r => X.testBit r = true) =
      (Finset.range Z).image fun a => ptX (TT a) := by
    ext r
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_image, hb]
    constructor
    · rintro ⟨_, a, ha, h⟩
      exact ⟨a, ha, h⟩
    · rintro ⟨a, ha, h⟩
      exact ⟨h ▸ hx a ha, a, ha, h⟩
  rw [hsum, himg] at e
  have hinj := Finset.card_image_iff.1 (e.trans (Finset.card_range Z).symm)
  intro a ha a' ha' he
  exact hinj (Finset.mem_coe.2 (Finset.mem_range.2 ha)) (Finset.mem_coe.2 (Finset.mem_range.2 ha')) he

theorem genOK_spec {k w lo hi j b : Nat} {fix : Bool} {U WP WL : Nat → Nat}
    (h : genOK k w U WP WL lo hi j b fix = true) :
    StagesValid k (U j) ∧ codesIn w lo hi (WP j) (WL j) = true ∧
      wordNet k (wordNets k w U (WP j) (WL j)) (U j) = true ∧
      (fix = true → netApply k (wid k) 1 (U j) (Nat.shiftLeft 1 b) = Nat.shiftLeft 1 b) := by
  unfold genOK at h
  obtain ⟨h1, h⟩ := andB_eq h
  obtain ⟨h2, h⟩ := andB_eq h
  obtain ⟨h3, h4⟩ := andB_eq h
  refine ⟨stagesValid_of_ymodel h1, h2, h3, fun hf => ?_⟩
  subst hf
  exact Nat.eq_of_beq_eq_true h4

theorem gen_good {k n w lo hi j b : Nat} {fix : Bool} {U WP WL : Nat → Nat} (hn : n ≤ 2 ^ k)
    (h : genOK k w U WP WL lo hi j b fix = true) (hg : CodesGood k n U (codesL w (WP j) (WL j))) :
    Good k n (U j) ∧ netPerm k n (U j) = cpermL k n U (codesL w (WP j) (WL j)) ∧
      (fix = true → ∀ hb : b < n, netPerm k n (U j) ⟨b, hb⟩ = ⟨b, hb⟩) := by
  obtain ⟨hv, -, hw, hf⟩ := genOK_spec h
  have g1 := good_wordNets hg
  have e := Nat.eq_of_beq_eq_true hw
  rw [shl1] at e
  have hc := eq_of_idP (acts_netsApply _ fun N hN => (g1 N hN).2.1) (acts_netApply hv) e
  have hG : Good k n (U j) := ⟨hn, hv, fun i h1 h2 => by
    rw [← hc i h2, compN_fix _ g1 i h1 h2]⟩
  refine ⟨hG, ?_, fun hfix hb => ?_⟩
  · rw [← prod_wordNets hg]
    ext i
    rw [netPerm_apply hG, prod_apply _ g1, hc i (by have := i.2; omega)]
  · have e2 := hf hfix
    rw [wid_eq] at e2
    have e3 : netApply k (2 ^ k) (repU (2 ^ k) 1) (U j) (Nat.shiftLeft 1 b) = Nat.shiftLeft 1 b := by
      rw [← repU_one' k]
      exact e2
    have := eq_of_point (acts_netApply (P := 1) hv) (by omega) e3
    apply Fin.ext
    rw [netPerm_apply hG]
    exact this

theorem transOK_spec {k w b lo hi a : Nat} {U TT : Nat → Nat}
    (h : transOK k w U TT b lo hi a 1 = true) :
    codesIn w lo hi (ptP (TT a)) (ptL (TT a)) = true ∧
      mapsTo k w U (ptP (TT a)) (ptL (TT a)) b (ptX (TT a)) = true := by
  change andB (andB (codesIn w lo hi (ptP (TT a)) (ptL (TT a)))
    (mapsTo k w U (ptP (TT a)) (ptL (TT a)) b (ptX (TT a)))) true = true at h
  exact andB_eq (andB_eq h).1

theorem recOK_spec {k w Z hi top a j rec : Nat} {U TT : Nat → Nat}
    (h : recOK k w U TT Z hi top a j rec = true) :
    ptX rec < Z ∧
      ((ptP (TT (ptX rec)) = catW w (2 * (j + 1)) 1 (ptP (TT a)) ∧
          ptL (TT (ptX rec)) = ptL (TT a) + 1) ∨
        (codesIn w hi top (ptP rec) (ptL rec) = true ∧
          sweqK k w U (catW w (catW w (invW w (ptP (TT (ptX rec))) (ptL (TT (ptX rec))))
              (ptL (TT (ptX rec))) (2 * (j + 1))) (ptL (TT (ptX rec)) + 1) (ptP (TT a)))
            (ptL (TT (ptX rec)) + 1 + ptL (TT a)) (ptP rec) (ptL rec) = true)) := by
  unfold recOK at h
  obtain ⟨h1, h⟩ := andB_eq h
  refine ⟨Nat.blt_eq.mp h1, ?_⟩
  cases hl : Nat.beq (ptL rec) 65535
  · rw [hl] at h
    dsimp only at h
    obtain ⟨h2, h3⟩ := andB_eq h
    exact Or.inr ⟨h2, h3⟩
  · rw [hl] at h
    dsimp only at h
    obtain ⟨h2, h3⟩ := andB_eq h
    exact Or.inl ⟨Nat.eq_of_beq_eq_true h2, Nat.eq_of_beq_eq_true h3⟩

theorem shr1_eq (x : Nat) : x >>> 1 = x / 2 := by rw [Nat.shiftRight_eq_div_pow, Nat.pow_one]

theorem codes_idx {w lo hi P len : Nat} (h : codesIn w lo hi P len = true) :
    ∀ x ∈ codesL w P len, lo ≤ (x >>> 1) - 1 ∧ (x >>> 1) - 1 < hi ∧
      2 * ((x >>> 1) - 1 + 1) < 2 ^ w := by
  intro x hx
  obtain ⟨h1, h2⟩ := codesIn_spec len P h x hx
  have h3 := mem_codesL_lt hx
  rw [shr1_eq] at h1 h2 ⊢
  refine ⟨by omega, by omega, ?_⟩
  have : 2 * (x / 2) ≤ x := Nat.mul_div_le x 2
  omega

theorem codesL_one {w x : Nat} (hx : x < 2 ^ w) : codesL w x 1 = [x] := by
  unfold codesL
  simp only [List.range_one, List.map_cons, List.map_nil]
  rw [fieldAt_eq', Nat.mul_zero, Nat.shiftRight_zero, Nat.mod_eq_of_lt hx]

theorem cperm_gen {k n j : Nat} {U : Nat → Nat} : cperm k n U (2 * (j + 1)) = netPerm k n (U j) := by
  unfold cperm
  have h1 : (2 * (j + 1)).testBit 0 = false := by
    rw [Nat.testBit_zero]
    simp
  have h2 : (2 * (j + 1)) >>> 1 - 1 = j := by rw [shr1_eq]; omega
  rw [h1, h2]
  rfl

theorem cpermL_gen {k n w j : Nat} {U : Nat → Nat} (hj : 2 * (j + 1) < 2 ^ w) :
    cpermL k n U (codesL w (2 * (j + 1)) 1) = netPerm k n (U j) := by
  rw [codesL_one hj, cpermL, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one,
    cperm_gen]

theorem catW_lt {w P1 L1 P2 : Nat} (h1 : P1 < 2 ^ (w * L1)) (h2 : P2 < 2 ^ w) :
    catW w P1 L1 P2 < 2 ^ (w * (L1 + 1)) := by
  unfold catW
  rw [nlor, nshl, nmul]
  apply Nat.or_lt_two_pow (lt_two_pow_mono h1 (by rw [Nat.mul_succ]; omega))
  rw [Nat.shiftLeft_eq, Nat.mul_succ, Nat.pow_add, Nat.mul_comm (2 ^ (w * L1))]
  exact Nat.mul_lt_mul_of_pos_right h2 (Nat.two_pow_pos _)

theorem xor1_shr (x : Nat) : (x ^^^ 1) >>> 1 = x >>> 1 := by
  rw [Nat.shiftRight_xor_distrib]
  simp

theorem card_level {n : Nat} {S : Set (Equiv.Perm (Fin n))} {H' : Subgroup (Equiv.Perm (Fin n))}
    {b : Fin n} {Z : Nat} {τ : Nat → Equiv.Perm (Fin n)}
    (h1 : ∀ a < Z, τ a ∈ Subgroup.closure S)
    (h2 : ∀ a < Z, ∀ a' < Z, τ a b = τ a' b → a = a')
    (h3 : H' ≤ Subgroup.closure S) (h3' : ∀ g ∈ H', g b = b)
    (h4 : ∀ s ∈ S, ∀ a < Z, ∃ y < Z, (τ y)⁻¹ * s * τ a ∈ H') (hZ : 0 < Z) :
    Nat.card (Subgroup.closure S) = Z * Nat.card H' := by
  classical
  set Hc := Subgroup.closure S
  let φ : Fin Z × H' → Hc := fun p => ⟨τ p.1 * p.2, Hc.mul_mem (h1 _ p.1.2) (h3 p.2.2)⟩
  have hinj : Function.Injective φ := by
    rintro ⟨a, g⟩ ⟨a', g'⟩ he
    have he' : τ a * g = τ a' * g' := congrArg Subtype.val he
    have hb : τ a b = τ a' b := by
      have := congrArg (fun f : Equiv.Perm (Fin n) => f b) he'
      simp only [Equiv.Perm.mul_apply, h3' g g.2, h3' g' g'.2] at this
      exact this
    have ha : a = a' := Fin.ext (h2 a a.2 a' a'.2 hb)
    subst ha
    have : (g : Equiv.Perm (Fin n)) = g' := mul_left_cancel he'
    rw [Subtype.ext this]
  have key : ∀ g ∈ Hc, ∀ a < Z, ∀ h ∈ H', ∃ a' < Z, ∃ h' ∈ H', g * (τ a * h) = τ a' * h' := by
    intro g hg
    induction hg using Subgroup.closure_induction with
    | mem s hs =>
      intro a ha h hh
      obtain ⟨y, hy, hv⟩ := h4 s hs a ha
      exact ⟨y, hy, (τ y)⁻¹ * s * τ a * h, H'.mul_mem hv hh, by group⟩
    | one =>
      intro a ha h hh
      exact ⟨a, ha, h, hh, one_mul _⟩
    | mul g1 g2 _ _ ih1 ih2 =>
      intro a ha h hh
      obtain ⟨a2, ha2, h2', hh2, e2⟩ := ih2 a ha h hh
      obtain ⟨a1, ha1, h1', hh1, e1⟩ := ih1 a2 ha2 h2' hh2
      exact ⟨a1, ha1, h1', hh1, by rw [mul_assoc, e2, e1]⟩
    | inv g _ ih =>
      have hpow : ∀ m : Nat, ∀ a < Z, ∀ h ∈ H', ∃ a' < Z, ∃ h' ∈ H', g ^ m * (τ a * h) = τ a' * h' := by
        intro m
        induction m with
        | zero =>
          intro a ha h hh
          exact ⟨a, ha, h, hh, by rw [pow_zero, one_mul]⟩
        | succ m ihm =>
          intro a ha h hh
          obtain ⟨a2, ha2, h2', hh2, e2⟩ := ihm a ha h hh
          obtain ⟨a1, ha1, h1', hh1, e1⟩ := ih a2 ha2 h2' hh2
          exact ⟨a1, ha1, h1', hh1, by rw [pow_succ', mul_assoc, e2, e1]⟩
      have hord : g⁻¹ = g ^ (orderOf g - 1) := by
        apply inv_eq_of_mul_eq_one_right
        rw [← pow_succ', Nat.sub_add_cancel (orderOf_pos g), pow_orderOf_eq_one]
      intro a ha h hh
      rw [hord]
      exact hpow _ a ha h hh
  have hsurj : Function.Surjective φ := by
    rintro ⟨g, hg⟩
    obtain ⟨a', ha', h', hh', e⟩ := key (g * (τ 0)⁻¹) (Hc.mul_mem hg (Hc.inv_mem (h1 0 hZ))) 0 hZ 1
      H'.one_mem
    refine ⟨(⟨a', ha'⟩, ⟨h', hh'⟩), Subtype.ext ?_⟩
    change τ a' * h' = g
    rw [← e]
    group
  rw [← Nat.card_eq_of_bijective φ ⟨hinj, hsurj⟩, Nat.card_prod, Nat.card_eq_fintype_card (α := Fin Z),
    Fintype.card_fin]

theorem off_le {t : Nat} {off : Nat → Nat} (hmono : ∀ i < t, off i ≤ off (i + 1)) :
    ∀ i i', i ≤ i' → i' ≤ t → off i ≤ off i' := by
  intro i i' h1 h2
  induction i', h1 using Nat.le_induction with
  | base => exact le_rfl
  | succ i' h ih => exact (ih (by omega)).trans (hmono i' (by omega))

theorem level_of {t : Nat} {off : Nat → Nat} {j : Nat} (a : Nat) : ∀ b, a ≤ b → b ≤ t →
    off a ≤ j → j < off b → ∃ i, a ≤ i ∧ i < b ∧ off i ≤ j ∧ j < off (i + 1)
  | 0, h1, _, h3, h4 => by
    have : a = 0 := by omega
    subst this
    omega
  | b + 1, h1, h2, h3, h4 => by
    by_cases h5 : off b ≤ j
    · exact ⟨b, by
        by_contra hc
        have : a = b + 1 := by omega
        subst this
        omega, by omega, h5, h4⟩
    · obtain ⟨i, hi1, hi2, hi3, hi4⟩ := level_of (t := t) a b (by
        by_contra hc
        have : a = b + 1 := by omega
        subst this
        omega) (by omega) h3 (by omega)
      exact ⟨i, hi1, by omega, hi3, hi4⟩

theorem card_sch {k n m w t : Nat} {F Nf U WP WL : Nat → Nat}
    {off bp Z LP LL : Nat → Nat} {TT : Nat → Nat → Nat} {O : Array (Array Nat)}
    (hk : k ≤ 32) (hw : 2 * m < 2 ^ w) (hm : 0 < m)
    (hOs : O.size = m) (hO : ∀ c < m, ∀ i < n, (O[c]!)[i]! = fieldAt 32 (F c) i)
    (h : ∀ c < m, letOK k n (F c) (Nf c) = true) (hU : ∀ c < m, U c = Nf c)
    (hoff : off 0 = m) (hmono : ∀ i < t, off i ≤ off (i + 1))
    (hgen0 : ∀ j, off 0 ≤ j → j < off 1 → genOK k w U WP WL 0 m j 0 false = true)
    (hgen : ∀ i, 0 < i → i < t → ∀ j, off i ≤ j → j < off (i + 1) →
      genOK k w U WP WL (off (i - 1)) (off i) j (bp (i - 1)) true = true)
    (hbp : ∀ i < t, bp i < n) (hb0 : ∀ i < t, ptX (TT i 0) = bp i ∧ 0 < Z i)
    (hpts : ∀ i < t, pointsOK k (TT i) (Z i) = true)
    (htr : ∀ i < t, ∀ a < Z i, transOK k w U (TT i) (bp i) (off i) (off (i + 1)) a 1 = true)
    (hrec : ∀ i < t, ∀ a < Z i, ∀ j, off i ≤ j → j < off (i + 1) →
      ∃ rec, recOK k w U (TT i) (Z i) (off (i + 1)) (off t) a j rec = true)
    (hlet : ∀ c < m, sweqK k w U (2 * (c + 1)) 1 (LP c) (LL c) = true ∧
      codesIn w m (off t) (LP c) (LL c) = true) :
    Nat.card (CFSG.YGroups.arrClosure n O) = ∏ i ∈ Finset.range t, Z i := by
  classical
  have hn : n ≤ 2 ^ k := (letOK_spec hk (h 0 hm)).1
  have hw0 : 0 < w := by
    rcases Nat.eq_zero_or_pos w with rfl | h'
    · simp at hw
      omega
    · exact h'
  have hL : ∀ c < m, Good k n (U c) ∧ netPerm k n (U c) = CFSG.Monster.B.Co2.permOfArr n O[c]! := by
    intro c hc
    obtain ⟨hn', hv, hent, hfix⟩ := letOK_spec hk (h c hc)
    have hg : Good k n (Nf c) := ⟨hn', hv, hfix⟩
    have hrep : CFSG.Monster.B.Co2.Rep n O[c]! (netPerm k n (Nf c)) := fun x => by
      rw [hO c hc x x.2, hent x x.2, ← netPerm_apply hg x]
    have hinv := isInvA_invCand (t := O[c]!) (fun i hi => hrep.lt hi) (fun i hi j hj e => by
      rw [hrep.apply hi, hrep.apply hj] at e
      have := (netPerm k n (Nf c)).injective (Fin.ext e)
      simpa using this)
    rw [hU c hc]
    exact ⟨hg, hrep.unique (CFSG.Monster.B.Co2.rep_permOfArr hinv).1⟩
  have hgood : ∀ i ≤ t, ∀ j < off i, Good k n (U j) := by
    intro i
    induction i with
    | zero =>
      intro _ j hj
      rw [hoff] at hj
      exact (hL j hj).1
    | succ i ih =>
      intro hi j hj
      by_cases hj' : j < off i
      · exact ih (by omega) j hj'
      · have hgo : ∃ lo hi' b fix, genOK k w U WP WL lo hi' j b fix = true ∧ hi' ≤ off i := by
          rcases Nat.eq_zero_or_pos i with rfl | hi0
          · exact ⟨0, m, 0, false, hgen0 j (by omega) hj, by rw [hoff]⟩
          · exact ⟨off (i - 1), off i, bp (i - 1), true,
              hgen i hi0 (by omega) j (by omega) hj, le_rfl⟩
        obtain ⟨lo, hi', b, fix, hg, hle⟩ := hgo
        obtain ⟨-, hc, -, -⟩ := genOK_spec hg
        exact (gen_good hn hg fun x hx => ih (by omega) _ (by
          have := codes_idx hc x hx
          omega)).1
  have hgt : ∀ j < off t, Good k n (U j) := hgood t le_rfl
  have hofft : ∀ i ≤ t, off i ≤ off t := fun i hi => off_le hmono i t hi le_rfl
  let Sg : Nat → Set (Equiv.Perm (Fin n)) := fun i =>
    {g | ∃ j, off i ≤ j ∧ j < off (i + 1) ∧ 2 * (j + 1) < 2 ^ w ∧ netPerm k n (U j) = g}
  let C : Nat → Subgroup (Equiv.Perm (Fin n)) := fun i =>
    if i < t then Subgroup.closure (Sg i) else ⊥
  have hCi : ∀ i < t, C i = Subgroup.closure (Sg i) := fun i hi => if_pos hi
  have hCt : C t = ⊥ := if_neg (lt_irrefl t)
  have hCmono : ∀ i < t, C (i + 1) ≤ C i := by
    intro i hi
    by_cases hi1 : i + 1 < t
    · rw [hCi _ hi1, hCi i hi, Subgroup.closure_le]
      rintro g ⟨j, hj1, hj2, -, rfl⟩
      have hg := hgen (i + 1) (by omega) hi1 j hj1 hj2
      simp only [Nat.add_sub_cancel] at hg
      obtain ⟨-, hc, -, -⟩ := genOK_spec hg
      have hcg : CodesGood k n U (codesL w (WP j) (WL j)) := fun x hx => hgt _ (by
        have := codes_idx hc x hx
        have := hofft (i + 1) (by omega)
        omega)
      rw [(gen_good hn hg hcg).2.1]
      apply cpermL_mem
      intro x hx
      obtain ⟨c1, c2, c3⟩ := codes_idx hc x hx
      exact Subgroup.subset_closure ⟨_, c1, c2, c3, rfl⟩
    · have : i + 1 = t := by omega
      rw [this, hCt]
      exact bot_le
  have hCanti : ∀ i i', i ≤ i' → i' ≤ t → C i' ≤ C i := by
    intro i i' h1 h2
    induction i', h1 using Nat.le_induction with
    | base => exact le_rfl
    | succ i' h ih => exact (hCmono i' (by omega)).trans (ih (by omega))
  have hgenC : ∀ a ≤ t, ∀ j, off a ≤ j → j < off t → 2 * (j + 1) < 2 ^ w →
      netPerm k n (U j) ∈ C a := by
    intro a ha j h1 h2 h3
    obtain ⟨i, hi1, hi2, hi3, hi4⟩ := level_of (t := t) a t ha le_rfl h1 h2
    apply hCanti a i hi1 (by omega)
    rw [hCi i hi2]
    exact Subgroup.subset_closure ⟨j, hi3, hi4, h3, rfl⟩
  have hfixC : ∀ i (hi : i < t), ∀ g ∈ C (i + 1), g ⟨bp i, hbp i hi⟩ = ⟨bp i, hbp i hi⟩ := by
    intro i hi g hg
    by_cases hi1 : i + 1 < t
    · rw [hCi _ hi1] at hg
      have hle : Subgroup.closure (Sg (i + 1)) ≤
          MulAction.stabilizer (Equiv.Perm (Fin n)) (⟨bp i, hbp i hi⟩ : Fin n) := by
        rw [Subgroup.closure_le]
        rintro g ⟨j, hj1, hj2, -, rfl⟩
        have hg := hgen (i + 1) (by omega) hi1 j hj1 hj2
        simp only [Nat.add_sub_cancel] at hg
        obtain ⟨-, hc, -, -⟩ := genOK_spec hg
        have hcg : CodesGood k n U (codesL w (WP j) (WL j)) := fun x hx => hgt _ (by
          have := codes_idx hc x hx
          have := hofft (i + 1) (by omega)
          omega)
        exact (gen_good hn hg hcg).2.2 rfl (hbp i hi)
      exact hle hg
    · have : i + 1 = t := by omega
      rw [this, hCt, Subgroup.mem_bot] at hg
      rw [hg]
      rfl
  let τ : Nat → Nat → Equiv.Perm (Fin n) := fun i a =>
    cpermL k n U (codesL w (ptP (TT i a)) (ptL (TT i a)))
  have hτ : ∀ i (hi : i < t), ∀ a < Z i, CodesGood k n U (codesL w (ptP (TT i a)) (ptL (TT i a))) ∧
      τ i a ∈ C i ∧ ((τ i a ⟨bp i, hbp i hi⟩ : Fin n) : Nat) = ptX (TT i a) := by
    intro i hi a ha
    obtain ⟨hc, hmt⟩ := transOK_spec (htr i hi a ha)
    have hcg : CodesGood k n U (codesL w (ptP (TT i a)) (ptL (TT i a))) := fun x hx => hgt _ (by
      have := codes_idx hc x hx
      have := hofft (i + 1) (by omega)
      omega)
    refine ⟨hcg, ?_, mapsTo_spec hn (hbp i hi) hcg hmt⟩
    rw [hCi i hi]
    apply cpermL_mem
    intro x hx
    obtain ⟨c1, c2, c3⟩ := codes_idx hc x hx
    exact Subgroup.subset_closure ⟨_, c1, c2, c3, rfl⟩
  have hdist : ∀ i (hi : i < t), ∀ a < Z i, ∀ a' < Z i,
      τ i a ⟨bp i, hbp i hi⟩ = τ i a' ⟨bp i, hbp i hi⟩ → a = a' := by
    intro i hi a ha a' ha' e
    apply points_inj (hpts i hi) (fun a ha => by
      rw [← (hτ i hi a ha).2.2]
      exact lt_of_lt_of_le (Fin.isLt _) hn) a ha a' ha'
    rw [← (hτ i hi a ha).2.2, ← (hτ i hi a' ha').2.2, e]
  have hsch : ∀ i (hi : i < t), ∀ s ∈ Sg i, ∀ a < Z i, ∃ y < Z i, (τ i y)⁻¹ * s * τ i a ∈ C (i + 1) := by
    intro i hi s hs a ha
    obtain ⟨j, hj1, hj2, hj3, rfl⟩ := hs
    have hjg : Good k n (U j) := hgt j (by have := hofft (i + 1) (by omega); omega)
    obtain ⟨rec, hr⟩ := hrec i hi a ha j hj1 hj2
    obtain ⟨hy, hr⟩ := recOK_spec hr
    refine ⟨ptX rec, hy, ?_⟩
    obtain ⟨hga, -, -⟩ := hτ i hi a ha
    obtain ⟨hgy, -, -⟩ := hτ i hi (ptX rec) hy
    rcases hr with ⟨e1, e2⟩ | ⟨hc, hs⟩
    ·
      have : τ i (ptX rec) = netPerm k n (U j) * τ i a := by
        change cpermL k n U (codesL w (ptP (TT i (ptX rec))) (ptL (TT i (ptX rec)))) = _
        rw [e1, e2, show ptL (TT i a) + 1 = 1 + ptL (TT i a) from Nat.add_comm _ _,
          codesL_catW (by rwa [Nat.mul_one]), cpermL_append, cpermL_gen hj3]
      rw [this]
      have : (netPerm k n (U j) * τ i a)⁻¹ * netPerm k n (U j) * τ i a = 1 := by group
      rw [this]
      exact (C (i + 1)).one_mem
    ·
      set Py := ptP (TT i (ptX rec))
      set Ly := ptL (TT i (ptX rec))
      obtain ⟨hinv, hinvlt⟩ := codesL_invW (w := w) (P := Py) (len := Ly) hw0
      have hin : catW w (invW w Py Ly) Ly (2 * (j + 1)) < 2 ^ (w * (Ly + 1)) :=
        catW_lt hinvlt hj3
      have hcodes : codesL w (catW w (catW w (invW w Py Ly) Ly (2 * (j + 1))) (Ly + 1)
          (ptP (TT i a))) (Ly + 1 + ptL (TT i a)) =
          ((codesL w Py Ly).reverse.map (· ^^^ 1) ++ [2 * (j + 1)]) ++
            codesL w (ptP (TT i a)) (ptL (TT i a)) := by
        rw [codesL_catW hin, codesL_catW hinvlt, hinv, codesL_one hj3]
      have hcg : CodesGood k n U (codesL w (catW w (catW w (invW w Py Ly) Ly (2 * (j + 1))) (Ly + 1)
          (ptP (TT i a))) (Ly + 1 + ptL (TT i a))) := by
        rw [hcodes]
        intro x hx
        rcases List.mem_append.mp hx with hx | hx
        · rcases List.mem_append.mp hx with hx | hx
          · obtain ⟨x', hx', rfl⟩ := List.mem_map.mp hx
            rw [xor1_shr]
            exact hgy x' (List.mem_reverse.mp hx')
          · rw [List.mem_singleton.mp hx, shr1_eq,
              show 2 * (j + 1) / 2 - 1 = j by omega]
            exact hjg
        · exact hga x hx
      have c1 := hc
      have c2 := hs
      have hcr : CodesGood k n U (codesL w (ptP rec) (ptL rec)) := fun x hx => hgt _ (by
        have := codes_idx c1 x hx
        omega)
      have e := sweqK_spec hn hcg hcr c2
      have hsg : cpermL k n U [2 * (j + 1)] = netPerm k n (U j) := by
        rw [← codesL_one hj3]
        exact cpermL_gen hj3
      rw [hcodes, cpermL_append, cpermL_append, cpermL_inv, hsg] at e
      change (cpermL k n U (codesL w Py Ly))⁻¹ * netPerm k n (U j) * τ i a ∈ C (i + 1)
      rw [e]
      apply cpermL_mem
      intro x hx
      obtain ⟨d1, d2, d3⟩ := codes_idx c1 x hx
      exact hgenC (i + 1) (by omega) _ d1 d2 d3
  have hcard : ∀ i < t, Nat.card (C i) = Z i * Nat.card (C (i + 1)) := by
    intro i hi
    rw [hCi i hi]
    refine card_level (b := ⟨bp i, hbp i hi⟩) (τ := τ i) (fun a ha => ?_) (hdist i hi) ?_
      (hfixC i hi) (hsch i hi) (hb0 i hi).2
    · rw [← hCi i hi]
      exact (hτ i hi a ha).2.1
    · rw [← hCi i hi]
      exact hCmono i hi
  have hprod : ∀ d ≤ t, Nat.card (C (t - d)) = ∏ i ∈ Finset.Ico (t - d) t, Z i := by
    intro d
    induction d with
    | zero =>
      intro _
      rw [Nat.sub_zero, hCt, Subgroup.card_bot, Finset.Ico_self, Finset.prod_empty]
    | succ d ih =>
      intro hd
      rw [hcard (t - (d + 1)) (by omega), show t - (d + 1) + 1 = t - d by omega, ih (by omega),
        Finset.prod_eq_prod_Ico_succ_bot (by omega : t - (d + 1) < t),
        show t - (d + 1) + 1 = t - d by omega]
  have harr : CFSG.YGroups.arrClosure n O = C 0 := by
    apply le_antisymm
    · unfold CFSG.YGroups.arrClosure
      rw [Subgroup.closure_le]
      rintro g ⟨c, hc, rfl⟩
      rw [hOs] at hc
      obtain ⟨hs, hcl⟩ := hlet c hc
      have hcg1 : CodesGood k n U (codesL w (2 * (c + 1)) 1) := by
        rw [codesL_one (by omega)]
        intro x hx
        rw [List.mem_singleton.mp hx, shr1_eq, show 2 * (c + 1) / 2 - 1 = c by omega]
        exact (hL c hc).1
      have hcg2 : CodesGood k n U (codesL w (LP c) (LL c)) := fun x hx => hgt _ (by
        have := codes_idx hcl x hx
        omega)
      have e := sweqK_spec hn hcg1 hcg2 hs
      rw [cpermL_gen (by omega), (hL c hc).2] at e
      rw [e]
      apply cpermL_mem
      intro x hx
      obtain ⟨d1, d2, d3⟩ := codes_idx hcl x hx
      exact hgenC 0 (Nat.zero_le _) _ (by rw [hoff]; exact d1) d2 d3
    · by_cases ht : 0 < t
      · rw [hCi 0 ht, Subgroup.closure_le]
        rintro g ⟨j, hj1, hj2, -, rfl⟩
        have hg := hgen0 j hj1 hj2
        obtain ⟨-, hc, -, -⟩ := genOK_spec hg
        have hcg : CodesGood k n U (codesL w (WP j) (WL j)) := fun x hx => by
          have := codes_idx hc x hx
          exact (hL _ (by omega)).1
        rw [(gen_good hn hg hcg).2.1]
        apply cpermL_mem
        intro x hx
        have hxc := codes_idx hc x hx
        rw [(hL _ (by omega)).2]
        exact Subgroup.subset_closure ⟨_, by rw [hOs]; omega, rfl⟩
      · have : C 0 = ⊥ := if_neg ht
        rw [this]
        exact bot_le
  rw [harr, show (0 : Nat) = t - t by omega, hprod t le_rfl, Nat.sub_self, Finset.range_eq_Ico]

end CFSG.KC.YModel.Sch

end

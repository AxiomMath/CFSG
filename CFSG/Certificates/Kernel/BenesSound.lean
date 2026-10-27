module

public import Certificates.Data.Kernel.KDense.Bind
public import CFSG.Certificates.Kernel.LieCocycle.Fi22.NwValid
public import CFSG.Certificates.Kernel.MonsterConv.PermValid
public import Certificates.Data.Kernel.YModel.Model

public section

namespace CFSG.KC.Benes

open CFSG.KC.MonsterConv.Perm

@[expose] def swp (d m q : Nat) : Nat :=
  if m.testBit q = true then q + d else if d ≤ q ∧ m.testBit (q - d) = true then q - d else q

@[expose] def Disj (d m : Nat) : Prop := ∀ q, m.testBit q = true → m.testBit (q + d) = false

@[expose] def ValidIn (S d m : Nat) : Prop :=
  ∀ p, m.testBit p = true → p + d < S ∧ m.testBit (p + d) = false

@[expose] def Rep (S n M m : Nat) : Prop :=
  ∀ q, M.testBit q = (decide (q < S * n) && m.testBit (q % S))

theorem nxor (a b : Nat) : Nat.xor a b = a ^^^ b := rfl
theorem nland (a b : Nat) : Nat.land a b = a &&& b := rfl
theorem nlor (a b : Nat) : Nat.lor a b = a ||| b := rfl
theorem nshl (a b : Nat) : Nat.shiftLeft a b = a <<< b := rfl
theorem nshr (a b : Nat) : Nat.shiftRight a b = a >>> b := rfl
theorem nmul (a b : Nat) : Nat.mul a b = a * b := rfl
theorem nadd (a b : Nat) : Nat.add a b = a + b := rfl
theorem nsub (a b : Nat) : Nat.sub a b = a - b := rfl
theorem ndiv (a b : Nat) : Nat.div a b = a / b := rfl

theorem ones_eq (W : Nat) : ones W = 2 ^ W - 1 := by
  simp only [ones, nshl, nsub, Nat.one_shiftLeft]

theorem lt_two_pow_mono {x a b : Nat} (hx : x < 2 ^ a) (h : a ≤ b) : x < 2 ^ b :=
  Nat.lt_of_lt_of_le hx (Nat.pow_le_pow_right (by decide) h)

theorem land_ones_lt (x w : Nat) : x &&& (2 ^ w - 1) < 2 ^ w :=
  Nat.lt_of_le_of_lt Nat.and_le_right (Nat.sub_lt (Nat.two_pow_pos w) Nat.one_pos)

theorem validIn_disj {S d m : Nat} (h : ValidIn S d m) : Disj d m := fun p hp => (h p hp).2

theorem validIn_lt {S d m : Nat} (h : ValidIn S d m) {p : Nat} (hp : m.testBit p = true) : p < S := by
  have := (h p hp).1
  omega

theorem swp_swp {d m : Nat} (h : Disj d m) (q : Nat) : swp d m (swp d m q) = q := by
  by_cases h1 : m.testBit q = true
  · have h2 := h q h1
    have e : swp d m q = q + d := by simp [swp, h1]
    rw [e]
    simp [swp, h2, h1]
  · by_cases h3 : d ≤ q ∧ m.testBit (q - d) = true
    · have e : swp d m q = q - d := by simp [swp, h1, h3]
      rw [e]
      have e2 : q - d + d = q := by omega
      simp [swp, h3.2, e2]
    · have e : swp d m q = q := by simp [swp, h1, h3]
      rw [e, e]

theorem swp_lt {S d m : Nat} (h : ValidIn S d m) {p : Nat} (hp : p < S) : swp d m p < S := by
  unfold swp
  split
  · next h1 => exact (h p h1).1
  · split
    · omega
    · exact hp

theorem testBit_dsw {d m : Nat} (h : Disj d m) (x q : Nat) :
    (dsw d m x).testBit q = x.testBit (swp d m q) := by
  simp only [dsw, nxor, nland, nshl, nshr, Nat.testBit_xor, Nat.testBit_and,
    Nat.testBit_shiftLeft, Nat.testBit_shiftRight]
  unfold swp
  by_cases h1 : m.testBit q = true
  · have h0 : ∀ hd : d ≤ q, m.testBit (q - d) = false := by
      intro hd
      cases h2 : m.testBit (q - d)
      · rfl
      · have := h (q - d) h2
        rw [Nat.sub_add_cancel hd, h1] at this
        exact absurd this (by decide)
    rw [ite_eq_left h1, Nat.add_comm q d]
    by_cases hd : d ≤ q
    · simp only [h1, h0 hd, Bool.and_false, Bool.and_true, Bool.xor_false]
      cases x.testBit q <;> cases x.testBit (d + q) <;> rfl
    · have : decide (q ≥ d) = false := by simp; omega
      simp only [h1, this, Bool.false_and, Bool.and_true]
      cases x.testBit q <;> cases x.testBit (d + q) <;> rfl
  · simp only [Bool.not_eq_true] at h1
    rw [ite_eq_right (by simp [h1])]
    by_cases h3 : d ≤ q ∧ m.testBit (q - d) = true
    · rw [ite_eq_left h3]
      have e : d + (q - d) = q := by omega
      have hd : decide (q ≥ d) = true := by simp; omega
      simp only [h1, h3.2, hd, e, Bool.and_false, Bool.true_and, Bool.and_true]
      cases x.testBit q <;> cases x.testBit (q - d) <;> rfl
    · rw [ite_eq_right h3]
      have : (decide (q ≥ d) && m.testBit (q - d)) = false := by
        cases hd : decide (q ≥ d)
        · rfl
        · simp only [Bool.true_and]
          cases h4 : m.testBit (q - d)
          · rfl
          · exact absurd ⟨by simpa using hd, h4⟩ h3
      simp only [h1, Bool.and_false]
      cases hd : decide (q ≥ d)
      · simp
      · have h4 : m.testBit (q - d) = false := by simpa [hd] using this
        simp [h4]

theorem testBit_stage {d m : Nat} (h : Disj d m) (x q : Nat) :
    (CFSG.KLC.Fi22.stage x m d).testBit q = x.testBit (swp d m q) := by
  have e : CFSG.KLC.Fi22.stage x m d = dsw d m x := by
    have hs : ∀ (v : Nat) (k : Nat → Nat), CFSG.KLC.Fi22.sN v k = k v := by
      intro v k
      cases v <;> rfl
    unfold CFSG.KLC.Fi22.stage
    rw [hs]
    apply Nat.eq_of_testBit_eq
    intro i
    simp only [dsw, nxor, nland, nshl, nshr, nlor, Nat.testBit_xor, Nat.testBit_and,
      Nat.testBit_shiftLeft, Nat.testBit_shiftRight, Nat.testBit_or]
    have hc : ¬ (m.testBit i = true ∧ decide (i ≥ d) = true ∧ m.testBit (i - d) = true) := by
      rintro ⟨h1, h2, h3⟩
      have := h (i - d) h3
      rw [Nat.sub_add_cancel (by simpa using h2), h1] at this
      exact absurd this (by decide)
    revert hc
    cases m.testBit i <;> cases m.testBit (i - d) <;> cases decide (i ≥ d) <;>
      cases x.testBit i <;> cases x.testBit (d + i) <;> cases x.testBit (i - d) <;>
      cases x.testBit (d + (i - d)) <;> decide
  rw [e, testBit_dsw h]

@[expose] def iterF (f : Nat → Nat → Nat) : Nat → Nat → Nat → Nat
  | _, 0, s => s
  | a, n + 1, s => iterF f (a + 1) n (f a s)

@[expose] def compF (τ : Nat → Nat → Nat) : Nat → Nat → Nat → Nat
  | _, 0, q => q
  | a, n + 1, q => τ a (compF τ (a + 1) n q)

theorem iterF_snoc (f : Nat → Nat → Nat) : ∀ a n s, iterF f a (n + 1) s = f (a + n) (iterF f a n s)
  | a, 0, s => rfl
  | a, n + 1, s => by
    rw [iterF, iterF_snoc f (a + 1) n, iterF, Nat.add_right_comm, Nat.add_assoc]

theorem compF_snoc (τ : Nat → Nat → Nat) : ∀ a n q, compF τ a (n + 1) q = compF τ a n (τ (a + n) q)
  | a, 0, q => rfl
  | a, n + 1, q => by
    rw [compF, compF_snoc τ (a + 1) n, compF, Nat.add_right_comm, Nat.add_assoc]

theorem compF_shift (τ : Nat → Nat → Nat) : ∀ a n q,
    compF τ (a + 1) n q = compF (fun i => τ (i + 1)) a n q
  | a, 0, q => rfl
  | a, n + 1, q => by rw [compF, compF, compF_shift τ (a + 1) n]

theorem compF_congr {τ τ' : Nat → Nat → Nat} : ∀ a n, (∀ i, a ≤ i → i < a + n → τ i = τ' i) →
    ∀ q, compF τ a n q = compF τ' a n q
  | a, 0, _, q => rfl
  | a, n + 1, h, q => by
    rw [compF, compF, compF_congr (a + 1) n (fun i h1 h2 => h i (by omega) (by omega)),
      h a (Nat.le_refl a) (by omega)]

theorem testBit_iterF {f τ : Nat → Nat → Nat} {c : Nat}
    (hf : ∀ i < c, ∀ y q, (f i y).testBit q = y.testBit (τ i q)) :
    ∀ a n, a + n ≤ c → ∀ s q, (iterF f a n s).testBit q = s.testBit (compF τ a n q)
  | a, 0, _, s, q => rfl
  | a, n + 1, h, s, q => by
    rw [iterF, compF, testBit_iterF hf (a + 1) n (by omega) (f a s) q, hf a (by omega)]

theorem compF_rev {τ : Nat → Nat → Nat} : ∀ c, (∀ i < c, ∀ q, τ i (τ i q) = q) →
    ∀ q, compF (fun i => τ (c - 1 - i)) 0 c (compF τ 0 c q) = q
  | 0, _, q => rfl
  | c + 1, h, q => by
    rw [compF_snoc τ 0 c, compF, compF_shift, Nat.zero_add]
    simp only [Nat.add_sub_cancel, Nat.sub_zero]
    have e : (fun i => τ (c - (i + 1))) = (fun i => τ (c - 1 - i)) := by
      funext i
      congr 1
      omega
    rw [e, compF_rev c (fun i hi => h i (by omega)), h c (by omega)]

theorem compF_rev' {τ : Nat → Nat → Nat} (c : Nat) (h : ∀ i < c, ∀ q, τ i (τ i q) = q) (q : Nat) :
    compF τ 0 c (compF (fun i => τ (c - 1 - i)) 0 c q) = q := by
  have h' : ∀ i < c, ∀ q, (fun i => τ (c - 1 - i)) i ((fun i => τ (c - 1 - i)) i q) = q :=
    fun i hi q => h _ (by omega) q
  have := compF_rev c h' q
  have hc := compF_congr (τ := fun i => (fun i => τ (c - 1 - i)) (c - 1 - i)) (τ' := τ) 0 c
    (fun i _ hi => congrArg τ (by omega)) (compF (fun i => τ (c - 1 - i)) 0 c q)
  rw [← hc]
  exact this

theorem compF_lt {τ : Nat → Nat → Nat} {S c : Nat} (h : ∀ i < c, ∀ r < S, τ i r < S) :
    ∀ a n, a + n ≤ c → ∀ r < S, compF τ a n r < S
  | a, 0, _, r, hr => hr
  | a, n + 1, hn, r, hr => h a (by omega) _ (compF_lt h (a + 1) n (by omega) r hr)

theorem compF_rep {τ τ' : Nat → Nat → Nat} {S n c : Nat}
    (h1 : ∀ i < c, ∀ u < n, ∀ r < S, τ i (S * u + r) = S * u + τ' i r)
    (h2 : ∀ i < c, ∀ r < S, τ' i r < S) :
    ∀ a k, a + k ≤ c → ∀ u < n, ∀ r < S, compF τ a k (S * u + r) = S * u + compF τ' a k r
  | a, 0, _, u, hu, r, hr => rfl
  | a, k + 1, hk, u, hu, r, hr => by
    rw [compF, compF, compF_rep h1 h2 (a + 1) k (by omega) u hu r hr,
      h1 a (by omega) u hu _ (compF_lt h2 (a + 1) k (by omega) r hr)]

theorem compF_fix {τ : Nat → Nat → Nat} {c q : Nat} (h : ∀ i < c, τ i q = q) :
    ∀ a k, a + k ≤ c → compF τ a k q = q
  | a, 0, _ => rfl
  | a, k + 1, hk => by rw [compF, compF_fix h (a + 1) k (by omega), h a (by omega)]

theorem mod_add_lt {q d S : Nat} (h : q % S + d < S) : (q + d) % S = q % S + d := by
  rw [Nat.add_mod, Nat.mod_eq_of_lt (b := S) (a := d) (by omega), Nat.mod_eq_of_lt h]

theorem rep_disj {S n M m d : Nat} (hR : Rep S n M m) (hv : ValidIn S d m) : Disj d M := by
  intro q hq
  rw [hR] at hq ⊢
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hq
  have h := hv _ hq.2
  rw [mod_add_lt h.1, h.2, Bool.and_false]

theorem swp_rep {S n M m d : Nat} (hR : Rep S n M m) (hv : ValidIn S d m) {u r : Nat} (hu : u < n)
    (hr : r < S) : swp d M (S * u + r) = S * u + swp d m r := by
  have hlt : ∀ r', r' < S → S * u + r' < S * n := by
    intro r' hr'
    have : S * (u + 1) ≤ S * n := Nat.mul_le_mul_left _ hu
    rw [Nat.mul_succ] at this
    omega
  have hM : ∀ r', r' < S → M.testBit (S * u + r') = m.testBit r' := by
    intro r' hr'
    rw [hR, Nat.mul_add_mod, Nat.mod_eq_of_lt hr', decide_eq_true (hlt r' hr'), Bool.true_and]
  unfold swp
  rw [hM r hr]
  by_cases h1 : m.testBit r = true
  · rw [ite_eq_left h1, ite_eq_left h1, Nat.add_assoc]
  · rw [ite_eq_right h1, ite_eq_right h1]
    by_cases hd : d ≤ r
    · have e : S * u + r - d = S * u + (r - d) := by omega
      rw [e, hM (r - d) (by omega)]
      by_cases h3 : m.testBit (r - d) = true
      · rw [ite_eq_left (show d ≤ r ∧ m.testBit (r - d) = true from ⟨hd, h3⟩),
          ite_eq_left (show d ≤ S * u + r ∧ m.testBit (r - d) = true from ⟨by omega, h3⟩)]
      · rw [ite_eq_right (show ¬(d ≤ r ∧ m.testBit (r - d) = true) from fun h => h3 h.2),
          ite_eq_right (show ¬(d ≤ S * u + r ∧ m.testBit (r - d) = true) from fun h => h3 h.2)]
    · rw [ite_eq_right (show ¬(d ≤ r ∧ m.testBit (r - d) = true) from fun h => hd h.1)]
      rw [ite_eq_right]
      rintro ⟨hdq, h3⟩
      rw [hR] at h3
      simp only [Bool.and_eq_true, decide_eq_true_eq] at h3
      have hv' := (hv _ h3.2).1
      have e1 := Nat.div_add_mod (S * u + r - d) S
      have e2 : (S * ((S * u + r - d) / S) + ((S * u + r - d) % S + d)) % S =
          (S * u + r) % S := by
        congr 1
        omega
      rw [Nat.mul_add_mod, Nat.mod_eq_of_lt hv', Nat.mul_add_mod, Nat.mod_eq_of_lt hr] at e2
      omega

theorem swp_rep_hi {S n M m d : Nat} (hR : Rep S n M m) (hv : ValidIn S d m) {q : Nat}
    (hq : S * n ≤ q) : swp d M q = q := by
  have h0 : M.testBit q = false := by
    rw [hR, decide_eq_false (by omega), Bool.false_and]
  unfold swp
  rw [ite_eq_right (by simp [h0])]
  rw [ite_eq_right]
  rintro ⟨hd, h3⟩
  rw [hR] at h3
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h3
  have hv' := (hv _ h3.2).1
  have e1 := Nat.div_add_mod (q - d) S
  have hS : 0 < S := by omega
  have hv1 : (q - d) / S < n := (Nat.div_lt_iff_lt_mul hS).2 (by rw [Nat.mul_comm]; exact h3.1)
  have : S * ((q - d) / S + 1) ≤ S * n := Nat.mul_le_mul_left _ hv1
  rw [Nat.mul_succ] at this
  omega

theorem net_rep {f : Nat → Nat → Nat} {d M m : Nat → Nat} {S n c : Nat}
    (hf : ∀ i < c, ∀ y q, (f i y).testBit q = y.testBit (swp (d i) (M i) q))
    (hR : ∀ i < c, Rep S n (M i) (m i)) (hv : ∀ i < c, ValidIn S (d i) (m i)) (x : Nat) :
    (∀ u < n, ∀ r < S, (iterF f 0 c x).testBit (S * u + r) =
      x.testBit (S * u + compF (fun i => swp (d i) (m i)) 0 c r)) ∧
    (∀ q, S * n ≤ q → (iterF f 0 c x).testBit q = x.testBit q) := by
  refine ⟨fun u hu r hr => ?_, fun q hq => ?_⟩
  · rw [testBit_iterF hf 0 c (by omega),
      compF_rep (fun i hi u hu r hr => swp_rep (hR i hi) (hv i hi) hu hr)
        (fun i hi r hr => swp_lt (hv i hi) hr) 0 c (by omega) u hu r hr]
  · rw [testBit_iterF hf 0 c (by omega), compF_fix (fun i hi => swp_rep_hi (hR i hi) (hv i hi) hq)
      0 c (by omega)]

def geom (L : Nat) : Nat → Nat
  | 0 => 0
  | n + 1 => geom L n + 2 ^ (L * n)

theorem geom_mul (L : Nat) : ∀ n, (2 ^ L - 1) * geom L n = 2 ^ (L * n) - 1
  | 0 => by simp [geom]
  | n + 1 => by
    rw [geom, Nat.mul_add, geom_mul L n, Nat.mul_succ, Nat.pow_add]
    have h1 : 1 ≤ 2 ^ (L * n) := Nat.one_le_two_pow
    have h2 : 1 ≤ 2 ^ L := Nat.one_le_two_pow
    obtain ⟨a, ha⟩ : ∃ a, 2 ^ L = a + 1 := ⟨2 ^ L - 1, by omega⟩
    rw [ha, Nat.add_sub_cancel, Nat.mul_add, Nat.mul_one, Nat.mul_comm a]
    omega

theorem geom_div {L : Nat} (hL : 0 < L) (n : Nat) : (2 ^ (L * n) - 1) / (2 ^ L - 1) = geom L n := by
  have h : 0 < 2 ^ L - 1 := by
    have := Nat.one_lt_two_pow (n := L) (by omega)
    omega
  rw [← geom_mul L n, Nat.mul_div_cancel_left _ h]

theorem testBit_geom_mul {L c : Nat} (hc : c < 2 ^ L) : ∀ n q,
    (c * geom L n).testBit q = (decide (q < L * n) && c.testBit (q % L))
  | 0, q => by simp [geom]
  | n + 1, q => by
    have hlt : c * geom L n < 2 ^ (L * n) := by
      have h1 : c * geom L n ≤ (2 ^ L - 1) * geom L n := Nat.mul_le_mul_right _ (by omega)
      rw [geom_mul] at h1
      have := Nat.one_le_two_pow (n := L * n)
      omega
    rw [geom, Nat.mul_add, Nat.add_comm, Nat.mul_comm c (2 ^ _), Nat.testBit_two_pow_mul_add _ hlt,
      Nat.mul_succ]
    split
    · next h => rw [testBit_geom_mul hc n q, decide_eq_true h, decide_eq_true (by omega)]
    · next h =>
      by_cases h2 : q < L * n + L
      · rw [decide_eq_true h2, Bool.true_and]
        have : q % L = q - L * n := by
          rw [← Nat.sub_mul_mod (x := q) (k := n) (n := L) (by omega), Nat.mod_eq_of_lt (by omega)]
        rw [this]
      · rw [decide_eq_false h2, Bool.false_and]
        apply Nat.testBit_lt_two_pow
        exact Nat.lt_of_lt_of_le hc (Nat.pow_le_pow_right (by decide) (by omega))

theorem testBit_mul_div {W L n c : Nat} (hL : 0 < L) (hW : W = L * n) (hc : c < 2 ^ L) (q : Nat) :
    (c * ((2 ^ W - 1) / (2 ^ L - 1))).testBit q = (decide (q < W) && c.testBit (q % L)) := by
  rw [hW, geom_div hL, testBit_geom_mul hc]

theorem rep_mul_div {S n m : Nat} (hS : 0 < S) (hm : m < 2 ^ S) :
    Rep S n (m * ((2 ^ (S * n) - 1) / (2 ^ S - 1))) m :=
  fun q => testBit_mul_div hS rfl hm q

theorem rep_land_mul {W B : Nat} (x : Nat) (hW : 0 < W) :
    Rep W B ((x &&& (2 ^ W - 1)) * ((2 ^ (W * B) - 1) / (2 ^ W - 1))) (x &&& (2 ^ W - 1)) :=
  rep_mul_div hW (land_ones_lt x W)

theorem lt_of_validIn {S d m : Nat} (h : ValidIn S d m) : m < 2 ^ S := by
  apply Nat.lt_pow_two_of_testBit
  intro i hi
  cases hm : m.testBit i
  · rfl
  · have := validIn_lt h hm
    omega

theorem testBit_hiBlock (b r : Nat) :
    ((2 ^ 2 ^ b - 1) <<< 2 ^ b).testBit r = (decide (r ≥ 2 ^ b) && decide (r - 2 ^ b < 2 ^ b)) := by
  rw [Nat.testBit_shiftLeft, Nat.testBit_two_pow_sub_one]

theorem hiBlock_lt (b : Nat) : (2 ^ 2 ^ b - 1) <<< 2 ^ b < 2 ^ (2 ^ b + 2 ^ b) := by
  rw [Nat.shiftLeft_eq, Nat.pow_add]
  have := Nat.one_le_two_pow (n := 2 ^ b)
  exact Nat.mul_lt_mul_of_pos_right (by omega) (Nat.two_pow_pos _)

theorem testBit_top {b r : Nat} (hr : r < 2 ^ (b + 1)) : r.testBit b = decide (2 ^ b ≤ r) := by
  have h2 : 2 ^ (b + 1) = 2 ^ b * 2 := Nat.pow_succ 2 b
  have hlt : r / 2 ^ b < 2 := (Nat.div_lt_iff_lt_mul (Nat.two_pow_pos b)).2 (by rw [Nat.mul_comm]; omega)
  rw [Nat.testBit_eq_decide_div_mod_eq]
  by_cases h : 2 ^ b ≤ r
  · have : r / 2 ^ b = 1 := by
      have := (Nat.le_div_iff_mul_le (Nat.two_pow_pos b)).2 (by rw [Nat.one_mul]; exact h)
      omega
    rw [this, decide_eq_true h]
    rfl
  · have : r / 2 ^ b = 0 := Nat.div_eq_of_lt (by omega)
    rw [this, decide_eq_false h]
    rfl

theorem testBit_bitPlane {b W n : Nat} (hW : W = 2 ^ (b + 1) * n) (q : Nat) :
    (((2 ^ 2 ^ b - 1) <<< 2 ^ b) * ((2 ^ W - 1) / (2 ^ 2 ^ (b + 1) - 1))).testBit q =
      (decide (q < W) && q.testBit b) := by
  have e : 2 ^ (b + 1) = 2 ^ b + 2 ^ b := by rw [Nat.pow_succ]; omega
  rw [testBit_mul_div (L := 2 ^ (b + 1)) (n := n) (Nat.two_pow_pos _) hW (by rw [e]; exact hiBlock_lt b)]
  congr 1
  have hr : q % 2 ^ (b + 1) < 2 ^ (b + 1) := Nat.mod_lt _ (Nat.two_pow_pos _)
  have ht := testBit_top hr
  rw [Nat.testBit_mod_two_pow, decide_eq_true (Nat.lt_succ_self b), Bool.true_and] at ht
  rw [testBit_hiBlock, ht]
  generalize q % 2 ^ (b + 1) = r at hr ⊢
  have : r - 2 ^ b < 2 ^ b := by omega
  rw [decide_eq_true this, Bool.and_true]

@[expose] noncomputable def benesMask (k N i : Nat) : Nat :=
  Nat.land (Nat.shiftRight N (Nat.mul i (2 ^ k))) (ones (2 ^ k))

@[expose] noncomputable def benesPerm (k N : Nat) : Nat → Nat :=
  compF (fun i => swp (stageShift k i) (benesMask k N i)) 0 (2 * k - 1)

@[expose] noncomputable def benesInv (k N : Nat) : Nat → Nat :=
  compF (fun i => swp (stageShift k (2 * k - 1 - 1 - i)) (benesMask k N (2 * k - 1 - 1 - i))) 0
    (2 * k - 1)

@[expose] def StagesValid (k N : Nat) : Prop :=
  ∀ i < 2 * k - 1, ValidIn (2 ^ k) (stageShift k i) (benesMask k N i)

theorem benesPerm_lt {k N : Nat} (h : StagesValid k N) {p : Nat} (hp : p < 2 ^ k) :
    benesPerm k N p < 2 ^ k :=
  compF_lt (c := 2 * k - 1) (fun i hi r hr => swp_lt (h i hi) hr) 0 (2 * k - 1) (by omega) p hp

theorem benesInv_lt {k N : Nat} (h : StagesValid k N) {p : Nat} (hp : p < 2 ^ k) :
    benesInv k N p < 2 ^ k :=
  compF_lt (c := 2 * k - 1) (fun i hi r hr => swp_lt (h _ (by omega)) hr) 0 (2 * k - 1) (by omega) p hp

theorem benesInv_benesPerm {k N : Nat} (h : StagesValid k N) (p : Nat) :
    benesInv k N (benesPerm k N p) = p :=
  compF_rev (τ := fun i => swp (stageShift k i) (benesMask k N i)) _
    (fun i hi q => swp_swp (validIn_disj (h i hi)) q) p

theorem benesPerm_benesInv {k N : Nat} (h : StagesValid k N) (p : Nat) :
    benesPerm k N (benesInv k N p) = p :=
  compF_rev' (τ := fun i => swp (stageShift k i) (benesMask k N i)) _
    (fun i hi q => swp_swp (validIn_disj (h i hi)) q) p

theorem validIn_of_dsw {W d m : Nat} (h1 : m &&& (m <<< d) = 0) (h2 : m >>> (W - d) = 0) :
    ValidIn W d m := by
  intro p hp
  constructor
  · apply Nat.lt_of_not_le
    intro hc
    have := congrArg (fun x => x.testBit (p - (W - d))) h2
    simp only [Nat.testBit_shiftRight, Nat.zero_testBit] at this
    rw [show W - d + (p - (W - d)) = p by omega, hp] at this
    exact absurd this (by decide)
  · have := congrArg (fun x => x.testBit (p + d)) h1
    simp only [Nat.testBit_and, Nat.testBit_shiftLeft, Nat.zero_testBit, Nat.add_sub_cancel,
      hp, Bool.and_true] at this
    simpa using this

theorem andB_true {a b : Bool} (h : (Bool.rec false b a : Bool) = true) : a = true ∧ b = true := by
  cases a <;> cases b <;> simp_all

theorem recAll_left {P : Nat → Bool} : ∀ n,
    (Nat.rec (motive := fun _ => Bool) true (fun i ih => (Bool.rec false ih (P i) : Bool)) n) = true →
    ∀ i < n, P i = true
  | 0, _, i, hi => absurd hi (Nat.not_lt_zero i)
  | n + 1, h, i, hi => by
    obtain ⟨h1, h2⟩ := andB_true h
    rcases Nat.lt_succ_iff_lt_or_eq.1 hi with hi | rfl
    · exact recAll_left n h2 i hi
    · exact h1

theorem recAll_right {P : Nat → Bool} : ∀ n,
    (Nat.rec (motive := fun _ => Bool) true (fun i ih => (Bool.rec false (P i) ih : Bool)) n) = true →
    ∀ i < n, P i = true
  | 0, _, i, hi => absurd hi (Nat.not_lt_zero i)
  | n + 1, h, i, hi => by
    obtain ⟨h1, h2⟩ := andB_true h
    rcases Nat.lt_succ_iff_lt_or_eq.1 hi with hi | rfl
    · exact recAll_right n h1 i hi
    · exact h2

theorem stageShift_eq (k i : Nat) : stageShift k i = 2 ^ CFSG.KC.KDense.stBit k i := by
  unfold stageShift CFSG.KC.KDense.stBit
  cases Nat.blt i k <;> simp [Nat.one_shiftLeft]

theorem stBit_lt {k i : Nat} (hi : i < 2 * k - 1) : CFSG.KC.KDense.stBit k i < k := by
  unfold CFSG.KC.KDense.stBit
  cases h : Nat.blt i k
  · have h' : ¬ i < k := fun h2 => by rw [← Nat.blt_eq] at h2; rw [h2] at h; exact absurd h (by decide)
    change Nat.sub (Nat.add i 1) k < k
    simp only [nsub, nadd]
    omega
  · have h' : i < k := by rw [← Nat.blt_eq]; exact h
    change Nat.sub (Nat.sub k 1) i < k
    simp only [nsub]
    omega

theorem two_shl (b : Nat) : 2 <<< b = 2 ^ (b + 1) := by
  rw [Nat.shiftLeft_eq, Nat.pow_succ, Nat.mul_comm]

theorem idPlane_testBit {k b : Nat} (hb : b < k) (p : Nat) :
    (idPlane (2 ^ k) b).testBit p = (decide (p < 2 ^ k) && p.testBit b) := by
  have hW : 2 ^ k = 2 ^ (b + 1) * 2 ^ (k - (b + 1)) := by rw [← Nat.pow_add]; congr 1; omega
  have := testBit_bitPlane hW p
  simp only [idPlane, nmul, ndiv, nshl, ones_eq, Nat.one_shiftLeft, two_shl]
  rw [← this]
  congr 1
  exact Nat.mul_comm _ _

theorem add_two_pow_of_clear {k b p : Nat} (hb : b < k) (hp : p < 2 ^ k) (hc : p.testBit b = false) :
    p + 2 ^ b < 2 ^ k ∧ (p + 2 ^ b).testBit b = true := by
  have e1 := Nat.div_add_mod p (2 ^ b)
  have hr : p % 2 ^ b < 2 ^ b := Nat.mod_lt _ (Nat.two_pow_pos b)
  have hbit : ∀ a, (2 ^ b * a + p % 2 ^ b).testBit b = decide (a % 2 = 1) := by
    intro a
    rw [Nat.testBit_mul_two_pow_add_eq, Nat.testBit_lt_two_pow hr]
    cases decide (a % 2 = 1) <;> rfl
  have ha : (p / 2 ^ b) % 2 = 0 := by
    have := hbit (p / 2 ^ b)
    rw [e1, hc] at this
    have := this.symm
    simp at this
    omega
  have hk : 2 ^ k = 2 ^ b * 2 ^ (k - b) := by rw [← Nat.pow_add]; congr 1; omega
  have hE : 2 ^ (k - b) % 2 = 0 := by
    rw [show k - b = (k - b - 1) + 1 by omega, Nat.pow_succ]
    simp
  have hlt : p / 2 ^ b < 2 ^ (k - b) :=
    (Nat.div_lt_iff_lt_mul (Nat.two_pow_pos b)).2 (by rw [Nat.mul_comm, ← hk]; exact hp)
  have h2 : p / 2 ^ b + 2 ≤ 2 ^ (k - b) := by omega
  have h3 : 2 ^ b * (p / 2 ^ b + 2) ≤ 2 ^ b * 2 ^ (k - b) := Nat.mul_le_mul_left _ h2
  rw [← hk, Nat.mul_add] at h3
  constructor
  · omega
  · have e2 : p + 2 ^ b = 2 ^ b * (p / 2 ^ b + 1) + p % 2 ^ b := by rw [Nat.mul_succ]; omega
    rw [e2, hbit]
    simp
    omega

theorem stagesValid_of_netOK {k N : Nat} (h : CFSG.KC.KDense.netOK k N = true) : StagesValid k N := by
  obtain ⟨-, h2⟩ := andB_true h
  have h3 := recAll_left _ h2
  intro i hi
  have h4 := h3 i hi
  simp only [Nat.beq_eq, CFSG.KC.KDense.wK, nshl, Nat.one_shiftLeft] at h4
  have hb := stBit_lt hi
  have hm : ∀ p, (benesMask k N i).testBit p = true → p < 2 ^ k ∧ p.testBit (CFSG.KC.KDense.stBit k i) = false := by
    intro p hp
    have hlt : p < 2 ^ k := by
      have := hp
      simp only [benesMask, nland, Nat.testBit_and, ones_eq,
        Nat.testBit_two_pow_sub_one, Bool.and_eq_true, decide_eq_true_eq] at this
      exact this.2
    refine ⟨hlt, ?_⟩
    have := congrArg (fun x => x.testBit p) h4
    simp only [Nat.zero_testBit] at this
    change ((benesMask k N i) &&& idPlane (2 ^ k) (CFSG.KC.KDense.stBit k i)).testBit p = false at this
    · rw [Nat.testBit_and, hp, idPlane_testBit hb, decide_eq_true hlt] at this
      simpa using this
  intro p hp
  obtain ⟨hlt, hc⟩ := hm p hp
  obtain ⟨h5, h6⟩ := add_two_pow_of_clear hb hlt hc
  rw [stageShift_eq]
  refine ⟨h5, ?_⟩
  cases h7 : (benesMask k N i).testBit (p + 2 ^ CFSG.KC.KDense.stBit k i)
  · rfl
  · rw [(hm _ h7).2] at h6
    exact absurd h6 (by decide)

theorem stagesValid_of_netValid {k N : Nat} (h : netValid k N = true) : StagesValid k N := by
  obtain ⟨-, h2⟩ := andB_true h
  have h3 := recAll_right _ h2
  intro i hi
  obtain ⟨h4, h5⟩ := andB_true (h3 i hi)
  simp only [Nat.beq_eq, nshl, Nat.one_shiftLeft] at h4 h5
  exact validIn_of_dsw h4 h5

theorem rep_repP {S m : Nat} (hm : ∀ p, m.testBit p = true → p < S) : ∀ n,
    Rep S n (CFSG.KC.KDense.repP S n m) m
  | 0, q => by
    change Nat.testBit 0 q = _
    simp
  | n + 1, q => by
    have ih := rep_repP hm n
    change (CFSG.KC.KDense.repP S n m ||| m <<< (n * S)).testBit q = _
    rw [Nat.testBit_or, ih, Nat.testBit_shiftLeft, Nat.mul_comm n S]
    by_cases h1 : q < S * n
    · rw [decide_eq_true h1, decide_eq_false (by omega), decide_eq_true (by rw [Nat.mul_succ]; omega)]
      simp
    · rw [decide_eq_false h1, decide_eq_true (by omega), Bool.false_and, Bool.false_or, Bool.true_and]
      by_cases h2 : q < S * (n + 1)
      · rw [decide_eq_true h2, Bool.true_and]
        have : q % S = q - S * n := by
          rw [← Nat.sub_mul_mod (x := q) (k := n) (n := S) (by omega),
            Nat.mod_eq_of_lt (by rw [Nat.mul_succ] at h2; omega)]
        rw [this]
      · rw [decide_eq_false h2, Bool.false_and]
        cases h3 : m.testBit (q - S * n)
        · rfl
        · have := hm _ h3
          rw [Nat.mul_succ] at h2
          omega

theorem strictN_eq (y : Nat) (k : Nat → Nat) : CFSG.KC.Loop.strictN y k = k y := by
  cases y <;> rfl

theorem rec_strictN (g : Nat → Nat → Nat) (e : Nat) : ∀ j, j ≤ e + 1 → ∀ s,
    (Nat.rec (motive := fun _ => Nat → Nat) (fun y => y)
      (fun j ih y => CFSG.KC.Loop.strictN (g (Nat.sub e j) y) ih) j s) = iterF g (e + 1 - j) j s
  | 0, _, s => rfl
  | j + 1, hj, s => by
    have ih := rec_strictN g e j (by omega) (g (Nat.sub e j) s)
    have e1 : e + 1 - (j + 1) = Nat.sub e j := by simp only [nsub]; omega
    have e2 : e + 1 - j = Nat.sub e j + 1 := by simp only [nsub]; omega
    rw [e1, iterF, ← e2, ← ih]
    exact strictN_eq _ _

theorem iterF_zero_len (f : Nat → Nat → Nat) (a b s : Nat) : iterF f a 0 s = iterF f b 0 s := rfl

theorem testBit_netP {S k n N : Nat} (hS : S = 2 ^ k) (h : CFSG.KC.KDense.netOK k N = true)
    (x : Nat) :
    (∀ u < n, ∀ r < S, (CFSG.KC.KDense.netP S k n N x).testBit (S * u + r) =
      x.testBit (S * u + benesPerm k N r)) ∧
    (∀ q, S * n ≤ q → (CFSG.KC.KDense.netP S k n N x).testBit q = x.testBit q) := by
  have hv := stagesValid_of_netOK h
  subst hS
  have e : CFSG.KC.KDense.netP (2 ^ k) k n N x = iterF (fun i y => dsw (stageShift k i)
      (CFSG.KC.KDense.repP (2 ^ k) n (benesMask k N i)) y) 0 (2 * k - 1) x := by
    refine Eq.trans (rec_strictN (fun i y => dsw (stageShift k i)
      (CFSG.KC.KDense.repP (2 ^ k) n (benesMask k N i)) y) (Nat.sub (Nat.mul 2 k) 2) (2 * k - 1)
      (by simp only [nsub, nmul]; omega) x) ?_
    rcases Nat.eq_zero_or_pos k with hk | hk
    · subst hk
      rfl
    · congr 1
      simp only [nsub, nmul]
      omega
  rw [e]
  have hR : ∀ i < 2 * k - 1, Rep (2 ^ k) n (CFSG.KC.KDense.repP (2 ^ k) n (benesMask k N i))
      (benesMask k N i) := fun i hi => rep_repP (fun p hp => validIn_lt (hv i hi) hp) n
  exact net_rep (d := fun i => stageShift k i) (m := fun i => benesMask k N i)
    (fun i hi y q => testBit_dsw (rep_disj (hR i hi) (hv i hi)) y q) hR hv x

theorem repU_eq (W P : Nat) : repU W P = (2 ^ (W * P) - 1) / (2 ^ W - 1) := by
  simp only [repU, ndiv, nsub, nshl, nmul, Nat.one_shiftLeft]

theorem testBit_netApply {k W P N : Nat} (hW : W = 2 ^ k) (h : StagesValid k N) (X : Nat) :
    (∀ u < P, ∀ r < W, (netApply k W (repU W P) N X).testBit (W * u + r) =
      X.testBit (W * u + benesPerm k N r)) ∧
    (∀ q, W * P ≤ q → (netApply k W (repU W P) N X).testBit q = X.testBit q) := by
  subst hW
  have e : netApply k (2 ^ k) (repU (2 ^ k) P) N X = iterF (fun i y => dsw (stageShift k i)
      (benesMask k N i * repU (2 ^ k) P) y) 0 (2 * k - 1) X := by
    refine Eq.trans (rec_strictN (fun i y => dsw (stageShift k i)
      (benesMask k N i * repU (2 ^ k) P) y) (Nat.sub (Nat.mul 2 k) 2) (2 * k - 1)
      (by simp only [nsub, nmul]; omega) X) ?_
    rcases Nat.eq_zero_or_pos k with hk | hk
    · subst hk
      rfl
    · congr 1
      simp only [nsub, nmul]
      omega
  rw [e]
  have hR : ∀ i < 2 * k - 1, Rep (2 ^ k) P (benesMask k N i * repU (2 ^ k) P) (benesMask k N i) := by
    intro i hi
    rw [repU_eq]
    exact rep_mul_div (Nat.two_pow_pos k) (lt_of_validIn (h i hi))
  exact net_rep (d := fun i => stageShift k i) (m := fun i => benesMask k N i)
    (fun i hi y q => testBit_dsw (rep_disj (hR i hi) (h i hi)) y q) hR h X

theorem repU_one {W : Nat} (hW : 0 < W) : repU W 1 = 1 := by
  rw [repU_eq, Nat.mul_one, Nat.div_self]
  have := Nat.one_lt_two_pow (n := W) (by omega)
  omega

theorem stagesValid_of_ymodel {k N : Nat} (h : CFSG.KC.YModel.netOK k N = true) : StagesValid k N :=
  stagesValid_of_netOK h

section Fi22

open CFSG.KLC.Fi22

@[expose] noncomputable def nwTau (NW s : Nat) : Nat → Nat := swp (stageDist s) (nwMask NW s)

@[expose] noncomputable def nwPerm (NW : Nat) : Nat → Nat := compF (nwTau NW) 0 23

@[expose] noncomputable def nwInv (NW : Nat) : Nat → Nat := compF (fun s => nwTau NW (22 - s)) 0 23

theorem maskN_eq (w : Nat) : maskN w = 2 ^ w - 1 := by
  simp only [maskN, nshl, nsub, Nat.one_shiftLeft]

theorem nw_valid {NW : Nat} (h : nwValid NW = true) : ∀ s < 23, ValidIn 4096 (stageDist s) (nwMask NW s) := by
  obtain ⟨-, h2⟩ := andB_true h
  have h3 := recAll_right (P := fun s => (fun m d => CFSG.KLC.Fi22.andB (Nat.beq (Nat.land m (Nat.shiftLeft m d)) 0)
    (Nat.beq (Nat.shiftRight m (Nat.sub 4096 d)) 0)) (nwMask NW s) (stageDist s)) 23 h2
  intro s hs
  obtain ⟨h4, h5⟩ := andB_true (h3 s hs)
  simp only [Nat.beq_eq] at h4 h5
  exact validIn_of_dsw h4 h5

theorem nwPerm_lt {NW : Nat} (h : nwValid NW = true) {p : Nat} (hp : p < 4096) : nwPerm NW p < 4096 :=
  compF_lt (c := 23) (fun i hi r hr => swp_lt (nw_valid h i hi) hr) 0 23 (by omega) p hp

theorem nwInv_lt {NW : Nat} (h : nwValid NW = true) {p : Nat} (hp : p < 4096) : nwInv NW p < 4096 :=
  compF_lt (c := 23) (fun i hi r hr => swp_lt (nw_valid h (22 - i) (by omega)) hr) 0 23 (by omega) p hp

theorem nwInv_nwPerm {NW : Nat} (h : nwValid NW = true) (p : Nat) : nwInv NW (nwPerm NW p) = p :=
  compF_rev (τ := nwTau NW) 23 (fun i hi q => swp_swp (validIn_disj (nw_valid h i hi)) q) p

theorem nwPerm_nwInv {NW : Nat} (h : nwValid NW = true) (p : Nat) : nwPerm NW (nwInv NW p) = p :=
  compF_rev' (τ := nwTau NW) 23 (fun i hi q => swp_swp (validIn_disj (nw_valid h i hi)) q) p

theorem sN_eq (v : Nat) (k : Nat → Nat) : sN v k = k v := by
  cases v <;> rfl

theorem iterN_eq (c : Nat) (f : Nat → Nat → Nat) (s : Nat) : iterN c f s = iterF f 0 c s := by
  unfold iterN
  have key : ∀ j, j ≤ c → ∀ s, (Nat.rec (motive := fun _ => Nat → Nat) (fun s => s)
      (fun i ih s => sN (f (Nat.sub (Nat.sub c 1) i) s) ih) j s) = iterF f (c - j) j s := by
    intro j
    induction j with
    | zero => intro _ s; rfl
    | succ j ih =>
      intro hj s
      have h1 := ih (by omega) (f (Nat.sub (Nat.sub c 1) j) s)
      have e1 : c - (j + 1) = Nat.sub (Nat.sub c 1) j := by simp only [nsub]; omega
      have e2 : c - j = Nat.sub (Nat.sub c 1) j + 1 := by simp only [nsub]; omega
      rw [e1, iterF, ← e2, ← h1]
      exact sN_eq _ _
  rw [key c (Nat.le_refl c), Nat.sub_self]

theorem rep_nw (NW s B : Nat) :
    Rep 4096 B (Nat.mul (nwMask NW s) (maskN (4096 * B) / M4096)) (nwMask NW s) := by
  have := rep_land_mul (W := 4096) (B := B) (Nat.shiftRight NW (Nat.shiftLeft s 12)) (Nat.zero_lt_succ _)
  simpa only [nwMask, nmul, nland, M4096, maskN_eq] using this

theorem testBit_applyNW {NW : Nat} (h : nwValid NW = true) {B R : Nat}
    (hR : R = maskN (4096 * B) / M4096) (X : Nat) :
    (∀ u < B, ∀ p < 4096, (applyNW NW R X).testBit (4096 * u + p) =
      X.testBit (4096 * u + nwPerm NW p)) ∧
    (∀ q, 4096 * B ≤ q → (applyNW NW R X).testBit q = X.testBit q) := by
  subst hR
  unfold applyNW
  rw [iterN_eq]
  exact net_rep (d := stageDist) (m := nwMask NW)
    (fun i hi y q => testBit_stage (rep_disj (rep_nw NW i B) (nw_valid h i hi)) y q)
    (fun i _ => rep_nw NW i B) (nw_valid h) X

theorem testBit_applyInvNW {NW : Nat} (h : nwValid NW = true) {B R : Nat}
    (hR : R = maskN (4096 * B) / M4096) (X : Nat) :
    (∀ u < B, ∀ p < 4096, (applyInvNW NW R X).testBit (4096 * u + p) =
      X.testBit (4096 * u + nwInv NW p)) ∧
    (∀ q, 4096 * B ≤ q → (applyInvNW NW R X).testBit q = X.testBit q) := by
  subst hR
  unfold applyInvNW
  rw [iterN_eq]
  exact net_rep (d := fun s => stageDist (22 - s)) (m := fun s => nwMask NW (22 - s))
    (fun i hi y q => testBit_stage (rep_disj (rep_nw NW (22 - i) B) (nw_valid h (22 - i) (by omega))) y q)
    (fun i _ => rep_nw NW (22 - i) B) (fun i hi => nw_valid h (22 - i) (by omega)) X

theorem one_eq_rep : (1 : Nat) = maskN (4096 * 1) / M4096 := by
  rw [Nat.mul_one, M4096, Nat.div_self]
  rw [maskN_eq]
  have := Nat.one_lt_two_pow (n := 4096) (by decide)
  omega

theorem REP_eq_rep : REP = maskN (4096 * 3510) / M4096 := rfl

@[expose] noncomputable def dstep (k y : Nat) : Nat :=
  sN (Nat.land y (dilMask k)) (fun h =>
    Nat.lor (Nat.xor y h) (Nat.shiftLeft h (Nat.mul 15 (Nat.shiftLeft 1 k))))

theorem dilMask_testBit {k : Nat} (hk : k ≤ 11) (q : Nat) :
    (dilMask k).testBit q = (decide (q < 65536) &&
      (decide (2 ^ k ≤ q % 2 ^ (k + 5)) && decide (q % 2 ^ (k + 5) - 2 ^ k < 2 ^ k))) := by
  have hW : 65536 = 2 ^ (k + 5) * 2 ^ (11 - k) := by
    rw [← Nat.pow_add, show k + 5 + (11 - k) = 16 by omega]
  have hc : (2 ^ 2 ^ k - 1) <<< 2 ^ k < 2 ^ 2 ^ (k + 5) := by
    refine Nat.lt_of_lt_of_le (hiBlock_lt k) (Nat.pow_le_pow_right (by decide) ?_)
    have := Nat.pow_le_pow_right (n := 2) (by decide) (show k + 1 ≤ k + 5 by omega)
    rw [Nat.pow_succ] at this
    omega
  have := testBit_mul_div (Nat.two_pow_pos (k + 5)) hW hc q
  simp only [dilMask, nmul, ndiv, nshl, nadd, maskN_eq, Nat.one_shiftLeft] at this ⊢
  rw [this, Nat.testBit_shiftLeft, Nat.testBit_two_pow_sub_one]

theorem dstep_testBit (k y q : Nat) :
    (dstep k y).testBit q =
      ((y.testBit q && !(dilMask k).testBit q) ||
        (decide (15 * 2 ^ k ≤ q) && y.testBit (q - 15 * 2 ^ k) && (dilMask k).testBit (q - 15 * 2 ^ k))) := by
  unfold dstep
  rw [sN_eq]
  simp only [nlor, nxor, nland, nshl, nmul, Nat.one_shiftLeft, Nat.testBit_or, Nat.testBit_xor,
    Nat.testBit_and, Nat.testBit_shiftLeft]
  cases y.testBit q <;> cases (dilMask k).testBit q <;> simp [Bool.and_assoc]

@[expose] def DInv (x A y : Nat) : Prop :=
  ∀ q, y.testBit q = (decide (q < 65536 ∧ q % (16 * A) < A) && x.testBit (q / (16 * A) * A + q % A))

theorem dtrans_gen {x y y' A s : Nat} {D : Nat → Prop} [DecidablePred D]
    (hy : DInv x (2 * A) y)
    (hy' : ∀ q, y'.testBit q = ((y.testBit q && !decide (D q)) ||
      (decide (s ≤ q) && y.testBit (q - s) && decide (D (q - s)))))
    (a1 : ∀ q, (q < 65536 ∧ q % (16 * A) < A) →
      ((q < 65536 ∧ q % (16 * (2 * A)) < 2 * A) ∧ ¬ D q ∧
        q / (16 * (2 * A)) * (2 * A) + q % (2 * A) = q / (16 * A) * A + q % A ∧
        ¬ (s ≤ q ∧ (q - s < 65536 ∧ (q - s) % (16 * (2 * A)) < 2 * A) ∧ D (q - s))) ∨
      (¬ ((q < 65536 ∧ q % (16 * (2 * A)) < 2 * A) ∧ ¬ D q) ∧ s ≤ q ∧
        (q - s < 65536 ∧ (q - s) % (16 * (2 * A)) < 2 * A) ∧ D (q - s) ∧
        (q - s) / (16 * (2 * A)) * (2 * A) + (q - s) % (2 * A) = q / (16 * A) * A + q % A))
    (a2 : ∀ q, ¬ (q < 65536 ∧ q % (16 * A) < A) →
      ¬ ((q < 65536 ∧ q % (16 * (2 * A)) < 2 * A) ∧ ¬ D q) ∧
      ¬ (s ≤ q ∧ (q - s < 65536 ∧ (q - s) % (16 * (2 * A)) < 2 * A) ∧ D (q - s))) :
    DInv x A y' := by
  intro q
  rw [hy', hy q, hy (q - s)]
  by_cases hv : q < 65536 ∧ q % (16 * A) < A
  · rw [decide_eq_true hv, Bool.true_and]
    rcases a1 q hv with ⟨h1, h2, h3, h4⟩ | ⟨h1, h2, h3, h4, h5⟩
    · rw [decide_eq_true h1, decide_eq_false h2, h3]
      by_cases h5 : s ≤ q
      · by_cases h6 : q - s < 65536 ∧ (q - s) % (16 * (2 * A)) < 2 * A
        · rw [decide_eq_true h5, decide_eq_true h6, decide_eq_false (fun h => h4 ⟨h5, h6, h⟩)]
          simp
        · rw [decide_eq_false h6]
          simp
      · rw [decide_eq_false h5]
        simp
    · rw [decide_eq_true h2, decide_eq_true h3, decide_eq_true h4, h5]
      by_cases h6 : q < 65536 ∧ q % (16 * (2 * A)) < 2 * A
      · have : D q := by
          by_cases hn : D q
          · exact hn
          · exact absurd ⟨h6, hn⟩ h1
        rw [decide_eq_true this]
        simp
      · rw [decide_eq_false h6]
        simp
  · rw [decide_eq_false hv, Bool.false_and]
    obtain ⟨h1, h2⟩ := a2 q hv
    have t1 : (decide (q < 65536 ∧ q % (16 * (2 * A)) < 2 * A) &&
        x.testBit (q / (16 * (2 * A)) * (2 * A) + q % (2 * A)) && !decide (D q)) = false := by
      by_cases h6 : q < 65536 ∧ q % (16 * (2 * A)) < 2 * A
      · have : D q := by
          by_cases hn : D q
          · exact hn
          · exact absurd ⟨h6, hn⟩ h1
        rw [decide_eq_true this]
        simp
      · rw [decide_eq_false h6]
        simp
    rw [t1, Bool.false_or]
    by_cases h5 : s ≤ q
    · by_cases h6 : q - s < 65536 ∧ (q - s) % (16 * (2 * A)) < 2 * A
      · rw [decide_eq_true h5, decide_eq_true h6, decide_eq_false (fun h => h2 ⟨h5, h6, h⟩)]
        simp
      · rw [decide_eq_false h6]
        simp
    · rw [decide_eq_false h5]
      simp

theorem dtrans {x : Nat} : ∀ k, k ≤ 11 → ∀ y, DInv x (2 * 2 ^ k) y → DInv x (2 ^ k) (dstep k y) := by
  intro k hk y hy
  refine dtrans_gen (s := 15 * 2 ^ k)
    (D := fun q => q < 65536 ∧ 2 ^ k ≤ q % 2 ^ (k + 5) ∧ q % 2 ^ (k + 5) - 2 ^ k < 2 ^ k) hy ?_ ?_ ?_
  · intro q
    rw [dstep_testBit, dilMask_testBit hk, dilMask_testBit hk]
    simp only [Bool.decide_and]
  all_goals
    have : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5 ∨ k = 6 ∨ k = 7 ∨ k = 8 ∨ k = 9 ∨
      k = 10 ∨ k = 11 := by omega
    rcases this with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    · intro q
      simp only [Nat.reducePow, Nat.reduceAdd, Nat.reduceMul]
      omega

theorem dil_eq (x : Nat) : dil x = iterF (fun i y => dstep (11 - i) y) 0 12 x := by
  unfold dil
  rw [iterN_eq]
  rfl

theorem dil_inv {x : Nat} : ∀ a n, a + n ≤ 12 → ∀ y, DInv x (2 ^ (12 - a)) y →
    DInv x (2 ^ (12 - a - n)) (iterF (fun i y => dstep (11 - i) y) a n y)
  | a, 0, _, y, hy => hy
  | a, n + 1, hn, y, hy => by
    rw [iterF]
    have h1 := dtrans (x := x) (11 - a) (by omega) y (by
      rw [← Nat.pow_succ', Nat.succ_eq_add_one, show 11 - a + 1 = 12 - a by omega]
      exact hy)
    have e : 2 ^ (11 - a) = 2 ^ (12 - (a + 1)) := by rw [show 11 - a = 12 - (a + 1) by omega]
    rw [e] at h1
    have := dil_inv (a + 1) n (by omega) (dstep (11 - a) y) h1
    rwa [show 12 - (a + 1) - n = 12 - a - (n + 1) by omega] at this

theorem testBit_dil {x : Nat} (hx : x < 2 ^ 4096) (q : Nat) :
    (dil x).testBit q = (decide (q < 65536 ∧ q % 16 = 0) && x.testBit (q / 16)) := by
  have h0 : DInv x 4096 x := by
    intro q
    by_cases h : q < 4096
    · rw [decide_eq_true (show q < 65536 ∧ q % (16 * 4096) < 4096 by omega), Bool.true_and]
      congr 1
      omega
    · rw [decide_eq_false (show ¬(q < 65536 ∧ q % (16 * 4096) < 4096) by omega), Bool.false_and]
      exact Nat.testBit_lt_two_pow (lt_two_pow_mono hx (by omega))
  have := dil_inv 0 12 (by omega) x h0 q
  rw [dil_eq, this]
  have e : (2 : Nat) ^ (12 - 0 - 12) = 1 := rfl
  rw [e, Nat.mul_one, Nat.mul_one, Nat.mod_one, Nat.add_zero]
  by_cases hq : q < 65536 ∧ q % 16 = 0
  · rw [decide_eq_true hq, decide_eq_true (show q < 65536 ∧ q % 16 < 1 by omega)]
  · rw [decide_eq_false hq, decide_eq_false (show ¬(q < 65536 ∧ q % 16 < 1) by omega)]

theorem testBit_dil_shift {y : Nat} (hy : y < 2 ^ 4096) {j j0 p : Nat} (hj : j < 16) (hj0 : j0 < 16)
    (hp : p < 4096) : (dil y <<< j).testBit (16 * p + j0) = (decide (j = j0) && y.testBit p) := by
  rw [Nat.testBit_shiftLeft, testBit_dil hy]
  by_cases h : j = j0
  · subst h
    have h1 : 16 * p + j ≥ j := by omega
    have h2 : 16 * p + j - j < 65536 ∧ (16 * p + j - j) % 16 = 0 := by omega
    have h3 : (16 * p + j - j) / 16 = p := by omega
    rw [decide_eq_true h1, decide_eq_true h2, h3, decide_eq_true (rfl : j = j)]
    simp only [Bool.true_and]
  · by_cases hle : 16 * p + j0 ≥ j
    · have h2 : ¬ (16 * p + j0 - j < 65536 ∧ (16 * p + j0 - j) % 16 = 0) := by omega
      rw [decide_eq_true hle, decide_eq_false h2, decide_eq_false h]
      simp
    · rw [decide_eq_false hle, decide_eq_false h]
      simp

theorem arrOf_iter {pl : Nat → Nat} {j0 p q : Nat}
    (ht : ∀ j < 12, (dil (pl j) <<< j).testBit q = (decide (j = j0) && (pl j0).testBit p)) :
    ∀ a n, a + n ≤ 12 → ∀ acc, (iterF (fun j acc => Nat.lor acc (Nat.shiftLeft (dil (pl j)) j)) a n acc).testBit q =
      (acc.testBit q || (decide (a ≤ j0 ∧ j0 < a + n) && (pl j0).testBit p))
  | a, 0, _, acc => by
    rw [decide_eq_false (show ¬(a ≤ j0 ∧ j0 < a + 0) by omega)]
    simp [iterF]
  | a, n + 1, hn, acc => by
    rw [iterF, arrOf_iter ht (a + 1) n (by omega), nlor, nshl, Nat.testBit_or, ht a (by omega)]
    by_cases h : a = j0
    · subst h
      rw [decide_eq_true (rfl : a = a), decide_eq_true (show a ≤ a ∧ a < a + (n + 1) by omega),
        decide_eq_false (show ¬(a + 1 ≤ a ∧ a < a + 1 + n) by omega)]
      simp
    · rw [decide_eq_false h]
      by_cases h2 : a + 1 ≤ j0 ∧ j0 < a + 1 + n
      · rw [decide_eq_true h2, decide_eq_true (show a ≤ j0 ∧ j0 < a + (n + 1) by omega)]
        simp
      · rw [decide_eq_false h2, decide_eq_false (show ¬(a ≤ j0 ∧ j0 < a + (n + 1)) by omega)]
        simp

theorem testBit_arrOf {pl : Nat → Nat} (hpl : ∀ j < 12, pl j < 2 ^ 4096) {p j0 : Nat} (hp : p < 4096)
    (hj0 : j0 < 16) : (arrOf pl).testBit (16 * p + j0) = (decide (j0 < 12) && (pl j0).testBit p) := by
  unfold arrOf
  rw [iterN_eq]
  have ht : ∀ j < 12, (dil (pl j) <<< j).testBit (16 * p + j0) = (decide (j = j0) && (pl j0).testBit p) := by
    intro j hj
    rw [testBit_dil_shift (hpl j hj) (by omega) hj0 hp]
    by_cases h : j = j0
    · subst h
      rfl
    · rw [decide_eq_false h, Bool.false_and, Bool.false_and]
  rw [arrOf_iter ht 0 12 (by omega), Nat.zero_testBit, Bool.false_or]
  congr 1

theorem coord_testBit {j : Nat} (hj : j < 12) (q : Nat) :
    (coord j).testBit q = (decide (q < 4096) && q.testBit j) := by
  have hW : 4096 = 2 ^ (j + 1) * 2 ^ (11 - j) := by
    rw [← Nat.pow_add, show j + 1 + (11 - j) = 12 by omega]
  have := testBit_bitPlane hW q
  simp only [coord, nmul, ndiv, nshl, nadd, M4096, maskN_eq, Nat.one_shiftLeft]
  exact this

theorem lt_of_testBit_ge {x W : Nat} (h : ∀ q, W ≤ q → x.testBit q = false) : x < 2 ^ W :=
  Nat.lt_pow_two_of_testBit x h

theorem arr_entry {F : Nat → Nat} (σ : Nat → Nat) (hσ : ∀ p < 4096, σ p < 4096)
    (happ : ∀ j < 12, (∀ p < 4096, (F j).testBit p = (coord j).testBit (σ p)) ∧
      ∀ q, 4096 ≤ q → (F j).testBit q = (coord j).testBit q)
    {p : Nat} (hp : p < 4096) : arrOf F / 2 ^ (16 * p) % 2 ^ 16 = σ p := by
  have hpl : ∀ j < 12, F j < 2 ^ 4096 := by
    intro j hj
    apply lt_of_testBit_ge
    intro q hq
    rw [(happ j hj).2 q hq, coord_testBit hj, decide_eq_false (by omega), Bool.false_and]
  apply Nat.eq_of_testBit_eq
  intro j0
  rw [Nat.testBit_mod_two_pow, Nat.testBit_div_two_pow]
  have hs := hσ p hp
  by_cases h16 : j0 < 16
  · rw [decide_eq_true h16, Bool.true_and, Nat.add_comm, testBit_arrOf hpl hp h16]
    by_cases h12 : j0 < 12
    · rw [decide_eq_true h12, Bool.true_and, (happ j0 h12).1 p hp, coord_testBit h12,
        decide_eq_true hs, Bool.true_and]
    · rw [decide_eq_false h12, Bool.false_and, Nat.testBit_lt_two_pow
        (Nat.lt_of_lt_of_le hs (Nat.pow_le_pow_right (n := 2) (by decide) (show 12 ≤ j0 by omega)))]
  · rw [decide_eq_false h16, Bool.false_and, Nat.testBit_lt_two_pow
      (Nat.lt_of_lt_of_le hs (Nat.pow_le_pow_right (n := 2) (by decide) (show 12 ≤ j0 by omega)))]

theorem arrNW_entry {NW : Nat} (h : nwValid NW = true) {p : Nat} (hp : p < 4096) :
    arrNW NW / 2 ^ (16 * p) % 2 ^ 16 = nwPerm NW p := by
  unfold arrNW
  refine arr_entry (nwPerm NW) (fun p hp => nwPerm_lt h hp) (fun j _ => ⟨fun p hp => ?_, fun q hq => ?_⟩) hp
  · have := (testBit_applyNW h one_eq_rep (coord j)).1 0 (by omega) p hp
    simpa using this
  · exact (testBit_applyNW h one_eq_rep (coord j)).2 q (by omega)

theorem arrInvNW_entry {NW : Nat} (h : nwValid NW = true) {p : Nat} (hp : p < 4096) :
    arrInvNW NW / 2 ^ (16 * p) % 2 ^ 16 = nwInv NW p := by
  unfold arrInvNW
  refine arr_entry (nwInv NW) (fun p hp => nwInv_lt h hp) (fun j _ => ⟨fun p hp => ?_, fun q hq => ?_⟩) hp
  · have := (testBit_applyInvNW h one_eq_rep (coord j)).1 0 (by omega) p hp
    simpa using this
  · exact (testBit_applyInvNW h one_eq_rep (coord j)).2 q (by omega)

end Fi22

end CFSG.KC.Benes

end

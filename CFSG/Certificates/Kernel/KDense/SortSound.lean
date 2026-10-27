module

public import CFSG.Certificates.Kernel.KDense.Sound
public import CFSG.Certificates.Kernel.BenesSound
import Mathlib.Tactic.Ring.RingNF

public section

namespace CFSG.KC.KDense.SortAux

open CFSG.KC CFSG.KC.MonsterConv.Perm CFSG.KC.Loop CFSG.KC.Benes CFSG.KC.KDense.InitAux

theorem dm {M a r : ℕ} (hr : r < M) : (M * a + r) / M = a ∧ (M * a + r) % M = r := by
  have hM : 0 < M := by omega
  constructor
  · rw [Nat.add_comm, Nat.add_mul_div_left _ _ hM, Nat.div_eq_of_lt hr, Nat.zero_add]
  · rw [Nat.add_comm, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hr]

theorem testBit_ones (W q : ℕ) : (ones W).testBit q = decide (q < W) := by
  rw [Benes.ones_eq, Nat.testBit_two_pow_sub_one]

@[expose] noncomputable def rawStep (rec h j x : ℕ) : ℕ :=
  (fun g => (fun lo => Nat.lor (Nat.land x lo)
      (Nat.shiftRight (Nat.land x (Nat.shiftLeft lo (Nat.mul rec g))) (Nat.mul (Nat.sub rec (nat_lit 1)) g)))
    (Nat.mul (Nat.div (ones (Nat.mul rec (Nat.shiftLeft (nat_lit 1) h)))
        (ones (Nat.mul rec (Nat.shiftLeft g (nat_lit 1))))) (ones g)))
    (Nat.shiftLeft (nat_lit 1) j)

theorem rawPlane_eq (RAW rec n h c b : ℕ) : rawPlane RAW rec n h c b =
    Nat.rec (motive := fun _ => ℕ) (Nat.land (Nat.shiftRight RAW (Nat.add (Nat.mul (nat_lit 32) c) b))
      (Nat.div (ones (Nat.mul rec n)) (ones rec))) (rawStep rec h) h := rfl

@[expose] def RawInv (rec h j : ℕ) (T : ℕ → Bool) (x : ℕ) : Prop :=
  ∀ q, x.testBit q = (decide (q % (rec * 2 ^ j) < 2 ^ j ∧ q / (rec * 2 ^ j) < 2 ^ (h - j)) &&
    T (2 ^ j * (q / (rec * 2 ^ j)) + q % (rec * 2 ^ j)))

theorem rawInv_zero {RAW rec h off : ℕ} (hrec : 0 < rec) :
    RawInv rec h 0 (fun p => RAW.testBit (rec * p + off))
      (Nat.land (Nat.shiftRight RAW off) (Nat.div (ones (Nat.mul rec (2 ^ h))) (ones rec))) := by
  intro q
  have hm := testBit_mul_div (W := rec * 2 ^ h) (L := rec) (n := 2 ^ h) (c := 1) hrec rfl
    (Nat.one_lt_two_pow (by omega)) q
  rw [Nat.one_mul, InitAux.testBit_one] at hm
  simp only [nland, nshr, nmul, ndiv, Benes.ones_eq, Nat.testBit_and, Nat.testBit_shiftRight, hm,
    pow_zero, Nat.mul_one, Nat.sub_zero, Nat.one_mul]
  have e := Nat.div_add_mod q rec
  have h2 : q < rec * 2 ^ h ↔ q / rec < 2 ^ h := by
    rw [Nat.div_lt_iff_lt_mul hrec, Nat.mul_comm]
  rw [Bool.eq_iff_iff]
  simp only [Bool.and_eq_true, decide_eq_true_eq]
  constructor
  · rintro ⟨hb, hlt, h0⟩
    refine ⟨⟨by omega, h2.1 hlt⟩, ?_⟩
    rw [h0, Nat.add_zero] at e ⊢
    rw [e, Nat.add_comm]
    exact hb
  · rintro ⟨⟨h0, hlt⟩, hb⟩
    have h0' : q % rec = 0 := by omega
    rw [h0', Nat.add_zero] at e hb
    rw [e, Nat.add_comm] at hb
    exact ⟨hb, h2.2 hlt, h0'⟩

theorem rawInv_succ {rec h j : ℕ} {T : ℕ → Bool} {x : ℕ} (hrec : 0 < rec) (hj : j < h)
    (hx : RawInv rec h j T x) : RawInv rec h (j + 1) T (rawStep rec h j x) := by
  set G := 2 ^ j with hG
  set L := rec * G with hL
  set P := 2 ^ (h - (j + 1)) with hP
  have hG0 : 0 < G := Nat.two_pow_pos j
  have hGL : G ≤ L := Nat.le_mul_of_pos_left G hrec
  have hP2 : 2 ^ (h - j) = 2 * P := by
    rw [hP, ← Nat.pow_succ']
    congr 1
    omega
  have hL2 : rec * 2 ^ (j + 1) = 2 * L := by rw [hL, hG, Nat.pow_succ]; ring
  have hG2 : 2 ^ (j + 1) = 2 * G := by rw [hG, Nat.pow_succ]; ring
  have hW : rec * 2 ^ h = 2 * L * P := by
    have e : 2 ^ h = 2 * 2 ^ j * 2 ^ (h - (j + 1)) := by
      rw [← Nat.pow_succ', ← Nat.pow_add]
      congr 1
      omega
    rw [hL, hG, hP, e]
    ring
  have hlo : ∀ t, (Nat.mul (Nat.div (ones (Nat.mul rec (Nat.shiftLeft (nat_lit 1) h)))
      (ones (Nat.mul rec (Nat.shiftLeft G (nat_lit 1))))) (ones G)).testBit t =
        (decide (t < 2 * L * P) && decide (t % (2 * L) < G)) := by
    intro t
    have e1 : Nat.shiftLeft (nat_lit 1) h = 2 ^ h := by rw [nshl, Nat.one_shiftLeft]
    have e2 : Nat.shiftLeft G (nat_lit 1) = 2 * G := by
      rw [nshl, Nat.shiftLeft_eq, pow_one, Nat.mul_comm]
    have e3 : rec * (2 * G) = 2 * L := by rw [hL]; ring
    have hc : 2 ^ G - 1 < 2 ^ (2 * L) :=
      lt_two_pow_mono (Nat.sub_lt (Nat.two_pow_pos G) Nat.one_pos) (by omega)
    have := testBit_mul_div (W := rec * 2 ^ h) (L := 2 * L) (n := P) (c := 2 ^ G - 1) (by omega)
      hW hc t
    simp only [nmul, ndiv, e1, e2, e3, Benes.ones_eq]
    rw [Nat.mul_comm ((2 ^ (rec * 2 ^ h) - 1) / (2 ^ (2 * L) - 1)), this, hW,
      Nat.testBit_two_pow_sub_one]
  have hg : Nat.shiftLeft (nat_lit 1) j = G := by rw [nshl, Nat.one_shiftLeft]
  have hRL : Nat.mul (Nat.sub rec (nat_lit 1)) G = L - G := by
    rw [nmul, nsub, hL, Nat.sub_mul, Nat.one_mul]
  have hRG : Nat.mul rec G = L := rfl
  intro q
  unfold rawStep
  simp only [hg]
  generalize Nat.mul (Nat.div (ones (Nat.mul rec (Nat.shiftLeft (nat_lit 1) h)))
      (ones (Nat.mul rec (Nat.shiftLeft G (nat_lit 1))))) (ones G) = lo at hlo
  rw [hRL, hRG]
  simp only [nlor, nland, nshr, nshl, Nat.testBit_or, Nat.testBit_and,
    Nat.testBit_shiftRight, Nat.testBit_shiftLeft, hlo]
  rw [hL2, hG2, ← hP]
  have hq := Nat.div_add_mod q (2 * L)
  generalize q / (2 * L) = a at hq ⊢
  generalize hβ : q % (2 * L) = β at hq ⊢
  have hβ2 : β < 2 * L := by rw [← hβ]; exact Nat.mod_lt _ (by omega)
  subst hq
  have hX : ∀ t, x.testBit t = (decide (t % L < G ∧ t / L < 2 * P) && T (G * (t / L) + t % L)) := by
    intro t
    rw [hx t, hP2]
  have hr1 : ∀ γ, γ < 2 * L → (2 * L * a + γ < 2 * L * P ↔ a < P) := by
    intro γ hγ
    constructor
    · intro h
      by_contra hc
      have : 2 * L * P ≤ 2 * L * a := Nat.mul_le_mul_left _ (by omega)
      omega
    · intro h
      have : 2 * L * (a + 1) ≤ 2 * L * P := Nat.mul_le_mul_left _ h
      rw [Nat.mul_succ] at this
      omega
  simp only [hr1 β hβ2]
  rcases Nat.lt_or_ge β G with h1 | h1
  ·
    have e : 2 * L * a + β = L * (2 * a) + β := by ring
    obtain ⟨d1, m1⟩ := dm (M := L) (a := 2 * a) (r := β) (by omega)
    have hxq := hX (L * (2 * a) + β)
    rw [d1, m1, ← e] at hxq
    rw [hxq]
    have hsec : (decide (L - G + (2 * L * a + β) ≥ L) &&
        (decide (L - G + (2 * L * a + β) - L < 2 * L * P) &&
          decide ((L - G + (2 * L * a + β) - L) % (2 * L) < G))) = false := by
      rcases Nat.eq_zero_or_pos a with ha | ha
      · subst ha
        have hn : ¬ (L - G + (2 * L * 0 + β) ≥ L) := by omega
        rw [decide_eq_false hn]
        rfl
      · have e2 : L - G + (2 * L * a + β) - L = 2 * L * (a - 1) + (2 * L + β - G) := by
          have : 2 * L * a = 2 * L * (a - 1) + 2 * L := by
            rw [← Nat.mul_succ]
            congr 1
            omega
          omega
        have hn : ¬ (2 * L + β - G < G) := by omega
        rw [e2, (dm (a := a - 1) (by omega : 2 * L + β - G < 2 * L)).2, decide_eq_false hn]
        simp
    rw [hsec, Bool.and_false, Bool.or_false]
    have e3 : G * (2 * a) + β = 2 * G * a + β := by ring
    rw [e3]
    have h1' : β < 2 * G := by omega
    have ha2 : 2 * a < 2 * P ↔ a < P := by omega
    simp only [ha2]
    by_cases ha : a < P <;> simp [ha, h1, h1']
  ·
    have hn : ¬ β < G := by omega
    rw [decide_eq_false hn]
    simp only [Bool.and_false, Bool.false_or]
    rcases Nat.lt_or_ge β (2 * G) with h2 | h2
    ·
      have hL3 : L * (2 * a + 1) = 2 * L * a + L := by ring
      have e : L - G + (2 * L * a + β) = L * (2 * a + 1) + (β - G) := by omega
      obtain ⟨d1, m1⟩ := dm (M := L) (a := 2 * a + 1) (r := β - G) (by omega)
      have hxt := hX (L - G + (2 * L * a + β))
      rw [e, d1, m1] at hxt
      rw [e, hxt]
      have e2 : L * (2 * a + 1) + (β - G) - L = 2 * L * a + (β - G) := by omega
      have hβG : β - G < 2 * L := by omega
      rw [e2, (dm (a := a) hβG).2]
      simp only [hr1 (β - G) hβG]
      have e3 : G * (2 * a + 1) + (β - G) = 2 * G * a + β := by
        have : G * (2 * a + 1) = 2 * G * a + G := by ring
        omega
      rw [e3]
      have h3 : β - G < G := by omega
      have h4 : L * (2 * a + 1) + (β - G) ≥ L := by omega
      have ha2 : 2 * a + 1 < 2 * P ↔ a < P := by omega
      simp only [ha2]
      by_cases ha : a < P <;> simp [ha, h2, h3, h4]
    ·
      have hn2 : ¬ (β < 2 * G ∧ a < P) := by omega
      rw [decide_eq_false hn2]
      have e2 : L - G + (2 * L * a + β) - L = 2 * L * a + (β - G) := by omega
      have hn3 : ¬ (β - G < G) := by omega
      rw [e2, (dm (a := a) (by omega : β - G < 2 * L)).2, decide_eq_false hn3]
      simp

theorem testBit_rawPlane {RAW rec n h b : ℕ} (hrec : 0 < rec) (hn : n = 2 ^ h) (q : ℕ) :
    (rawPlane RAW rec n h 0 b).testBit q = (decide (q < n) && RAW.testBit (rec * q + b)) := by
  subst hn
  rw [rawPlane_eq]
  have e0 : Nat.add (Nat.mul 32 0) b = b := by simp
  rw [e0]
  have key : ∀ j, j ≤ h → RawInv rec h j (fun p => RAW.testBit (rec * p + b))
      (Nat.rec (motive := fun _ => ℕ) (Nat.land (Nat.shiftRight RAW b)
        (Nat.div (ones (Nat.mul rec (2 ^ h))) (ones rec))) (rawStep rec h) j) := by
    intro j
    induction j with
    | zero => exact fun _ => rawInv_zero hrec
    | succ j ih => exact fun hj => rawInv_succ hrec (by omega) (ih (by omega))
  rw [key h le_rfl q, Nat.sub_self, pow_zero]
  by_cases hq : q < 2 ^ h
  · have hq' : q < rec * 2 ^ h := lt_of_lt_of_le hq (Nat.le_mul_of_pos_left _ hrec)
    rw [Nat.div_eq_of_lt hq', Nat.mod_eq_of_lt hq']
    simp [hq]
  · have hn : ¬ (q % (rec * 2 ^ h) < 2 ^ h ∧ q / (rec * 2 ^ h) < 1) := by
      rintro ⟨h1, h2⟩
      have h0 : q / (rec * 2 ^ h) = 0 := Nat.lt_one_iff.1 h2
      have e := Nat.div_add_mod q (rec * 2 ^ h)
      rw [h0, Nat.mul_zero, Nat.zero_add] at e
      rw [e] at h1
      exact hq h1
    rw [decide_eq_false hn, Bool.false_and, decide_eq_false hq, Bool.false_and]

theorem rawPlane_lt {RAW rec n h b : ℕ} (hrec : 0 < rec) (hn : n = 2 ^ h) :
    rawPlane RAW rec n h 0 b < 2 ^ n :=
  Nat.lt_pow_two_of_testBit _ fun q hq => by
    have hq' : ¬ q < n := by omega
    rw [testBit_rawPlane hrec hn]
    simp [hq']

@[expose] def lexV (D : ℕ → ℕ → ℕ) (B : ℕ) : ℕ → ℕ → ℕ
  | 0, _ => 0
  | j + 1, r => lexV D B j r * B + D j r

theorem lexV_congr (D : ℕ → ℕ → ℕ) (B : ℕ) {r r' : ℕ} :
    ∀ n, (∀ j < n, D j r = D j r') → lexV D B n r = lexV D B n r'
  | 0, _ => rfl
  | n + 1, h => by
    rw [lexV, lexV, lexV_congr D B n (fun j hj => h j (by omega)), h n (by omega)]

theorem digit_lt_iff {a a' d d' B : ℕ} (hd : d < B) (hd' : d' < B) :
    a * B + d < a' * B + d' ↔ a < a' ∨ (a = a' ∧ d < d') := by
  constructor
  · intro h
    rcases Nat.lt_trichotomy a a' with h1 | h1 | h1
    · exact Or.inl h1
    · subst h1
      exact Or.inr ⟨rfl, by omega⟩
    · have : (a' + 1) * B ≤ a * B := Nat.mul_le_mul_right _ h1
      rw [Nat.succ_mul] at this
      omega
  · rintro (h | ⟨rfl, h⟩)
    · have : (a + 1) * B ≤ a' * B := Nat.mul_le_mul_right _ h
      rw [Nat.succ_mul] at this
      omega
    · omega

theorem digit_eq_iff {a a' d d' B : ℕ} (hd : d < B) (hd' : d' < B) :
    a * B + d = a' * B + d' ↔ a = a' ∧ d = d' := by
  constructor
  · intro h
    have h1 := congrArg (· / B) h
    have h2 := congrArg (· % B) h
    simp only [Nat.mul_comm _ B] at h1 h2
    rw [(dm hd).1, (dm hd').1] at h1
    rw [(dm hd).2, (dm hd').2] at h2
    exact ⟨h1, h2⟩
  · rintro ⟨rfl, rfl⟩
    rfl

theorem lex_inv {M B N : ℕ} (D : ℕ → ℕ → ℕ) (hD : ∀ j < N, ∀ r, D j r < B) (st : ℕ → ℕ × ℕ)
    (h0 : ∀ r < M, (st 0).1.testBit r = false ∧ (st 0).2.testBit r = true)
    (hs : ∀ j < N, ∀ r < M, (st (j + 1)).1.testBit r =
        ((st j).1.testBit r || ((st j).2.testBit r && decide (D j r < D j (r + 1)))) ∧
      (st (j + 1)).2.testBit r = ((st j).2.testBit r && decide (D j r = D j (r + 1)))) :
    ∀ n ≤ N, ∀ r < M, (st n).1.testBit r = decide (lexV D B n r < lexV D B n (r + 1)) ∧
      (st n).2.testBit r = decide (lexV D B n r = lexV D B n (r + 1))
  | 0, _, r, hr => by
    rw [(h0 r hr).1, (h0 r hr).2]
    simp [lexV]
  | n + 1, hn, r, hr => by
    obtain ⟨ih1, ih2⟩ := lex_inv D hD st h0 hs n (by omega) r hr
    obtain ⟨e1, e2⟩ := hs n (by omega) r hr
    rw [e1, e2, ih1, ih2]
    have hl := digit_lt_iff (a := lexV D B n r) (a' := lexV D B n (r + 1))
      (hD n (by omega) r) (hD n (by omega) (r + 1))
    have he := digit_eq_iff (a := lexV D B n r) (a' := lexV D B n (r + 1))
      (hD n (by omega) r) (hD n (by omega) (r + 1))
    simp only [lexV]
    constructor
    · rw [Bool.eq_iff_iff]
      simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq, hl]
    · rw [Bool.eq_iff_iff]
      simp only [Bool.and_eq_true, decide_eq_true_eq, he]

theorem lexV_inj {N : ℕ} {f : ℕ → ℕ} (h : ∀ r, r + 1 < N → f r < f (r + 1)) :
    ∀ r r', r < N → r' < N → f r = f r' → r = r' := by
  have mono : ∀ k r, r + k + 1 < N → f r < f (r + k + 1) := by
    intro k
    induction k with
    | zero => exact fun r hr => h r hr
    | succ k ih =>
      intro r hr
      exact lt_trans (ih r (by omega)) (h (r + k + 1) (by omega))
  intro r r' hr hr' e
  rcases Nat.lt_trichotomy r r' with h1 | h1 | h1
  · have := mono (r' - r - 1) r (by omega)
    rw [show r + (r' - r - 1) + 1 = r' by omega, e] at this
    exact absurd this (lt_irrefl _)
  · exact h1
  · have := mono (r - r' - 1) r' (by omega)
    rw [show r' + (r - r' - 1) + 1 = r by omega, e] at this
    exact absurd this (lt_irrefl _)

theorem SX_pow : SX = 2 ^ 17 := rfl

theorem testBit_netP1 {N : ℕ} (hN : netOK 17 N = true) (x : ℕ) {r : ℕ} (hr : r < SX) :
    (netP SX 17 1 N x).testBit r = x.testBit (benesPerm 17 N r) := by
  have := (testBit_netP (n := 1) SX_pow hN x).1 0 Nat.zero_lt_one r hr
  simpa using this

theorem validX_perm {N : ℕ} (hN : netOK 17 N = true) (hV : netP SX 17 1 N validX = ones 98280)
    {q : ℕ} (hq : q < 98280) :
    benesInv 17 N (xposK q) < 98280 ∧ benesPerm 17 N (benesInv 17 N (xposK q)) = xposK q := by
  have hv := stagesValid_of_netOK hN
  have hx : xposK q < 2 ^ 17 := by
    have := xposK_lt' hq
    rwa [SX_pow] at this
  have hr := benesInv_lt hv hx
  have e := benesPerm_benesInv hv (xposK q)
  refine ⟨?_, e⟩
  have h1 := testBit_netP1 hN validX (r := benesInv 17 N (xposK q)) (by rw [SX_pow]; exact hr)
  rw [hV, e, xposK_mem hq, testBit_ones] at h1
  exact of_decide_eq_true h1

end CFSG.KC.KDense.SortAux

end

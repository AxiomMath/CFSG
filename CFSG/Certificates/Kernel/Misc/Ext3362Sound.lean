module

public import Certificates.Data.Kernel.Misc.Ext3362
public import CFSG.LocalAnalysis.ComponentInitial.ChevSp6EpsOneModuleData

public section

namespace CFSG.KC.Misc.Ext

open CFSG.LocalAnalysis.ComponentInitial.ChevSp6EpsOne.ExtOne CFSG.KC.Ord CFSG.KC.LQT.P

@[expose] def extCheckG (a b : ℕ) : Bool :=
  (List.range 512).all fun x => !(pmulN (a, x) (a, x) == (oneN, 0)) ||
    (List.range 512).all fun y => !(ppowN (b, y) 3 == (oneN, 0)) ||
      !(ppowN (pmulN (a, x) (b, y)) 7 == (oneN, 0)) ||
      (List.range 512).any fun m => x == add9 (mul9 a m) (mul9 m a) && y == add9 (mul9 b m) (mul9 m b)

theorem extCheck_eq : extCheck = extCheckG aN bN := rfl

theorem bitK_eq (x k : ℕ) : bitK x k = x / 2 ^ k % 2 := by
  change (x >>> k) &&& 1 = _
  rw [Nat.and_one_is_mod, Nat.shiftRight_eq_div_pow]

theorem rowK_eq (y k : ℕ) : rowK y k = y / 2 ^ (3 * k) % 8 := by
  change (y >>> (3 * k)) &&& (2 ^ 3 - 1) = _
  rw [Nat.and_two_pow_sub_one_eq_mod, Nat.shiftRight_eq_div_pow]

theorem prodRow_eq (x y i : ℕ) : prodRow x y i =
    (x / 2 ^ (3 * i) % 2 * (y % 8)) ^^^ ((x / 2 ^ (3 * i + 1) % 2 * (y / 8 % 8)) ^^^
      (x / 2 ^ (3 * i + 2) % 2 * (y / 64 % 8))) := by
  have e0 : rowK y 0 = y % 8 := by rw [rowK_eq]; simp
  have e1 : rowK y 1 = y / 8 % 8 := by rw [rowK_eq]
  have e2 : rowK y 2 = y / 64 % 8 := by rw [rowK_eq]
  unfold prodRow
  rw [e0, e1, e2, bitK_eq, bitK_eq, bitK_eq]
  rfl

theorem decomp {x : ℕ} (hx : x < 512) :
    ∃ u0 u1 u2, u0 < 8 ∧ u1 < 8 ∧ u2 < 8 ∧ x = u0 + 8 * u1 + 64 * u2 :=
  ⟨x % 8, x / 8 % 8, x / 64, by omega, by omega, by omega, by omega⟩

theorem nb_split {u0 u1 u2 : ℕ} (h0 : u0 < 8) (h1 : u1 < 8) (_h2 : u2 < 8) :
    nb (u0 + 8 * u1 + 64 * u2) 0 = nb u0 0 ∧ nb (u0 + 8 * u1 + 64 * u2) 1 = nb u0 1 ∧
    nb (u0 + 8 * u1 + 64 * u2) 2 = nb u0 2 ∧ nb (u0 + 8 * u1 + 64 * u2) 3 = nb u1 0 ∧
    nb (u0 + 8 * u1 + 64 * u2) 4 = nb u1 1 ∧ nb (u0 + 8 * u1 + 64 * u2) 5 = nb u1 2 ∧
    nb (u0 + 8 * u1 + 64 * u2) 6 = nb u2 0 ∧ nb (u0 + 8 * u1 + 64 * u2) 7 = nb u2 1 ∧
    nb (u0 + 8 * u1 + 64 * u2) 8 = nb u2 2 := by
  simp only [nb, Nat.reducePow]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> omega

theorem split_divs {u0 u1 u2 : ℕ} (h0 : u0 < 8) (h1 : u1 < 8) (h2 : u2 < 8) :
    (u0 + 8 * u1 + 64 * u2) % 8 = u0 ∧ (u0 + 8 * u1 + 64 * u2) / 8 % 8 = u1 ∧
    (u0 + 8 * u1 + 64 * u2) / 64 % 8 = u2 := by
  refine ⟨?_, ?_, ?_⟩ <;> omega

theorem row_eq : ∀ u < 8, ∀ v0 < 8, ∀ v1 < 8, ∀ v2 < 8,
    dot3 (nb u 0) (nb u 1) (nb u 2) (nb v0 0) (nb v1 0) (nb v2 0) +
      2 * dot3 (nb u 0) (nb u 1) (nb u 2) (nb v0 1) (nb v1 1) (nb v2 1) +
      4 * dot3 (nb u 0) (nb u 1) (nb u 2) (nb v0 2) (nb v1 2) (nb v2 2) =
    (nb u 0 * v0) ^^^ ((nb u 1 * v1) ^^^ (nb u 2 * v2)) := by
  decide +kernel

theorem xrow_lt : ∀ u < 8, ∀ v0 < 8, ∀ v1 < 8, ∀ v2 < 8,
    (nb u 0 * v0) ^^^ ((nb u 1 * v1) ^^^ (nb u 2 * v2)) < 8 := by
  decide +kernel

theorem lor_eq : ∀ a < 8, ∀ b < 8, ∀ c < 8,
    Nat.lor a (Nat.lor (Nat.shiftLeft b 3) (Nat.shiftLeft c 6)) = a + 8 * b + 64 * c := by
  decide +kernel

theorem add_row : ∀ u < 8, ∀ v < 8,
    (nb u 0 + nb v 0) % 2 + 2 * ((nb u 1 + nb v 1) % 2) + 4 * ((nb u 2 + nb v 2) % 2) =
      u ^^^ v := by
  decide +kernel

theorem xor_split {a b c d k : ℕ} (ha : a < 2 ^ k) (hc : c < 2 ^ k) :
    (2 ^ k * b + a) ^^^ (2 ^ k * d + c) = 2 ^ k * (b ^^^ d) + (a ^^^ c) := by
  apply Nat.eq_of_testBit_eq
  intro j
  rw [Nat.testBit_xor, Nat.testBit_two_pow_mul_add _ ha, Nat.testBit_two_pow_mul_add _ hc,
    Nat.testBit_two_pow_mul_add _ (Nat.xor_lt_two_pow ha hc), Nat.testBit_xor]
  split <;> simp

theorem xor_lt512 {x y : ℕ} (hx : x < 512) (hy : y < 512) : x ^^^ y < 512 :=
  Nat.xor_lt_two_pow (n := 9) hx hy

theorem dot3_lt (a b c d e f : ℕ) : dot3 a b c d e f < 2 := Nat.mod_lt _ (by decide)

theorem mul9_lt (x y : ℕ) : mul9 x y < 512 := by
  unfold mul9
  have := dot3_lt
  have h0 := this (nb x 0) (nb x 1) (nb x 2) (nb y 0) (nb y 3) (nb y 6)
  have h1 := this (nb x 0) (nb x 1) (nb x 2) (nb y 1) (nb y 4) (nb y 7)
  have h2 := this (nb x 0) (nb x 1) (nb x 2) (nb y 2) (nb y 5) (nb y 8)
  have h3 := this (nb x 3) (nb x 4) (nb x 5) (nb y 0) (nb y 3) (nb y 6)
  have h4 := this (nb x 3) (nb x 4) (nb x 5) (nb y 1) (nb y 4) (nb y 7)
  have h5 := this (nb x 3) (nb x 4) (nb x 5) (nb y 2) (nb y 5) (nb y 8)
  have h6 := this (nb x 6) (nb x 7) (nb x 8) (nb y 0) (nb y 3) (nb y 6)
  have h7 := this (nb x 6) (nb x 7) (nb x 8) (nb y 1) (nb y 4) (nb y 7)
  have h8 := this (nb x 6) (nb x 7) (nb x 8) (nb y 2) (nb y 5) (nb y 8)
  omega

theorem mulK_eq {x y : ℕ} (hx : x < 512) (hy : y < 512) : mulK x y = mul9 x y := by
  obtain ⟨u0, u1, u2, hu0, hu1, hu2, rfl⟩ := decomp hx
  obtain ⟨v0, v1, v2, hv0, hv1, hv2, rfl⟩ := decomp hy
  obtain ⟨a0, a1, a2, a3, a4, a5, a6, a7, a8⟩ := nb_split hu0 hu1 hu2
  obtain ⟨b0, b1, b2, b3, b4, b5, b6, b7, b8⟩ := nb_split hv0 hv1 hv2
  obtain ⟨d0, d1, d2⟩ := split_divs hv0 hv1 hv2
  have p0 : prodRow (u0 + 8 * u1 + 64 * u2) (v0 + 8 * v1 + 64 * v2) 0 =
      (nb u0 0 * v0) ^^^ ((nb u0 1 * v1) ^^^ (nb u0 2 * v2)) := by
    rw [prodRow_eq, d0, d1, d2, ← a0, ← a1, ← a2]
    rfl
  have p1 : prodRow (u0 + 8 * u1 + 64 * u2) (v0 + 8 * v1 + 64 * v2) 1 =
      (nb u1 0 * v0) ^^^ ((nb u1 1 * v1) ^^^ (nb u1 2 * v2)) := by
    rw [prodRow_eq, d0, d1, d2, ← a3, ← a4, ← a5]
    rfl
  have p2 : prodRow (u0 + 8 * u1 + 64 * u2) (v0 + 8 * v1 + 64 * v2) 2 =
      (nb u2 0 * v0) ^^^ ((nb u2 1 * v1) ^^^ (nb u2 2 * v2)) := by
    rw [prodRow_eq, d0, d1, d2, ← a6, ← a7, ← a8]
    rfl
  unfold mulK
  rw [p0, p1, p2, lor_eq _ (xrow_lt _ hu0 _ hv0 _ hv1 _ hv2) _ (xrow_lt _ hu1 _ hv0 _ hv1 _ hv2) _
    (xrow_lt _ hu2 _ hv0 _ hv1 _ hv2), ← row_eq _ hu0 _ hv0 _ hv1 _ hv2,
    ← row_eq _ hu1 _ hv0 _ hv1 _ hv2, ← row_eq _ hu2 _ hv0 _ hv1 _ hv2]
  unfold mul9
  rw [a0, a1, a2, a3, a4, a5, a6, a7, a8, b0, b1, b2, b3, b4, b5, b6, b7, b8]
  omega

theorem add9_eq {x y : ℕ} (hx : x < 512) (hy : y < 512) : add9 x y = x ^^^ y := by
  obtain ⟨u0, u1, u2, hu0, hu1, hu2, rfl⟩ := decomp hx
  obtain ⟨v0, v1, v2, hv0, hv1, hv2, rfl⟩ := decomp hy
  obtain ⟨a0, a1, a2, a3, a4, a5, a6, a7, a8⟩ := nb_split hu0 hu1 hu2
  obtain ⟨b0, b1, b2, b3, b4, b5, b6, b7, b8⟩ := nb_split hv0 hv1 hv2
  have eU : u0 + 8 * u1 + 64 * u2 = 2 ^ 3 * (2 ^ 3 * u2 + u1) + u0 := by omega
  have eV : v0 + 8 * v1 + 64 * v2 = 2 ^ 3 * (2 ^ 3 * v2 + v1) + v0 := by omega
  have r0 := add_row _ hu0 _ hv0
  have r1 := add_row _ hu1 _ hv1
  have r2 := add_row _ hu2 _ hv2
  unfold add9
  rw [a0, a1, a2, a3, a4, a5, a6, a7, a8, b0, b1, b2, b3, b4, b5, b6, b7, b8, eU, eV,
    xor_split (k := 3) hu0 hv0, xor_split (k := 3) hu1 hv1]
  omega

theorem pk_eq {g : ℕ} (hg : g < 512) (X : ℕ) : pk g X = g + 512 * X := by
  change g ||| X <<< 9 = _
  rw [Nat.or_comm, ← Nat.shiftLeft_add_eq_or_of_lt (i := 9) hg, Nat.shiftLeft_eq]
  omega

theorem lo_pk {g : ℕ} (hg : g < 512) (X : ℕ) : lo (pk g X) = g := by
  rw [pk_eq hg]
  change (g + 512 * X) &&& (2 ^ 9 - 1) = g
  rw [Nat.and_two_pow_sub_one_eq_mod]
  omega

theorem hi_pk {g : ℕ} (hg : g < 512) (X : ℕ) : hi (pk g X) = X := by
  rw [pk_eq hg]
  change (g + 512 * X) >>> 9 = X
  rw [Nat.shiftRight_eq_div_pow]
  omega

noncomputable def E (p : ℕ × ℕ) : ℕ := pk p.1 p.2

def Sm (p : ℕ × ℕ) : Prop := p.1 < 512 ∧ p.2 < 512

theorem E_inj {p q : ℕ × ℕ} (hp : Sm p) (hq : Sm q) (h : E p = E q) : p = q := by
  unfold E at h
  rw [pk_eq hp.1, pk_eq hq.1] at h
  have := hp.1
  have := hq.1
  ext <;> omega

theorem sm_one : Sm (oneN, 0) := ⟨by unfold oneN; decide, by decide⟩

theorem sm_pmulN {p q : ℕ × ℕ} : Sm (pmulN p q) := by
  unfold pmulN
  refine ⟨mul9_lt _ _, ?_⟩
  rw [add9_eq (mul9_lt _ _) (mul9_lt _ _)]
  exact xor_lt512 (mul9_lt _ _) (mul9_lt _ _)

theorem pmulK_E {p q : ℕ × ℕ} (hp : Sm p) (hq : Sm q) : pmulK (E p) (E q) = E (pmulN p q) := by
  unfold pmulK E pmulN
  rw [lo_pk hp.1, lo_pk hq.1, hi_pk hp.1, hi_pk hq.1, mulK_eq hp.1 hq.1, mulK_eq hp.1 hq.2,
    mulK_eq hp.2 hq.1, add9_eq (mul9_lt _ _) (mul9_lt _ _)]
  rfl

theorem sm_ppowN (p : ℕ × ℕ) : ∀ n, Sm (ppowN p n)
  | 0 => sm_one
  | _ + 1 => sm_pmulN

theorem E_one : E (oneN, 0) = 273 := by
  unfold E
  rw [pk_eq (by unfold oneN; decide)]
  rfl

theorem ppowK_E {p : ℕ × ℕ} (hp : Sm p) : ∀ n, ppowK (E p) n = E (ppowN p n)
  | 0 => by
    change 273 = E (oneN, 0)
    rw [E_one]
  | n + 1 => by
    change pmulK (ppowK (E p) n) (E p) = E (pmulN (ppowN p n) p)
    rw [ppowK_E hp n, pmulK_E (sm_ppowN p n) hp]

theorem beq_E {p q : ℕ × ℕ} (hp : Sm p) (hq : Sm q) :
    Nat.beq (E p) (E q) = (p == q) := by
  by_cases h : p = q
  · subst h
    simp [Nat.beq_refl]
  · have h1 : (p == q) = false := by simpa using h
    rw [h1]
    exact Bool.eq_false_iff.mpr fun e => h (E_inj hp hq (Nat.eq_of_beq_eq_true e))

theorem relAK_eq {a x : ℕ} (ha : a < 512) (hx : x < 512) :
    relAK a x = (pmulN (a, x) (a, x) == (oneN, 0)) := by
  unfold relAK
  change Nat.beq (pmulK (E (a, x)) (E (a, x))) 273 = _
  rw [← E_one, pmulK_E ⟨ha, hx⟩ ⟨ha, hx⟩, beq_E sm_pmulN sm_one]

theorem relBK_eq {b y : ℕ} (hb : b < 512) (hy : y < 512) :
    relBK b y = (ppowN (b, y) 3 == (oneN, 0)) := by
  unfold relBK
  change Nat.beq (ppowK (E (b, y)) 3) 273 = _
  rw [← E_one, ppowK_E ⟨hb, hy⟩, beq_E (sm_ppowN _ _) sm_one]

theorem relABK_eq {a b x y : ℕ} (ha : a < 512) (hb : b < 512) (hx : x < 512) (hy : y < 512) :
    relABK a b x y = (ppowN (pmulN (a, x) (b, y)) 7 == (oneN, 0)) := by
  unfold relABK
  change Nat.beq (ppowK (pmulK (E (a, x)) (E (b, y))) 7) 273 = _
  rw [← E_one, pmulK_E ⟨ha, hx⟩ ⟨hb, hy⟩, ppowK_E sm_pmulN, beq_E (sm_ppowN _ _) sm_one]

theorem andB_iff {a b : Bool} : andB a b = true ↔ a = true ∧ b = true := by
  cases a <;> cases b <;> simp [andB]

theorem orB_iff {a b : Bool} : orB a b = true ↔ a = true ∨ b = true := by
  cases a <;> cases b <;> simp [orB]

theorem impB_iff {a b : Bool} : impB a b = true ↔ (a = true → b = true) := by
  cases a <;> cases b <;> simp [impB]

theorem allN_iff (m : ℕ) (f : ℕ → Bool) : allN m f = true ↔ ∀ i < m, f i = true := by
  induction m with
  | zero => exact ⟨fun _ i hi => absurd hi (Nat.not_lt_zero _), fun _ => rfl⟩
  | succ m ih =>
    change andB (f m) (allN m f) = true ↔ _
    rw [andB_iff, ih]
    constructor
    · rintro ⟨h1, h2⟩ i hi
      rcases Nat.lt_succ_iff_lt_or_eq.mp hi with h | h
      · exact h2 i h
      · exact h ▸ h1
    · intro h
      exact ⟨h m (Nat.lt_succ_self m), fun i hi => h i (Nat.lt_succ_of_lt hi)⟩

theorem allL_iff (l : List ℕ) (f : ℕ → Bool) : allL l f = true ↔ ∀ x ∈ l, f x = true := by
  induction l with
  | nil => simp [allL]
  | cons x t ih =>
    change andB (f x) (allL t f) = true ↔ _
    rw [andB_iff, ih]
    simp

theorem anyL_iff (l : List ℕ) (f : ℕ → Bool) : anyL l f = true ↔ ∃ x ∈ l, f x = true := by
  induction l with
  | nil => simp [anyL]
  | cons x t ih =>
    change orB (f x) (anyL t f) = true ↔ _
    rw [orB_iff, ih]
    simp

theorem memN_iff (x : ℕ) (l : List ℕ) : memN x l = true ↔ x ∈ l := by
  have e : memN x l = List.rec (motive := fun _ => Bool) false
      (fun z _ ih => orB (Nat.beq x z) ih) l := by
    unfold memN
    cases x <;> rfl
  rw [e]
  clear e
  induction l with
  | nil => simp
  | cons z t ih =>
    change orB (Nat.beq x z) _ = true ↔ _
    rw [orB_iff, Nat.beq_eq, List.mem_cons]
    exact or_congr Iff.rfl ih

theorem beq_iff' {x y : ℕ} : Nat.beq x y = true ↔ x = y := by
  rw [Nat.beq_eq]

theorem c3362_sound {a b : ℕ} {XS YS T : List ℕ} (h : c3362 a b XS YS T = true) :
    extCheckG a b = true := by
  unfold c3362 at h
  simp only [andB_iff, allN_iff, allL_iff, impB_iff, anyL_iff, memN_iff] at h
  obtain ⟨⟨ha, hb⟩, hX, hY, hT, hXY⟩ := h
  have ha : a < 512 := Nat.le_of_ble_eq_true ha
  have hb : b < 512 := Nat.le_of_ble_eq_true hb
  unfold extCheckG
  simp only [List.all_eq_true, List.mem_range, Bool.or_eq_true, Bool.not_eq_true',
    List.any_eq_true]
  intro x hx
  by_cases hA : (pmulN (a, x) (a, x) == (oneN, 0)) = false
  · exact Or.inl hA
  right
  have hA : relAK a x = true := by
    rw [relAK_eq ha hx]
    simpa using hA
  intro y hy
  by_cases hB : (ppowN (b, y) 3 == (oneN, 0)) = false
  · exact Or.inl (Or.inl hB)
  have hB : relBK b y = true := by
    rw [relBK_eq hb hy]
    simpa using hB
  by_cases hAB : (ppowN (pmulN (a, x) (b, y)) 7 == (oneN, 0)) = false
  · exact Or.inl (Or.inr hAB)
  have hAB : relABK a b x y = true := by
    rw [relABK_eq ha hb hx hy]
    simpa using hAB
  right
  obtain ⟨t, ht, -, hc⟩ := hXY x (hX x hx hA) y (hY y hy hB) hAB
  have hm := Nat.le_of_ble_eq_true (hT t ht)
  refine ⟨Nat.shiftRight t 18, hm, ?_⟩
  unfold cobK at hc
  rw [andB_iff, beq_iff', beq_iff'] at hc
  obtain ⟨h1, h2⟩ := hc
  rw [Bool.and_eq_true, beq_iff_eq, beq_iff_eq, add9_eq (mul9_lt _ _) (mul9_lt _ _),
    add9_eq (mul9_lt _ _) (mul9_lt _ _), ← mulK_eq ha hm, ← mulK_eq hm ha, ← mulK_eq hb hm,
    ← mulK_eq hm hb]
  exact ⟨h1, h2⟩

end CFSG.KC.Misc.Ext

end

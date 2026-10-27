module

public import CFSG.LieType.Ree.SmallReeFrattini
public import CFSG.LieType.Ree.SmallReeBorelCosetAction
public import CFSG.LocalAnalysis.ComponentInitial.CoprimeSeriesCoverTrivialPrime
public import CFSG.LieType.Steinberg.CentralExt.FiniteFieldPairing

public section

namespace CFSG.LieType.Steinberg.CentralExt.SmallReeClosed

open CFSG.LieType.Ree CFSG.LieType.Ree.ReeTag CFSG.Blueprint.Chevalley

theorem dvd_pow_sub_pow_mod (f n : ℕ) : ((3 : ℤ) ^ f - 1) ∣ (3 : ℤ) ^ n - 3 ^ (n % f) := by
  have h : (3 : ℤ) ^ n = ((3 : ℤ) ^ f) ^ (n / f) * 3 ^ (n % f) := by
    rw [← pow_mul, ← pow_add, Nat.div_add_mod]
  rw [h, ← sub_one_mul]
  apply dvd_mul_of_dvd_left
  simpa using sub_dvd_pow_sub_pow ((3 : ℤ) ^ f) 1 (n / f)

theorem three_pow_mul_le {e f : ℕ} (h : e < f) : (3 : ℤ) ^ e * 3 ≤ 3 ^ f := by
  rw [← pow_succ]
  exact pow_le_pow_right₀ (by norm_num) h

theorem odd_three_pow (e : ℕ) : Odd ((3 : ℤ) ^ e) := Odd.pow (by decide)

theorem eq_of_pow_add_two_mul_pow {x y z : ℕ} (h : 3 ^ x + 2 * 3 ^ y = 3 ^ z) :
    x = y ∧ z = x + 1 := by
  rcases lt_trichotomy x y with hxy | rfl | hxy
  · exfalso
    have h1 : 3 ^ x < 3 ^ y := Nat.pow_lt_pow_right (by norm_num) hxy
    have h0 : 0 < 3 ^ x := by positivity
    have h2 : 3 ^ y < 3 ^ z := by omega
    have h3 : 3 ^ z < 3 ^ (y + 1) := by rw [pow_succ]; omega
    have h4 := (Nat.pow_lt_pow_iff_right (by norm_num : 1 < 3)).1 h2
    have h5 := (Nat.pow_lt_pow_iff_right (by norm_num : 1 < 3)).1 h3
    omega
  · refine ⟨rfl, Nat.pow_right_injective (by norm_num : 2 ≤ 3) ?_⟩
    change 3 ^ z = 3 ^ (x + 1)
    rw [pow_succ]
    omega
  · exfalso
    have h1 : 3 ^ (y + 1) ≤ 3 ^ x := Nat.pow_le_pow_right (by norm_num) hxy
    rw [pow_succ] at h1
    have h2 : 3 ^ x < 3 ^ z := by
      have : 0 < 3 ^ y := by positivity
      omega
    have h3 : 3 ^ z < 3 ^ (x + 1) := by rw [pow_succ]; omega
    have h4 := (Nat.pow_lt_pow_iff_right (by norm_num : 1 < 3)).1 h2
    have h5 := (Nat.pow_lt_pow_iff_right (by norm_num : 1 < 3)).1 h3
    omega



def wt (a : ℕ) : ℕ → ℤ
  | 0 => 3 ^ a
  | 1 => 1 - 3 ^ a
  | _ => 2 * 3 ^ a - 1

theorem three_pow_odd (a : ℕ) : (3 : ℤ) ^ (2 * a + 1) = 3 * ((3 : ℤ) ^ a) ^ 2 := by
  ring

theorem mod_cases {n f : ℕ} (h : n < 2 * f) : n % f = n ∨ n % f + f = n := by
  rcases Nat.lt_or_ge n f with h1 | h1
  · exact Or.inl (Nat.mod_eq_of_lt h1)
  · right
    rw [Nat.mod_eq_sub_mod h1, Nat.mod_eq_of_lt (by omega)]
    omega

theorem not_dvd_00 {a k l : ℕ} (ha : 1 ≤ a) (hk : k < 2 * a + 1) (hl : l < 2 * a + 1) :
    ¬ ((3 : ℤ) ^ (2 * a + 1) - 1) ∣ 3 ^ k * 3 ^ a + 3 ^ l * 3 ^ a := by
  intro h
  have hc : IsCoprime ((3 : ℤ) ^ (2 * a + 1) - 1) (3 ^ a) :=
    ⟨-1, 3 * 3 ^ a, by rw [three_pow_odd]; ring⟩
  have h1 : ((3 : ℤ) ^ (2 * a + 1) - 1) ∣ (3 ^ k + 3 ^ l) * 3 ^ a := by rwa [add_mul]
  have h2 := Int.le_of_dvd (by positivity) (hc.dvd_of_dvd_mul_right h1)
  have hk3 := three_pow_mul_le hk
  have hl3 := three_pow_mul_le hl
  have h27 : (27 : ℤ) ≤ 3 ^ (2 * a + 1) := by
    calc (27 : ℤ) = 3 ^ 3 := by norm_num
      _ ≤ 3 ^ (2 * a + 1) := pow_le_pow_right₀ (by norm_num) (by omega)
  linarith

theorem not_dvd_22 {a k l : ℕ} (ha : 1 ≤ a) (hk : k < 2 * a + 1) (hl : l < 2 * a + 1) :
    ¬ ((3 : ℤ) ^ (2 * a + 1) - 1) ∣ 3 ^ k * (2 * 3 ^ a - 1) + 3 ^ l * (2 * 3 ^ a - 1) := by
  intro h
  have hc : IsCoprime ((3 : ℤ) ^ (2 * a + 1) - 1) (2 * 3 ^ a - 1) :=
    ⟨-4, 3 * (2 * 3 ^ a + 1), by rw [three_pow_odd]; ring⟩
  have h1 : ((3 : ℤ) ^ (2 * a + 1) - 1) ∣ (3 ^ k + 3 ^ l) * (2 * 3 ^ a - 1) := by rwa [add_mul]
  have h2 := Int.le_of_dvd (by positivity) (hc.dvd_of_dvd_mul_right h1)
  have hk3 := three_pow_mul_le hk
  have hl3 := three_pow_mul_le hl
  have h27 : (27 : ℤ) ≤ 3 ^ (2 * a + 1) := by
    calc (27 : ℤ) = 3 ^ 3 := by norm_num
      _ ≤ 3 ^ (2 * a + 1) := pow_le_pow_right₀ (by norm_num) (by omega)
  linarith

theorem not_dvd_11 {a k l : ℕ} (ha : 1 ≤ a) (hk : k < 2 * a + 1) (hl : l < 2 * a + 1) :
    ¬ ((3 : ℤ) ^ (2 * a + 1) - 1) ∣ 3 ^ k * (1 - 3 ^ a) + 3 ^ l * (1 - 3 ^ a) := by
  intro h
  set N : ℤ := (3 : ℤ) ^ (2 * a + 1) - 1 with hN
  set X : ℤ := (3 : ℤ) ^ k + 3 ^ l with hX
  have h1 : N ∣ X * (1 - 3 ^ a) * (-(3 * (3 ^ a + 1))) :=
    dvd_mul_of_dvd_left (by rw [hX, add_mul]; exact h) _
  have h2 : N ∣ 2 * X := by
    have e : 2 * X = X * N - X * (1 - 3 ^ a) * (-(3 * (3 ^ a + 1))) := by
      rw [hN, three_pow_odd]; ring
    rw [e]
    exact dvd_sub (dvd_mul_left N X) h1
  have hk3 := three_pow_mul_le hk
  have hl3 := three_pow_mul_le hl
  have h27 : (27 : ℤ) ≤ 3 ^ (2 * a + 1) := by
    calc (27 : ℤ) = 3 ^ 3 := by norm_num
      _ ≤ 3 ^ (2 * a + 1) := pow_le_pow_right₀ (by norm_num) (by omega)
  have hk1 : (1 : ℤ) ≤ 3 ^ k := one_le_pow₀ (by norm_num)
  have hl1 : (1 : ℤ) ≤ 3 ^ l := one_le_pow₀ (by norm_num)
  obtain ⟨c, hc⟩ := h2
  have hc0 : 0 < c := by
    by_contra hc0
    rw [not_lt] at hc0
    nlinarith
  have hc1 : c < 2 := by
    by_contra hc1
    rw [not_lt] at hc1
    nlinarith
  have hc' : c = 1 := by omega
  rw [hc', mul_one] at hc
  obtain ⟨u, hu⟩ := odd_three_pow k
  obtain ⟨v, hv⟩ := odd_three_pow l
  obtain ⟨w, hw⟩ : (8 : ℤ) ∣ 9 ^ a - 1 := by simpa using sub_dvd_pow_sub_pow (9 : ℤ) 1 a
  have h9 : (3 : ℤ) ^ (2 * a + 1) = 3 * 9 ^ a := by
    rw [three_pow_odd, ← pow_mul, mul_comm a 2, pow_mul]
    norm_num
  rw [hX, hN, hu, hv, h9] at hc
  omega

theorem not_dvd_01 {a k l : ℕ} (hl : l < 2 * a + 1) :
    ¬ ((3 : ℤ) ^ (2 * a + 1) - 1) ∣ 3 ^ k * 3 ^ a + 3 ^ l * (1 - 3 ^ a) := by
  intro h
  set f := 2 * a + 1 with hf
  have hA := dvd_pow_sub_pow_mod f (k + a)
  have hC := dvd_pow_sub_pow_mod f (l + a)
  have h' : ((3 : ℤ) ^ f - 1) ∣ 3 ^ ((k + a) % f) + 3 ^ l - 3 ^ ((l + a) % f) := by
    have e : (3 : ℤ) ^ ((k + a) % f) + 3 ^ l - 3 ^ ((l + a) % f) =
        (3 ^ k * 3 ^ a + 3 ^ l * (1 - 3 ^ a)) - (3 ^ (k + a) - 3 ^ ((k + a) % f)) +
          (3 ^ (l + a) - 3 ^ ((l + a) % f)) := by
      rw [pow_add, pow_add]; ring
    rw [e]
    exact dvd_add (dvd_sub h hA) hC
  have hA3 := three_pow_mul_le (Nat.mod_lt (k + a) (by omega : 0 < f))
  have hC3 := three_pow_mul_le (Nat.mod_lt (l + a) (by omega : 0 < f))
  have hl3 := three_pow_mul_le hl
  have hA1 : (1 : ℤ) ≤ 3 ^ ((k + a) % f) := one_le_pow₀ (by norm_num)
  have hC1 : (1 : ℤ) ≤ 3 ^ ((l + a) % f) := one_le_pow₀ (by norm_num)
  have hl1 : (1 : ℤ) ≤ 3 ^ l := one_le_pow₀ (by norm_num)
  have h0 := Int.eq_zero_of_abs_lt_dvd h' (by rw [abs_lt]; constructor <;> linarith)
  obtain ⟨u, hu⟩ := odd_three_pow ((k + a) % f)
  obtain ⟨v, hv⟩ := odd_three_pow l
  obtain ⟨w, hw⟩ := odd_three_pow ((l + a) % f)
  rw [hu, hv, hw] at h0
  omega

theorem not_dvd_12 {a k l : ℕ} (hk : k < 2 * a + 1) (hl : l < 2 * a + 1) :
    ¬ ((3 : ℤ) ^ (2 * a + 1) - 1) ∣ 3 ^ k * (1 - 3 ^ a) + 3 ^ l * (2 * 3 ^ a - 1) := by
  intro h
  set f := 2 * a + 1 with hf
  have hA := dvd_pow_sub_pow_mod f (k + a)
  have hC := dvd_pow_sub_pow_mod f (l + a)
  have h' : ((3 : ℤ) ^ f - 1) ∣
      3 ^ k - 3 ^ ((k + a) % f) + 2 * 3 ^ ((l + a) % f) - 3 ^ l := by
    have e : (3 : ℤ) ^ k - 3 ^ ((k + a) % f) + 2 * 3 ^ ((l + a) % f) - 3 ^ l =
        (3 ^ k * (1 - 3 ^ a) + 3 ^ l * (2 * 3 ^ a - 1)) + (3 ^ (k + a) - 3 ^ ((k + a) % f)) -
          2 * (3 ^ (l + a) - 3 ^ ((l + a) % f)) := by
      rw [pow_add, pow_add]; ring
    rw [e]
    exact dvd_sub (dvd_add h hA) (dvd_mul_of_dvd_right hC 2)
  have hA3 := three_pow_mul_le (Nat.mod_lt (k + a) (by omega : 0 < f))
  have hC3 := three_pow_mul_le (Nat.mod_lt (l + a) (by omega : 0 < f))
  have hk3 := three_pow_mul_le hk
  have hl3 := three_pow_mul_le hl
  have hA1 : (1 : ℤ) ≤ 3 ^ ((k + a) % f) := one_le_pow₀ (by norm_num)
  have hC1 : (1 : ℤ) ≤ 3 ^ ((l + a) % f) := one_le_pow₀ (by norm_num)
  have hk1 : (1 : ℤ) ≤ 3 ^ k := one_le_pow₀ (by norm_num)
  have hl1 : (1 : ℤ) ≤ 3 ^ l := one_le_pow₀ (by norm_num)
  have h0 := Int.eq_zero_of_abs_lt_dvd h' (by rw [abs_lt]; constructor <;> linarith)
  obtain ⟨u, hu⟩ := odd_three_pow ((k + a) % f)
  obtain ⟨v, hv⟩ := odd_three_pow l
  obtain ⟨w, hw⟩ := odd_three_pow ((l + a) % f)
  obtain ⟨x, hx⟩ := odd_three_pow k
  rw [hu, hv, hw, hx] at h0
  omega

theorem not_dvd_02 {a k l : ℕ} (ha : 1 ≤ a) (hk : k < 2 * a + 1) (hl : l < 2 * a + 1) :
    ¬ ((3 : ℤ) ^ (2 * a + 1) - 1) ∣ 3 ^ k * 3 ^ a + 3 ^ l * (2 * 3 ^ a - 1) := by
  intro h
  set f := 2 * a + 1 with hf
  set A := (k + a) % f with hAdef
  set C := (l + a) % f with hCdef
  have hA := dvd_pow_sub_pow_mod f (k + a)
  have hC := dvd_pow_sub_pow_mod f (l + a)
  have h' : ((3 : ℤ) ^ f - 1) ∣ 3 ^ A + 2 * 3 ^ C - 3 ^ l := by
    have e : (3 : ℤ) ^ A + 2 * 3 ^ C - 3 ^ l =
        (3 ^ k * 3 ^ a + 3 ^ l * (2 * 3 ^ a - 1)) - (3 ^ (k + a) - 3 ^ A) -
          2 * (3 ^ (l + a) - 3 ^ C) := by
      rw [pow_add, pow_add]; ring
    rw [e]
    exact dvd_sub (dvd_sub h hA) (dvd_mul_of_dvd_right hC 2)
  have hAf : A < f := Nat.mod_lt _ (by omega)
  have hCf : C < f := Nat.mod_lt _ (by omega)
  have hA3 := three_pow_mul_le hAf
  have hC3 := three_pow_mul_le hCf
  have hl3 := three_pow_mul_le hl
  have hA1 : (1 : ℤ) ≤ 3 ^ A := one_le_pow₀ (by norm_num)
  have hC1 : (1 : ℤ) ≤ 3 ^ C := one_le_pow₀ (by norm_num)
  have hl1 : (1 : ℤ) ≤ 3 ^ l := one_le_pow₀ (by norm_num)
  have hf27 : (27 : ℤ) ≤ 3 ^ f := by
    calc (27 : ℤ) = 3 ^ 3 := by norm_num
      _ ≤ 3 ^ f := pow_le_pow_right₀ (by norm_num) (by omega)
  have hAc := mod_cases (show k + a < 2 * f by omega)
  have hCc := mod_cases (show l + a < 2 * f by omega)
  rw [← hAdef] at hAc
  rw [← hCdef] at hCc
  obtain ⟨c, hc⟩ := h'
  have hc0 : 0 ≤ c := by
    by_contra hc0
    rw [not_le] at hc0
    nlinarith
  have hc1 : c ≤ 1 := by
    by_contra hc1
    rw [not_le] at hc1
    nlinarith
  interval_cases c
  · have hz : (3 : ℕ) ^ A + 2 * 3 ^ C = 3 ^ l := by
      have : (3 : ℤ) ^ A + 2 * 3 ^ C = 3 ^ l := by linarith
      exact_mod_cast this
    obtain ⟨hAC, hlA⟩ := eq_of_pow_add_two_mul_pow hz
    omega
  · have hl0 : l = 0 := by
      by_contra hl0
      have : (3 : ℤ) ^ 1 ≤ 3 ^ l := pow_le_pow_right₀ (by norm_num) (by omega)
      linarith
    subst hl0
    have hz : (3 : ℕ) ^ A + 2 * 3 ^ C = 3 ^ f := by
      have : (3 : ℤ) ^ A + 2 * 3 ^ C = 3 ^ f := by simp at hc; linarith
      exact_mod_cast this
    obtain ⟨hAC, hfA⟩ := eq_of_pow_add_two_mul_pow hz
    omega

theorem wt_not_dvd {a : ℕ} (ha : 1 ≤ a) {i j : ℕ} (hi : i < 3) (hj : j < 3) {k l : ℕ}
    (hk : k < 2 * a + 1) (hl : l < 2 * a + 1) :
    ¬ ((3 : ℤ) ^ (2 * a + 1) - 1) ∣ 3 ^ k * wt a i + 3 ^ l * wt a j := by
  interval_cases i <;> interval_cases j <;> simp only [wt]
  · exact not_dvd_00 ha hk hl
  · exact not_dvd_01 hl
  · exact not_dvd_02 ha hk hl
  · exact fun h => not_dvd_01 hk (by rwa [add_comm (3 ^ l * (3 : ℤ) ^ a)])
  · exact not_dvd_11 ha hk hl
  · exact not_dvd_12 hk hl
  · exact fun h => not_dvd_02 ha hl hk (by rwa [add_comm (3 ^ l * (3 : ℤ) ^ a)])
  · exact fun h => not_dvd_12 hl hk (by rwa [add_comm (3 ^ l * (1 - (3 : ℤ) ^ a))])
  · exact not_dvd_22 ha hk hl


theorem wt_not_dvd_self {a : ℕ} (ha : 1 ≤ a) {i : ℕ} (hi : i < 3) :
    ¬ ((3 ^ (2 * a + 1) - 1 : ℕ) : ℤ) ∣ wt a i := by
  rw [Nat.cast_sub (Nat.one_le_pow _ _ (by norm_num)), Nat.cast_pow, Nat.cast_ofNat, Nat.cast_one]
  intro h
  have h3a : (3 : ℤ) ^ a * 3 ≤ 3 ^ (2 * a + 1) := three_pow_mul_le (by omega)
  have h3 : (3 : ℤ) ≤ 3 ^ a := by
    calc (3 : ℤ) = 3 ^ 1 := by norm_num
      _ ≤ 3 ^ a := pow_le_pow_right₀ (by norm_num) ha
  have hz := Int.eq_zero_of_abs_lt_dvd h (by
    interval_cases i <;> simp only [wt] <;> rw [abs_lt] <;> constructor <;> linarith)
  interval_cases i <;> simp only [wt] at hz <;> linarith


section Weights

variable {K : Type} [Field K] {a : ℕ}

theorem coe_zpow_wt_zero (s : Kˣ) : ((s ^ wt a 0 : Kˣ) : K) = (s : K) ^ 3 ^ a := by
  change ((s ^ ((3 : ℤ) ^ a) : Kˣ) : K) = _
  rw [show ((3 : ℤ) ^ a) = ((3 ^ a : ℕ) : ℤ) by push_cast; rfl, zpow_natCast,
    Units.val_pow_eq_pow_val]

theorem coe_zpow_wt_two (s : Kˣ) :
    ((s ^ wt a 2 : Kˣ) : K) = ((s ^ (2 * 3 ^ a - 1) : Kˣ) : K) := by
  change ((s ^ (2 * (3 : ℤ) ^ a - 1) : Kˣ) : K) = _
  have h1 : 1 ≤ 2 * 3 ^ a := by
    have := Nat.one_le_pow a 3 (by norm_num)
    omega
  rw [show (2 * (3 : ℤ) ^ a - 1) = ((2 * 3 ^ a - 1 : ℕ) : ℤ) by push_cast [h1]; rfl,
    zpow_natCast]

theorem exists_generator [Finite K] (hK : Nat.card K = 3 ^ (2 * a + 1)) :
    ∃ g : Kˣ, orderOf g = 3 ^ (2 * a + 1) - 1 := by
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := Kˣ)
  exact ⟨g, by rw [orderOf_eq_card_of_forall_mem_zpowers hg, Nat.card_units, hK]⟩

end Weights

section Series


variable {a : ℕ} {K : Type} [Field K] [Finite K] [CharP K G2.prime]

omit [Finite K] [CharP K G2.prime] in
variable (a K) in
@[expose] noncomputable def torusHom : Kˣ →* ModGL G2.tag K where
  toFun := smallReeTorusElt a K
  map_one' := smallReeTorusElt_one
  map_mul' := smallReeTorusElt_mul

omit [Finite K] [CharP K G2.prime] in
variable (a K) in
noncomputable abbrev uM (t b c : K) : ModGL G2.tag K := smallReeCoord a K t b c

variable (a K) in
@[expose] noncomputable def series : ℕ → Subgroup (ModGL G2.tag K)
  | 0 => ⊥
  | 1 => smallReeZ1 a K
  | 2 => smallReeU1 a K
  | _ => G2.reeFixedPosUnipotent K a

omit [Finite K] [CharP K G2.prime] in
variable (a K) in
@[expose] noncomputable def coord : ℕ → K → ModGL G2.tag K
  | 0 => fun c => uM a K 0 0 c
  | 1 => fun b => uM a K 0 b 0
  | _ => fun t => uM a K t 0 0

theorem mem_series_one {x : ModGL G2.tag K} : x ∈ series a K 1 ↔ ∃ c, x = uM a K 0 0 c :=
  Iff.rfl

theorem mem_series_two {x : ModGL G2.tag K} :
    x ∈ series a K 2 ↔ ∃ b c, x = uM a K 0 b c :=
  Iff.rfl

theorem uM_mem_series_one (c : K) : uM a K 0 0 c ∈ series a K 1 := ⟨c, rfl⟩

theorem uM_mem_series_two (b c : K) : uM a K 0 b c ∈ series a K 2 := ⟨b, c, rfl⟩

omit [Finite K] [CharP K G2.prime]
    in
theorem uM_zero : uM a K 0 0 0 = 1 := smallReeCoord_zero

variable (hK : Nat.card K = 3 ^ (2 * a + 1))
include hK

theorem mem_U_iff {x : ModGL G2.tag K} :
    x ∈ G2.reeFixedPosUnipotent K a ↔ ∃ t b c : K, x = uM a K t b c := by
  constructor
  · intro hx
    obtain ⟨⟨t, b, c⟩, -, h⟩ := (bijOn_smallReeCoord hK).2.2 (SetLike.mem_coe.2 hx)
    exact ⟨t, b, c, h.symm⟩
  · rintro ⟨t, b, c, rfl⟩
    exact smallReeCoord_mem_reeFixedPosUnipotent hK t b c

theorem mem_series_three {x : ModGL G2.tag K} :
    x ∈ series a K 3 ↔ ∃ t b c : K, x = uM a K t b c :=
  mem_U_iff hK

theorem uM_mem_U (t b c : K) : uM a K t b c ∈ G2.reeFixedPosUnipotent K a :=
  (mem_U_iff hK).2 ⟨t, b, c, rfl⟩

theorem uM_inj {t b c t' b' c' : K} (h : uM a K t b c = uM a K t' b' c') :
    t = t' ∧ b = b' ∧ c = c' := by
  have h' := (bijOn_smallReeCoord hK).2.1 (Set.mem_univ (t, b, c)) (Set.mem_univ (t', b', c')) h
  simpa only [Prod.mk.injEq] using h'

omit [CharP K G2.prime]
  in
theorem uM_mul (t b c s d e : K) :
    uM a K t b c * uM a K s d e =
      uM a K (t + s) (b + d + smallReeSigma a t * s) (c + e - b * s + smallReeSigma a t * s ^ 2) :=
  smallReeCoord_mul hK t b c s d e

omit [CharP K G2.prime]
  in
theorem uM_inv (t b c : K) :
    (uM a K t b c)⁻¹ =
      uM a K (-t) (-b + t * smallReeSigma a t) (-c - b * t - t ^ 2 * smallReeSigma a t) :=
  smallReeCoord_inv hK t b c

omit [CharP K G2.prime]
  in
theorem uM_pow_three (t b c : K) :
    uM a K t b c ^ 3 = uM a K 0 0 (-(t ^ 2 * smallReeSigma a t)) :=
  smallReeCoord_pow_three hK t b c

omit [CharP K G2.prime]
  in
theorem uM_zero_mul (b c s d e : K) :
    uM a K 0 b c * uM a K s d e = uM a K s (b + d) (c + e - b * s) := by
  rw [uM_mul hK, smallReeSigma_zero]
  congr 1 <;> ring

omit [CharP K G2.prime]
  in
theorem uM_mul_zero (s d e b c : K) :
    uM a K s d e * uM a K 0 b c = uM a K s (d + b) (e + c) := by
  rw [uM_mul hK]
  congr 1 <;> ring

theorem torus_conj (s : Kˣ) (t b c : K) :
    torusHom a K s * uM a K t b c * (torusHom a K s)⁻¹ =
      uM a K (((s ^ (2 * 3 ^ a - 1) : Kˣ) : K) * t) (((s ^ (1 - (3 ^ a : ℤ)) : Kˣ) : K) * b)
        ((s : K) ^ 3 ^ a * c) :=
  smallReeTorusElt_conj_smallReeCoord hK s t b c

theorem torus_conj_mem_U (s : Kˣ) {x : ModGL G2.tag K} (hx : x ∈ G2.reeFixedPosUnipotent K a) :
    torusHom a K s * x * (torusHom a K s)⁻¹ ∈ G2.reeFixedPosUnipotent K a := by
  obtain ⟨t, b, c, rfl⟩ := (mem_U_iff hK).1 hx
  rw [torus_conj hK]
  exact uM_mem_U hK _ _ _

theorem coord_mem {i : ℕ} (hi : i < 3) (u : K) : coord a K i u ∈ series a K (i + 1) := by
  interval_cases i
  · exact uM_mem_series_one u
  · exact uM_mem_series_two u 0
  · exact uM_mem_U hK u 0 0

theorem series_mono {i : ℕ} (hi : i < 3) : series a K i ≤ series a K (i + 1) := by
  interval_cases i
  · exact bot_le
  · intro x hx
    obtain ⟨c, rfl⟩ := mem_series_one.1 hx
    exact uM_mem_series_two 0 c
  · intro x hx
    obtain ⟨b, c, rfl⟩ := mem_series_two.1 hx
    exact uM_mem_U hK 0 b c

theorem exists_coord {i : ℕ} (hi : i < 3) {x : ModGL G2.tag K} (hx : x ∈ series a K (i + 1)) :
    ∃ u, ∃ z ∈ series a K i, x = coord a K i u * z := by
  interval_cases i
  · obtain ⟨c, rfl⟩ := mem_series_one.1 hx
    exact ⟨c, 1, one_mem _, (mul_one _).symm⟩
  · obtain ⟨b, c, rfl⟩ := mem_series_two.1 hx
    refine ⟨b, uM a K 0 0 c, uM_mem_series_one c, ?_⟩
    change _ = uM a K 0 b 0 * uM a K 0 0 c
    rw [uM_mul_zero hK, add_zero, zero_add]
  · obtain ⟨t, b, c, rfl⟩ := (mem_U_iff hK).1 hx
    refine ⟨t, uM a K 0 b c, uM_mem_series_two b c, ?_⟩
    change _ = uM a K t 0 0 * uM a K 0 b c
    rw [uM_mul_zero hK, zero_add, zero_add]

theorem coord_add {i : ℕ} (hi : i < 3) (u u' : K) :
    ∃ z ∈ series a K i, coord a K i u * coord a K i u' = coord a K i (u + u') * z := by
  interval_cases i
  · refine ⟨1, one_mem _, ?_⟩
    change uM a K 0 0 u * uM a K 0 0 u' = uM a K 0 0 (u + u') * 1
    rw [uM_zero_mul hK, mul_one]
    congr 1 <;> ring
  · refine ⟨1, one_mem _, ?_⟩
    change uM a K 0 u 0 * uM a K 0 u' 0 = uM a K 0 (u + u') 0 * 1
    rw [uM_zero_mul hK, mul_one]
    congr 1
    ring
  · refine ⟨uM a K 0 (smallReeSigma a u * u') (smallReeSigma a u * u' ^ 2),
      uM_mem_series_two _ _, ?_⟩
    change uM a K u 0 0 * uM a K u' 0 0 = uM a K (u + u') 0 0 * uM a K 0 _ _
    rw [uM_mul hK, uM_mul_zero hK]
    congr 1 <;> ring

theorem coord_conj {i : ℕ} (hi : i < 3) (s : Kˣ) (u : K) :
    torusHom a K s * coord a K i u * (torusHom a K s)⁻¹ =
      coord a K i (((s ^ wt a i : Kˣ) : K) * u) := by
  interval_cases i
  · change torusHom a K s * uM a K 0 0 u * (torusHom a K s)⁻¹ =
      uM a K 0 0 (((s ^ wt a 0 : Kˣ) : K) * u)
    rw [torus_conj hK, mul_zero, mul_zero, coe_zpow_wt_zero]
  · change torusHom a K s * uM a K 0 u 0 * (torusHom a K s)⁻¹ =
      uM a K 0 (((s ^ wt a 1 : Kˣ) : K) * u) 0
    rw [torus_conj hK, mul_zero, mul_zero]
    rfl
  · change torusHom a K s * uM a K u 0 0 * (torusHom a K s)⁻¹ =
      uM a K (((s ^ wt a 2 : Kˣ) : K) * u) 0 0
    rw [torus_conj hK, mul_zero, mul_zero, coe_zpow_wt_two]

theorem series_inv {i : ℕ} (hi : i ≤ 3) (s : Kˣ) {x : ModGL G2.tag K}
    (hx : x ∈ series a K i) : torusHom a K s * x * (torusHom a K s)⁻¹ ∈ series a K i := by
  interval_cases i
  · change x ∈ (⊥ : Subgroup (ModGL G2.tag K)) at hx
    change _ ∈ (⊥ : Subgroup (ModGL G2.tag K))
    rw [Subgroup.mem_bot] at hx ⊢
    rw [hx, mul_one, mul_inv_cancel]
  · obtain ⟨c, rfl⟩ := mem_series_one.1 hx
    rw [torus_conj hK, mul_zero, mul_zero]
    exact uM_mem_series_one _
  · obtain ⟨b, c, rfl⟩ := mem_series_two.1 hx
    rw [torus_conj hK, mul_zero]
    exact uM_mem_series_two _ _
  · exact torus_conj_mem_U hK s hx

theorem series_cent {i : ℕ} (hi : i < 3) {x : ModGL G2.tag K} (hx : x ∈ series a K (i + 1))
    {g : ModGL G2.tag K} (hg : g ∈ G2.reeFixedPosUnipotent K a) :
    x⁻¹ * g⁻¹ * x * g ∈ series a K i := by
  obtain ⟨s, d, e, rfl⟩ := (mem_U_iff hK).1 hg
  interval_cases i
  · obtain ⟨c, rfl⟩ := mem_series_one.1 hx
    have hc : uM a K 0 0 c * uM a K s d e = uM a K s d e * uM a K 0 0 c := by
      rw [uM_zero_mul hK, uM_mul_zero hK]
      congr 1 <;> ring
    change _ ∈ (⊥ : Subgroup (ModGL G2.tag K))
    rw [Subgroup.mem_bot, mul_assoc _ _ (uM a K s d e), hc]
    group
  · obtain ⟨b, c, rfl⟩ := mem_series_two.1 hx
    have hc : uM a K 0 b c * uM a K s d e =
        uM a K s d e * uM a K 0 b c * uM a K 0 0 (-(b * s)) := by
      rw [uM_zero_mul hK, uM_mul_zero hK, uM_mul_zero hK]
      congr 1 <;> ring
    have he : (uM a K 0 b c)⁻¹ * (uM a K s d e)⁻¹ * uM a K 0 b c * uM a K s d e =
        uM a K 0 0 (-(b * s)) := by
      rw [mul_assoc _ _ (uM a K s d e), hc]
      group
    rw [he]
    exact uM_mem_series_one _
  · obtain ⟨t, b, c, rfl⟩ := (mem_U_iff hK).1 hx
    rw [uM_inv hK, uM_inv hK, uM_mul hK, uM_mul hK, uM_mul hK]
    exact (mem_smallReeU1_iff hK _ _ _).2 (by ring)

theorem series_sq {i : ℕ} (hi : i < 3) {x : ModGL G2.tag K} (hx : x ∈ series a K (i + 1)) :
    x ^ 3 ∈ series a K i := by
  interval_cases i
  · obtain ⟨c, rfl⟩ := mem_series_one.1 hx
    change _ ∈ (⊥ : Subgroup (ModGL G2.tag K))
    rw [Subgroup.mem_bot, uM_pow_three hK, zero_pow two_ne_zero, zero_mul, neg_zero]
    exact uM_zero
  · obtain ⟨b, c, rfl⟩ := mem_series_two.1 hx
    rw [uM_pow_three hK]
    exact uM_mem_series_one _
  · obtain ⟨t, b, c, rfl⟩ := (mem_U_iff hK).1 hx
    rw [uM_pow_three hK]
    exact uM_mem_series_two _ _

theorem series_fix (ha : 1 ≤ a) {i : ℕ} (hi : i < 3) {x : ModGL G2.tag K}
    (hx : x ∈ series a K (i + 1))
    (hfx : ∀ s : Kˣ, (torusHom a K s * x * (torusHom a K s)⁻¹)⁻¹ * x ∈ series a K i) :
    x ∈ series a K i := by
  obtain ⟨g, hg⟩ := exists_generator hK
  have hg1 : ((g ^ wt a i : Kˣ) : K) ≠ 1 := by
    intro h
    have h' : g ^ wt a i = 1 := Units.ext h
    rw [← orderOf_dvd_iff_zpow_eq_one, hg] at h'
    exact wt_not_dvd_self ha hi h'
  have hsub : ∀ {u : K}, ((g ^ wt a i : Kˣ) : K) * u = u → u = 0 := by
    intro u hu
    have h' : (((g ^ wt a i : Kˣ) : K) - 1) * u = 0 := by rw [sub_mul, one_mul, hu, sub_self]
    exact (mul_eq_zero.1 h').resolve_left (sub_ne_zero.2 hg1)
  interval_cases i
  · obtain ⟨c, rfl⟩ := mem_series_one.1 hx
    have h := hfx g
    change _ ∈ (⊥ : Subgroup (ModGL G2.tag K)) at h
    change _ ∈ (⊥ : Subgroup (ModGL G2.tag K))
    rw [Subgroup.mem_bot, inv_mul_eq_one, torus_conj hK, mul_zero, mul_zero] at h
    have hc : c = 0 := hsub (by rw [coe_zpow_wt_zero]; exact (uM_inj hK h).2.2)
    rw [Subgroup.mem_bot, hc]
    exact uM_zero
  · obtain ⟨b, c, rfl⟩ := mem_series_two.1 hx
    have h := hfx g
    rw [torus_conj hK, mul_zero, uM_inv hK, uM_mul hK] at h
    obtain ⟨c', hc'⟩ := mem_series_one.1 h
    obtain ⟨-, hb', -⟩ := uM_inj hK hc'
    have hb : b = 0 := hsub (by
      change ((g ^ (1 - (3 ^ a : ℤ)) : Kˣ) : K) * b = b
      linear_combination -hb')
    rw [hb]
    exact uM_mem_series_one c
  · obtain ⟨t, b, c, rfl⟩ := (mem_U_iff hK).1 hx
    have h := hfx g
    rw [torus_conj hK, uM_inv hK, uM_mul hK] at h
    obtain ⟨b', c', hbc⟩ := mem_series_two.1 h
    obtain ⟨ht', -, -⟩ := uM_inj hK hbc
    have ht : t = 0 := hsub (by rw [coe_zpow_wt_two]; linear_combination -ht')
    rw [ht]
    exact uM_mem_series_two b c

theorem series_bil (ha : 1 ≤ a) {i : ℕ} (hi : i < 3) {j : ℕ} (hj : j < 3)
    (bf : ModGL G2.tag K → ModGL G2.tag K → ZMod 3)
    (hb₁ : ∀ x ∈ series a K (i + 1), ∀ x' ∈ series a K (i + 1), ∀ y ∈ series a K (j + 1),
      bf (x * x') y = bf x y + bf x' y)
    (hb₂ : ∀ x ∈ series a K (i + 1), ∀ y ∈ series a K (j + 1), ∀ y' ∈ series a K (j + 1),
      bf x (y * y') = bf x y + bf x y')
    (hv₁ : ∀ x ∈ series a K i, ∀ y ∈ series a K (j + 1), bf x y = 0)
    (hv₂ : ∀ x ∈ series a K (i + 1), ∀ y ∈ series a K j, bf x y = 0)
    (hT : ∀ (t : Kˣ), ∀ x ∈ series a K (i + 1), ∀ y ∈ series a K (j + 1),
      bf (torusHom a K t * x * (torusHom a K t)⁻¹) (torusHom a K t * y * (torusHom a K t)⁻¹) =
        bf x y) :
    ∀ x ∈ series a K (i + 1), ∀ y ∈ series a K (j + 1), bf x y = 0 := by
  set F : K → K → ZMod 3 := fun u v => bf (coord a K i u) (coord a K j v) with hFdef
  have hF₁ : ∀ u u' v, F (u + u') v = F u v + F u' v := by
    intro u u' v
    obtain ⟨z, hz, hzeq⟩ := coord_add hK hi u u'
    have h1 := hb₁ _ (coord_mem hK hi u) _ (coord_mem hK hi u') _ (coord_mem hK hj v)
    rw [hzeq, hb₁ _ (coord_mem hK hi (u + u')) _ (series_mono hK hi hz) _ (coord_mem hK hj v),
      hv₁ _ hz _ (coord_mem hK hj v), add_zero] at h1
    exact h1
  have hF₂ : ∀ u v v', F u (v + v') = F u v + F u v' := by
    intro u v v'
    obtain ⟨z, hz, hzeq⟩ := coord_add hK hj v v'
    have h1 := hb₂ _ (coord_mem hK hi u) _ (coord_mem hK hj v) _ (coord_mem hK hj v')
    rw [hzeq, hb₂ _ (coord_mem hK hi u) _ (coord_mem hK hj (v + v')) _ (series_mono hK hj hz),
      hv₂ _ (coord_mem hK hi u) _ hz, add_zero] at h1
    exact h1
  have hFT : ∀ (t : Kˣ) u v,
      F (((t ^ wt a i : Kˣ) : K) * u) (((t ^ wt a j : Kˣ) : K) * v) = F u v := by
    intro t u v
    simp only [hFdef]
    rw [← coord_conj hK hi, ← coord_conj hK hj]
    exact hT t _ (coord_mem hK hi u) _ (coord_mem hK hj v)
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : CharP K 3 := ‹CharP K G2.prime›
  have hF0 := zpow_form_eq_zero (p := 3) (f := 2 * a + 1) (by omega) hK (e₁ := wt a i)
    (e₂ := wt a j) (fun k l hk hl h => wt_not_dvd ha hi hj hk hl (by
      rw [Nat.cast_sub (Nat.one_le_pow _ _ (by norm_num)), Nat.cast_pow, Nat.cast_ofNat,
        Nat.cast_one] at h
      exact h)) F hF₁ hF₂ hFT
  intro x hx y hy
  obtain ⟨u, z, hz, rfl⟩ := exists_coord hK hi hx
  obtain ⟨v, z', hz', rfl⟩ := exists_coord hK hj hy
  rw [hb₁ _ (coord_mem hK hi u) _ (series_mono hK hi hz) _ hy, hv₁ _ hz _ hy, add_zero,
    hb₂ _ (coord_mem hK hi u) _ (coord_mem hK hj v) _ (series_mono hK hj hz'),
    hv₂ _ (coord_mem hK hi u) _ hz', add_zero]
  exact hF0 u v

theorem smallRee_three_cover_trivial (ha : 1 ≤ a) {E : Type*} [Group E] [Finite E]
    [Group.IsPerfect E] (η : E →* G2.reeGamma K a) (hη : Function.Surjective η)
    (hC : η.ker ≤ Subgroup.center E) (h3 : IsPGroup 3 η.ker) : η.ker = ⊥ := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨w₀, hw₀, -⟩ := CFSG.LieType.Chevalley.weyl_longest_element G2.tag
  obtain ⟨-, -, -, -, -, -, -, -, -, -, ⟨P, hP⟩, -⟩ :=
    small_Ree_Borel_coset_Sylow_action a K hK w₀ hw₀
  have hUp : IsPGroup 3 ((G2.reeFixedPosUnipotent K a).subgroupOf (G2.reeGamma K a)) := by
    rw [← hP]
    exact P.isPGroup'
  have hUi : ¬ 3 ∣ ((G2.reeFixedPosUnipotent K a).subgroupOf (G2.reeGamma K a)).index := by
    rw [← hP]
    exact P.not_dvd_index
  have hT : Nat.Coprime 3 (Nat.card Kˣ) := by
    rw [Nat.card_units, hK, Nat.Prime.coprime_iff_not_dvd Nat.prime_three]
    rintro ⟨c, hc⟩
    have h3 : 3 ^ (2 * a + 1) = 3 * 3 ^ (2 * a) := by ring
    have h1 : 1 ≤ 3 ^ (2 * a) := Nat.one_le_pow _ _ (by norm_num)
    omega
  exact CFSG.LocalAnalysis.ComponentInitial.ker_eq_bot_of_coprime_central_series_prime η hη hC
    h3 (fun _ hx => (Subgroup.mem_inf.1 hx).2) hUp hUi hT (torusHom a K)
    (fun s => (Subgroup.mem_inf.1 (smallReeTorusElt_mem hK s)).2)
    (fun s x hx => torus_conj_mem_U hK s hx) 3 (series a K) rfl rfl
    (fun i hi => series_mono hK hi) (fun i hi s x hx => series_inv hK hi s hx)
    (fun i hi x hx g hg => series_cent hK hi hx hg) (fun i hi x hx => series_sq hK hi hx)
    (fun i hi x hx hfx => series_fix hK ha hi hx hfx)
    (fun i hi j hj bf hb₁ hb₂ hv₁ hv₂ hT' => series_bil hK ha hi hj bf hb₁ hb₂ hv₁ hv₂ hT')

end Series

end CFSG.LieType.Steinberg.CentralExt.SmallReeClosed

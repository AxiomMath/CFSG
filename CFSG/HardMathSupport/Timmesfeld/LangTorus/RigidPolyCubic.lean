module

public import CFSG.HardMathSupport.Timmesfeld.LangTorus.RigidPoly

public section

namespace CFSG.HardMathSupport.Timmesfeld.LangTorus

open Polynomial

section Prod

variable {L A : Type*} [Field L] [Ring A] [Algebra L A]

@[expose] noncomputable def fac3 (w : ℕ) (a b d : A) : A[X] :=
  1 + C a * X ^ w + C b * X ^ (2 * w) + C d * X ^ (3 * w)

@[expose] noncomputable def prodList3 (q : ℕ) (a b d : ℕ → A) (ks : List ℕ) : A[X] :=
  (ks.map fun k => fac3 (q ^ k) (a k) (b k) (d k)).prod

theorem evAt_C_mul_X_pow (u : L) (n : ℕ) (a : A) : evAt u (C a * X ^ n) = u ^ n • a := by
  rw [C_mul_X_pow_eq_monomial, evAt_monomial]

theorem evAt_fac3 (u : L) (w : ℕ) (a b d : A) :
    evAt u (fac3 w a b d) = 1 + u ^ w • a + (u ^ w) ^ 2 • b + (u ^ w) ^ 3 • d := by
  unfold fac3
  rw [map_add, map_add, map_add, map_one, evAt_C_mul_X_pow, evAt_C_mul_X_pow, evAt_C_mul_X_pow,
    ← pow_mul, ← pow_mul, mul_comm 2 w, mul_comm 3 w]

theorem evAt_prodList3 (u : L) (q : ℕ) (a b d : ℕ → A) (ks : List ℕ) :
    evAt u (prodList3 q a b d ks) =
      (ks.map fun k => 1 + (u ^ q ^ k) • a k + (u ^ q ^ k) ^ 2 • b k +
        (u ^ q ^ k) ^ 3 • d k).prod := by
  unfold prodList3
  rw [map_list_prod, List.map_map]
  congr 1
  refine List.map_congr_left fun k _ => ?_
  exact evAt_fac3 u _ _ _ _

theorem prodList3_cons (q : ℕ) (a b d : ℕ → A) (k : ℕ) (ks : List ℕ) :
    prodList3 q a b d (k :: ks) = fac3 (q ^ k) (a k) (b k) (d k) * prodList3 q a b d ks := by
  simp [prodList3]

theorem coeff_fac3_mul (w : ℕ) (a b d : A) (p : A[X]) (n : ℕ) :
    (fac3 w a b d * p).coeff n = p.coeff n + (if w ≤ n then a * p.coeff (n - w) else 0) +
      (if 2 * w ≤ n then b * p.coeff (n - 2 * w) else 0) +
      (if 3 * w ≤ n then d * p.coeff (n - 3 * w) else 0) := by
  unfold fac3
  rw [add_mul, add_mul, add_mul, one_mul, mul_assoc, mul_assoc, mul_assoc, coeff_add, coeff_add,
    coeff_add, coeff_C_mul, coeff_C_mul, coeff_C_mul, coeff_X_pow_mul', coeff_X_pow_mul',
    coeff_X_pow_mul']
  simp only [mul_ite, mul_zero]

end Prod

section Support

variable {A : Type*} [Ring A]

@[expose] def Aset3 (q : ℕ) : List ℕ → Set ℕ
  | [] => {0}
  | k :: ks => {n | n ∈ Aset3 q ks ∨ (q ^ k ≤ n ∧ n - q ^ k ∈ Aset3 q ks) ∨
      (2 * q ^ k ≤ n ∧ n - 2 * q ^ k ∈ Aset3 q ks) ∨
      (3 * q ^ k ≤ n ∧ n - 3 * q ^ k ∈ Aset3 q ks)}

theorem coeff_zero_prodList3 {q : ℕ} (hq : 1 ≤ q) (a b d : ℕ → A) (ks : List ℕ) :
    (prodList3 q a b d ks).coeff 0 = 1 := by
  induction ks with
  | nil => simp [prodList3]
  | cons k ks ih =>
    rw [prodList3_cons, coeff_fac3_mul, ih]
    have h1 : 1 ≤ q ^ k := Nat.one_le_pow _ _ hq
    simp only [Nat.le_zero, (show q ^ k ≠ 0 by omega), (show 2 * q ^ k ≠ 0 by omega),
      (show 3 * q ^ k ≠ 0 by omega), ↓reduceIte]
    simp

theorem mem_Aset3_of_coeff_ne_zero (q : ℕ) (a b d : ℕ → A) (ks : List ℕ) (n : ℕ)
    (h : (prodList3 q a b d ks).coeff n ≠ 0) : n ∈ Aset3 q ks := by
  induction ks generalizing n with
  | nil =>
    have hp : prodList3 q a b d ([] : List ℕ) = 1 := by simp [prodList3]
    rw [hp, coeff_one] at h
    by_cases hn : n = 0
    · simp [Aset3, hn]
    · simp only [hn, ↓reduceIte] at h
      exact absurd rfl h
  | cons k ks ih =>
    rw [prodList3_cons, coeff_fac3_mul] at h
    by_contra hn
    simp only [Aset3, Set.mem_setOf_eq, not_or, not_and] at hn
    obtain ⟨h0, h1, h2, h3⟩ := hn
    refine h ?_
    have e0 : (prodList3 q a b d ks).coeff n = 0 := by
      by_contra hne
      exact h0 (ih n hne)
    have e1 : (if q ^ k ≤ n then a k * (prodList3 q a b d ks).coeff (n - q ^ k) else 0) = 0 := by
      split_ifs with hle
      · have : (prodList3 q a b d ks).coeff (n - q ^ k) = 0 := by
          by_contra hne
          exact h1 hle (ih _ hne)
        rw [this, mul_zero]
      · rfl
    have e2 : (if 2 * q ^ k ≤ n then b k * (prodList3 q a b d ks).coeff (n - 2 * q ^ k)
        else 0) = 0 := by
      split_ifs with hle
      · have : (prodList3 q a b d ks).coeff (n - 2 * q ^ k) = 0 := by
          by_contra hne
          exact h2 hle (ih _ hne)
        rw [this, mul_zero]
      · rfl
    have e3 : (if 3 * q ^ k ≤ n then d k * (prodList3 q a b d ks).coeff (n - 3 * q ^ k)
        else 0) = 0 := by
      split_ifs with hle
      · have : (prodList3 q a b d ks).coeff (n - 3 * q ^ k) = 0 := by
          by_contra hne
          exact h3 hle (ih _ hne)
        rw [this, mul_zero]
      · rfl
    rw [e0, e1, e2, e3]
    simp

end Support

section Bounds

variable {A : Type*} [Ring A]

theorem Aset3_le (q : ℕ) (ks : List ℕ) : ∀ n ∈ Aset3 q ks, n ≤ 3 * (ks.map (q ^ ·)).sum := by
  induction ks with
  | nil =>
    intro n hn
    simp only [Aset3, Set.mem_singleton_iff] at hn
    omega
  | cons k ks ih =>
    intro n hn
    simp only [List.map_cons, List.sum_cons]
    rcases hn with hn | ⟨h1, hn⟩ | ⟨h1, hn⟩ | ⟨h1, hn⟩
    · have := ih n hn
      omega
    · have := ih _ hn
      omega
    · have := ih _ hn
      omega
    · have := ih _ hn
      omega

theorem Aset3_small (q : ℕ) (ks : List ℕ) (hnd : ks.Nodup) :
    ∀ n ∈ Aset3 q ks, (0 ∈ ks → n ≤ 3 ∨ q ≤ n) ∧ (0 ∉ ks → n = 0 ∨ q ≤ n) := by
  induction ks with
  | nil =>
    intro n hn
    simp only [Aset3, Set.mem_singleton_iff] at hn
    subst hn
    simp
  | cons k ks ih =>
    intro n hn
    have hk : k ∉ ks := (List.nodup_cons.1 hnd).1
    have ih' := ih (List.nodup_cons.1 hnd).2
    by_cases hk0 : k = 0
    · subst hk0
      have h0 : (0 : ℕ) ∉ ks := hk
      refine ⟨fun _ => ?_, fun h => absurd List.mem_cons_self h⟩
      rcases hn with hn | ⟨h1, hn⟩ | ⟨h1, hn⟩ | ⟨h1, hn⟩
      · rcases (ih' n hn).2 h0 with h | h <;> omega
      · rcases (ih' _ hn).2 h0 with h | h <;> (simp only [pow_zero] at h1 h; omega)
      · rcases (ih' _ hn).2 h0 with h | h <;> (simp only [pow_zero] at h1 h; omega)
      · rcases (ih' _ hn).2 h0 with h | h <;> (simp only [pow_zero] at h1 h; omega)
    · have hqk : q ≤ q ^ k := Nat.le_self_pow hk0 q
      have hmem : (0 ∈ k :: ks) ↔ (0 ∈ ks) := by
        simp [Ne.symm hk0]
      rw [hmem]
      rcases hn with hn | ⟨h1, hn⟩ | ⟨h1, hn⟩ | ⟨h1, hn⟩
      · exact ih' n hn
      · exact ⟨fun _ => Or.inr (by omega), fun _ => Or.inr (by omega)⟩
      · exact ⟨fun _ => Or.inr (by omega), fun _ => Or.inr (by omega)⟩
      · exact ⟨fun _ => Or.inr (by omega), fun _ => Or.inr (by omega)⟩

theorem coeff_one_prodList3 {q : ℕ} (hq : 2 ≤ q) (a b d : ℕ → A) (ks : List ℕ)
    (hnd : ks.Nodup) : (prodList3 q a b d ks).coeff 1 = if 0 ∈ ks then a 0 else 0 := by
  induction ks with
  | nil => simp [prodList3, coeff_one]
  | cons k ks ih =>
    have hk : k ∉ ks := (List.nodup_cons.1 hnd).1
    have ih' := ih (List.nodup_cons.1 hnd).2
    rw [prodList3_cons, coeff_fac3_mul, ih']
    by_cases hk0 : k = 0
    · subst hk0
      have h0 : (0 : ℕ) ∉ ks := hk
      simp [h0, coeff_zero_prodList3 (by omega : 1 ≤ q)]
    · have hqk : q ≤ q ^ k := Nat.le_self_pow hk0 q
      have h1 : ¬ q ^ k ≤ 1 := by omega
      have h2 : ¬ 2 * q ^ k ≤ 1 := by omega
      have h3 : ¬ 3 * q ^ k ≤ 1 := by omega
      have hmem : (0 ∈ k :: ks) ↔ (0 ∈ ks) := by simp [Ne.symm hk0]
      simp [h1, h2, h3, hmem]

theorem support_bound3 {q s : ℕ} (ks : List ℕ) (hnd : ks.Nodup)
    (h0 : 0 ∈ ks) (hks : ∀ k ∈ ks, k < s) (a b d : ℕ → A) (n : ℕ)
    (hn : (prodList3 q a b d ks).coeff n ≠ 0) :
    n ≤ 3 * ∑ k ∈ Finset.range s, q ^ k ∧ (n ≤ 3 ∨ q ≤ n) := by
  have hmem := mem_Aset3_of_coeff_ne_zero q a b d ks n hn
  exact ⟨(Aset3_le q ks n hmem).trans (Nat.mul_le_mul_left _ (sum_pow_list_le q s ks hnd hks)),
    (Aset3_small q ks hnd n hmem).1 h0⟩

end Bounds

section Digits

theorem eq_of_dvd_mul_pred_add {N c n : ℕ} (hN : 1 ≤ N) (hn : n < N) (hc : c < N)
    (h : N ∣ c * (N - 1) + n) : n = c := by
  have hd' : (N : ℤ) ∣ (c : ℤ) * ((N : ℤ) - 1) + n := by
    have := Int.natCast_dvd_natCast.2 h
    push_cast [Nat.cast_sub hN] at this
    simpa using this
  have hd'' : (N : ℤ) ∣ (n : ℤ) - c := by
    have h2 : (N : ℤ) ∣ (c : ℤ) * N := dvd_mul_left _ _
    have h3 := dvd_sub hd' h2
    have e : (c : ℤ) * ((N : ℤ) - 1) + n - (c : ℤ) * N = (n : ℤ) - c := by ring
    rwa [e] at h3
  have h4 := Int.eq_zero_of_abs_lt_dvd hd'' (abs_lt.2 ⟨by omega, by omega⟩)
  omega

theorem eq_one_of_dvd_mul_pred_add_mul {N c n : ℕ} (hcop : Nat.Coprime c N) (hN : 2 ≤ N)
    (hn : n < N) (h : N ∣ c * (N - 1) + c * n) : n = 1 := by
  rw [← Nat.mul_add] at h
  have h1 := Nat.Coprime.dvd_of_dvd_mul_left hcop.symm h
  rw [add_comm] at h1
  exact eq_one_of_dvd_add_pred hN hn h1

variable {A : Type*} [Ring A]

theorem sum_support_dvd_eq {P : A[X]} {N n₀ : ℕ} {g : ℕ → ℕ}
    (h : ∀ n ∈ P.support, N ∣ g n ↔ n = n₀) :
    (∑ n ∈ P.support, if N ∣ g n then P.coeff n else 0) = P.coeff n₀ := by
  rw [Finset.sum_eq_single n₀]
  · by_cases hn : n₀ ∈ P.support
    · simp [(h n₀ hn).2 rfl]
    · rw [mem_support_iff, not_not] at hn
      simp [hn]
  · intro n hn hne
    simp [mt (h n hn).1 hne]
  · intro hn
    rw [mem_support_iff, not_not] at hn
    simp [hn]

theorem sum_support_dvd_eq_zero {P : A[X]} {N : ℕ} {g : ℕ → ℕ}
    (h : ∀ n ∈ P.support, ¬ N ∣ g n) :
    (∑ n ∈ P.support, if N ∣ g n then P.coeff n else 0) = 0 :=
  Finset.sum_eq_zero fun n hn => by simp [h n hn]

end Digits

section Core

variable {A : Type*} [Ring A]

theorem cubic_core_two {P P' : A[X]} {N σ : ℕ} {z : Aˣ} (hσ : 1 ≤ σ) (h6 : 6 * σ ≤ N)
    (hP : ∀ n, P.coeff n ≠ 0 → n ≤ 3 * σ) (hP' : ∀ n, P'.coeff n ≠ 0 → n ≤ 3 * σ)
    (hP1 : P.coeff 1 ≠ 0)
    (key : (z : A) * (∑ n ∈ P'.support, if N ∣ (N - 1) + 2 * n then P'.coeff n else 0) *
        (↑z⁻¹ : A) = ∑ n ∈ P.support, if N ∣ (N - 1) + 1 * n then P.coeff n else 0) :
    False := by
  have hL : (∑ n ∈ P'.support, if N ∣ (N - 1) + 2 * n then P'.coeff n else 0) = 0 := by
    refine sum_support_dvd_eq_zero fun n hn hd => ?_
    have hn' := hP' n (mem_support_iff.1 hn)
    have h1 := Nat.eq_of_dvd_of_lt_two_mul (by omega) hd (by omega)
    omega
  have hR : (∑ n ∈ P.support, if N ∣ (N - 1) + 1 * n then P.coeff n else 0) = P.coeff 1 := by
    refine sum_support_dvd_eq fun n hn => ?_
    have hn' := hP n (mem_support_iff.1 hn)
    refine ⟨fun hd => ?_, fun hn1 => ?_⟩
    · rw [one_mul, add_comm] at hd
      exact eq_one_of_dvd_add_pred (by omega) (by omega) hd
    · subst hn1
      exact ⟨1, by omega⟩
  rw [hL, hR, mul_zero, zero_mul] at key
  exact hP1 key.symm

theorem cubic_core_big {P P' : A[X]} {N σ q c : ℕ} {z : Aˣ} (hσ : 1 ≤ σ) (h4 : 4 * σ ≤ N)
    (hcop : Nat.Coprime c N) (hcN : c < N) (hcq : c < q) (hc4 : 4 ≤ c)
    (hP : ∀ n, P.coeff n ≠ 0 → n ≤ 3 * σ ∧ (n ≤ 3 ∨ q ≤ n))
    (hP' : ∀ n, P'.coeff n ≠ 0 → n ≤ 3 * σ) (hP'1 : P'.coeff 1 ≠ 0)
    (key : (z : A) * (∑ n ∈ P'.support, if N ∣ c * (N - 1) + c * n then P'.coeff n else 0) *
        (↑z⁻¹ : A) = ∑ n ∈ P.support, if N ∣ c * (N - 1) + 1 * n then P.coeff n else 0) :
    False := by
  have hL : (∑ n ∈ P'.support, if N ∣ c * (N - 1) + c * n then P'.coeff n else 0) =
      P'.coeff 1 := by
    refine sum_support_dvd_eq fun n hn => ?_
    have hn' := hP' n (mem_support_iff.1 hn)
    refine ⟨fun hd => eq_one_of_dvd_mul_pred_add_mul hcop (by omega) (by omega) hd, fun hn1 => ?_⟩
    subst hn1
    refine ⟨c, ?_⟩
    have := Nat.le_mul_of_pos_right c (show 0 < N by omega)
    rw [mul_one, Nat.mul_sub_one, Nat.mul_comm N c]
    omega
  have hR : (∑ n ∈ P.support, if N ∣ c * (N - 1) + 1 * n then P.coeff n else 0) = 0 := by
    refine sum_support_dvd_eq_zero fun n hn hd => ?_
    have hn' := hP n (mem_support_iff.1 hn)
    rw [one_mul] at hd
    have := eq_of_dvd_mul_pred_add (by omega) (by omega) hcN hd
    omega
  rw [hL, hR] at key
  exact hP'1 (conj_eq_zero z _ key)

end Core

section Main

variable {K L A : Type*} [Field K] [Fintype K] [DecidableEq K] [Field L] [Ring A] [Algebra L A]

theorem twisted_char_sum (ι : K →+* L) (c : ℕ) (P P' : A[X]) (z : Aˣ)
    (h : ∀ t : K, (z : A) * evAt ((ι t) ^ c) P' * (↑z⁻¹ : A) = evAt (ι t) P) (ν : ℕ) :
    (z : A) * (∑ n ∈ P'.support, if Fintype.card K - 1 ∣ ν + c * n then P'.coeff n else 0) *
        (↑z⁻¹ : A) =
      ∑ n ∈ P.support, if Fintype.card K - 1 ∣ ν + 1 * n then P.coeff n else 0 := by
  have e1 := sum_units_pow_smul_evAt (A := A) ι ν c P'
  have e2 := sum_units_pow_smul_evAt (A := A) ι ν 1 P
  simp only [pow_one] at e2
  have key : (z : A) * (∑ u : Kˣ, (ι (u : K)) ^ ν • evAt ((ι (u : K)) ^ c) P') * (↑z⁻¹ : A) =
      ∑ u : Kˣ, (ι (u : K)) ^ ν • evAt (ι (u : K)) P := by
    rw [Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun u _ => ?_
    rw [mul_smul_comm, smul_mul_assoc, h (u : K)]
  rw [e1, e2, mul_neg, neg_mul] at key
  exact neg_inj.1 key

theorem card_pred_eq_mul {q s : ℕ} (hq : 2 ≤ q) (hs : 0 < s) :
    1 ≤ ∑ k ∈ Finset.range s, q ^ k ∧
      q ^ s - 1 = (q - 1) * ∑ k ∈ Finset.range s, q ^ k := by
  have h := geom_sum_aux q s (by omega)
  refine ⟨?_, by omega⟩
  exact (Finset.single_le_sum (f := fun k => q ^ k) (fun _ _ => Nat.zero_le _)
    (Finset.mem_range.2 hs)).trans' (by simp)

theorem pow_coprime_lt_card_pred {r f j s : ℕ} (hr : r.Prime) (hj0 : 0 < j) (hjf : j < f)
    (hs : 0 < s) : Nat.Coprime (r ^ j) ((r ^ f) ^ s - 1) ∧ r ^ j < (r ^ f) ^ s - 1 := by
  have hr2 := hr.two_le
  have hcop : Nat.Coprime (r ^ j) ((r ^ f) ^ s - 1) := by
    refine Nat.Coprime.pow_left j ?_
    refine (Nat.Prime.coprime_iff_not_dvd hr).2 fun hdvd => ?_
    have h1 : r ∣ (r ^ f) ^ s := by
      rw [← pow_mul]
      exact dvd_pow_self r (Nat.mul_ne_zero (by omega) hs.ne')
    have h1' : 1 ≤ (r ^ f) ^ s := Nat.one_le_pow _ _ (pow_pos hr.pos f)
    have h2 : r ∣ ((r ^ f) ^ s - 1) + 1 := by rw [Nat.sub_add_cancel h1']; exact h1
    have h3 := (Nat.dvd_add_right hdvd).1 h2
    exact hr.one_lt.ne' (Nat.dvd_one.1 h3)
  have hcq : r ^ j < r ^ f := Nat.pow_lt_pow_right hr.one_lt hjf
  have hQq : r ^ f ≤ (r ^ f) ^ s := Nat.le_self_pow hs.ne' _
  have hc2 : 2 ≤ r ^ j := le_trans hr2 (Nat.le_self_pow hj0.ne' r)
  refine ⟨hcop, ?_⟩
  by_contra hge
  have hceq : r ^ j = (r ^ f) ^ s - 1 := by omega
  rw [hceq] at hcop
  have := (Nat.coprime_self _).1 hcop
  omega

theorem no_twisted_conj3 (ι : K →+* L) {r f j s : ℕ} (hr : r.Prime) (hj0 : 0 < j) (hjf : j < f)
    (hs : 0 < s) (hQ : Fintype.card K = (r ^ f) ^ s) (hq5 : 5 ≤ r ^ f) (hc3 : r ^ j ≠ 3)
    (hc2 : r ^ j = 2 → 7 ≤ r ^ f)
    (ks : List ℕ) (hnd : ks.Nodup) (h0 : 0 ∈ ks) (hks : ∀ k ∈ ks, k < s)
    (a b d a' b' d' : ℕ → A) (ha : a 0 ≠ 0) (ha' : a' 0 ≠ 0) (z : Aˣ)
    (h : ∀ t : K, (z : A) * evAt ((ι t) ^ (r ^ j)) (prodList3 (r ^ f) a' b' d' ks) *
      (↑z⁻¹ : A) = evAt (ι t) (prodList3 (r ^ f) a b d ks)) : False := by
  obtain ⟨hcop, hcN⟩ := pow_coprime_lt_card_pred hr hj0 hjf hs
  obtain ⟨hσ1, hNσ⟩ := card_pred_eq_mul (q := r ^ f) (by omega) hs
  rw [← hQ] at hcop hcN hNσ
  have hcq : r ^ j < r ^ f := Nat.pow_lt_pow_right hr.one_lt hjf
  have hc2' : 2 ≤ r ^ j := le_trans hr.two_le (Nat.le_self_pow hj0.ne' r)
  set N := Fintype.card K - 1 with hNdef
  set σ := ∑ k ∈ Finset.range s, (r ^ f) ^ k with hσdef
  have h4σ : 4 * σ ≤ N := by
    rw [hNσ]
    exact Nat.mul_le_mul_right σ (by omega)
  have hsupp := fun (a b d : ℕ → A) n (hn : (prodList3 (r ^ f) a b d ks).coeff n ≠ 0) =>
    support_bound3 ks hnd h0 hks a b d n hn
  have hcoef1 : ∀ (a b d : ℕ → A), (prodList3 (r ^ f) a b d ks).coeff 1 = a 0 := fun a b d => by
    rw [coeff_one_prodList3 (by omega) a b d ks hnd]
    simp only [h0, ↓reduceIte]
  by_cases hc : r ^ j = 2
  · have hk := twisted_char_sum ι (r ^ j) _ _ z h (N - 1)
    rw [hc] at hk
    have h6σ : 6 * σ ≤ N := by
      rw [hNσ]
      exact Nat.mul_le_mul_right σ (by have := hc2 hc; omega)
    exact cubic_core_two hσ1 h6σ (fun n hn => (hsupp a b d n hn).1)
      (fun n hn => (hsupp a' b' d' n hn).1) (by rw [hcoef1]; exact ha) hk
  · have hc4 : 4 ≤ r ^ j := by omega
    have hk := twisted_char_sum ι (r ^ j) _ _ z h (r ^ j * (N - 1))
    exact cubic_core_big hσ1 h4σ hcop hcN hcq hc4 (hsupp a b d)
      (fun n hn => (hsupp a' b' d' n hn).1) (by rw [hcoef1]; exact ha') hk

end Main

end CFSG.HardMathSupport.Timmesfeld.LangTorus

end

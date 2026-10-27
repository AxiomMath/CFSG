module

public import Mathlib.FieldTheory.Finite.Basic

public section

namespace CFSG.HardMathSupport.Timmesfeld.LangTorus

open Polynomial

section Eval

variable {L A : Type*} [Field L] [Ring A] [Algebra L A]

@[expose] noncomputable def evAt (u : L) : A[X] →+* A :=
  Polynomial.eval₂RingHom' (RingHom.id A) (algebraMap L A u)
    fun a => (Algebra.commutes u a).symm

theorem evAt_apply (u : L) (p : A[X]) :
    evAt u p = p.eval₂ (RingHom.id A) (algebraMap L A u) := rfl

theorem evAt_C (u : L) (a : A) : evAt u (C a) = a := by
  rw [evAt_apply, eval₂_C]
  rfl

theorem evAt_X (u : L) : evAt (A := A) u X = algebraMap L A u := by
  rw [evAt_apply, eval₂_X]

theorem evAt_monomial (u : L) (n : ℕ) (a : A) : evAt u (monomial n a) = u ^ n • a := by
  rw [← C_mul_X_pow_eq_monomial, map_mul, evAt_C, map_pow, evAt_X, ← map_pow,
    Algebra.smul_def, (Algebra.commutes (u ^ n) a).symm]

theorem evAt_eq_sum (u : L) (p : A[X]) :
    evAt u p = ∑ n ∈ p.support, u ^ n • p.coeff n := by
  conv_lhs => rw [p.as_sum_support]
  rw [map_sum]
  exact Finset.sum_congr rfl fun n _ => evAt_monomial u n _

end Eval

section Prod

variable {L A : Type*} [Field L] [Ring A] [Algebra L A]

@[expose] noncomputable def fac (w : ℕ) (a b : A) : A[X] :=
  1 + C a * X ^ w + C b * X ^ (2 * w)

@[expose] noncomputable def prodList (q : ℕ) (a b : ℕ → A) (ks : List ℕ) : A[X] :=
  (ks.map fun k => fac (q ^ k) (a k) (b k)).prod

theorem evAt_fac (u : L) (w : ℕ) (a b : A) :
    evAt u (fac w a b) = 1 + u ^ w • a + u ^ (2 * w) • b := by
  unfold fac
  rw [map_add, map_add, map_one, map_mul, map_mul, evAt_C, evAt_C, map_pow, map_pow, evAt_X,
    ← map_pow, ← map_pow, Algebra.smul_def, Algebra.smul_def,
    (Algebra.commutes (u ^ w) a), (Algebra.commutes (u ^ (2 * w)) b)]

theorem evAt_prodList (u : L) (q : ℕ) (a b : ℕ → A) (ks : List ℕ) :
    evAt u (prodList q a b ks) =
      (ks.map fun k => 1 + u ^ (q ^ k) • a k + u ^ (2 * q ^ k) • b k).prod := by
  unfold prodList
  rw [map_list_prod, List.map_map]
  congr 1
  refine List.map_congr_left fun k _ => ?_
  exact evAt_fac u _ _ _

theorem prodList_cons (q : ℕ) (a b : ℕ → A) (k : ℕ) (ks : List ℕ) :
    prodList q a b (k :: ks) = fac (q ^ k) (a k) (b k) * prodList q a b ks := by
  simp [prodList]

theorem coeff_fac_mul (w : ℕ) (a b : A) (p : A[X]) (n : ℕ) :
    (fac w a b * p).coeff n = p.coeff n + (if w ≤ n then a * p.coeff (n - w) else 0) +
      (if 2 * w ≤ n then b * p.coeff (n - 2 * w) else 0) := by
  unfold fac
  rw [add_mul, add_mul, one_mul, mul_assoc, mul_assoc, coeff_add, coeff_add, coeff_C_mul,
    coeff_C_mul, coeff_X_pow_mul', coeff_X_pow_mul']
  simp only [mul_ite, mul_zero]

end Prod

section Support

variable {A : Type*} [Ring A]

@[expose] def Aset (q : ℕ) : List ℕ → Set ℕ
  | [] => {0}
  | k :: ks => {n | n ∈ Aset q ks ∨ (q ^ k ≤ n ∧ n - q ^ k ∈ Aset q ks) ∨
      (2 * q ^ k ≤ n ∧ n - 2 * q ^ k ∈ Aset q ks)}

theorem coeff_zero_prodList {q : ℕ} (hq : 1 ≤ q) (a b : ℕ → A) (ks : List ℕ) :
    (prodList q a b ks).coeff 0 = 1 := by
  induction ks with
  | nil => simp [prodList]
  | cons k ks ih =>
    rw [prodList_cons, coeff_fac_mul, ih]
    have h1 : 1 ≤ q ^ k := Nat.one_le_pow _ _ hq
    simp only [Nat.le_zero, (show q ^ k ≠ 0 by omega), (show 2 * q ^ k ≠ 0 by omega), ↓reduceIte]
    simp

theorem mem_Aset_of_coeff_ne_zero (q : ℕ) (a b : ℕ → A) (ks : List ℕ) (n : ℕ)
    (h : (prodList q a b ks).coeff n ≠ 0) : n ∈ Aset q ks := by
  induction ks generalizing n with
  | nil =>
    have hp : prodList q a b ([] : List ℕ) = 1 := by simp [prodList]
    rw [hp, coeff_one] at h
    by_cases hn : n = 0
    · simp [Aset, hn]
    · simp only [hn, ↓reduceIte] at h
      exact absurd rfl h
  | cons k ks ih =>
    rw [prodList_cons, coeff_fac_mul] at h
    by_cases h1 : (prodList q a b ks).coeff n = 0
    · by_cases h2 : q ^ k ≤ n ∧ (prodList q a b ks).coeff (n - q ^ k) ≠ 0
      · exact Or.inr (Or.inl ⟨h2.1, ih _ h2.2⟩)
      · have h3 : 2 * q ^ k ≤ n ∧ (prodList q a b ks).coeff (n - 2 * q ^ k) ≠ 0 := by
          by_contra h3
          apply h
          rw [h1]
          have e2 : (if q ^ k ≤ n then a k * (prodList q a b ks).coeff (n - q ^ k) else 0) = 0 := by
            by_cases hle : q ^ k ≤ n
            · simp only [hle, ↓reduceIte]
              by_cases hc : (prodList q a b ks).coeff (n - q ^ k) = 0
              · rw [hc, mul_zero]
              · exact absurd ⟨hle, hc⟩ h2
            · simp only [hle, ↓reduceIte]
          have e3 : (if 2 * q ^ k ≤ n then b k * (prodList q a b ks).coeff (n - 2 * q ^ k)
              else 0) = 0 := by
            by_cases hle : 2 * q ^ k ≤ n
            · simp only [hle, ↓reduceIte]
              by_cases hc : (prodList q a b ks).coeff (n - 2 * q ^ k) = 0
              · rw [hc, mul_zero]
              · exact absurd ⟨hle, hc⟩ h3
            · simp only [hle, ↓reduceIte]
          rw [e2, e3]
          simp
        exact Or.inr (Or.inr ⟨h3.1, ih _ h3.2⟩)
    · exact Or.inl (ih n h1)

end Support

section Bounds

variable {A : Type*} [Ring A]

theorem Aset_le (q : ℕ) (ks : List ℕ) : ∀ n ∈ Aset q ks, n ≤ 2 * (ks.map (q ^ ·)).sum := by
  induction ks with
  | nil =>
    intro n hn
    simp only [Aset, Set.mem_singleton_iff] at hn
    omega
  | cons k ks ih =>
    intro n hn
    simp only [List.map_cons, List.sum_cons]
    rcases hn with hn | ⟨h1, hn⟩ | ⟨h1, hn⟩
    · have := ih n hn
      omega
    · have := ih _ hn
      omega
    · have := ih _ hn
      omega

theorem Aset_small (q : ℕ) (ks : List ℕ) (hnd : ks.Nodup) :
    ∀ n ∈ Aset q ks, (0 ∈ ks → n ≤ 2 ∨ q ≤ n) ∧ (0 ∉ ks → n = 0 ∨ q ≤ n) := by
  induction ks with
  | nil =>
    intro n hn
    simp only [Aset, Set.mem_singleton_iff] at hn
    subst hn
    simp
  | cons k ks ih =>
    intro n hn
    have hk : k ∉ ks := (List.nodup_cons.1 hnd).1
    have ih' := ih (List.nodup_cons.1 hnd).2
    by_cases hk0 : k = 0
    · subst hk0
      have h0 : (0 : ℕ) ∉ ks := hk
      refine ⟨fun _ => ?_, fun h => absurd (List.mem_cons_self) h⟩
      rcases hn with hn | ⟨h1, hn⟩ | ⟨h1, hn⟩
      · rcases (ih' n hn).2 h0 with h | h <;> omega
      · rcases (ih' _ hn).2 h0 with h | h <;> (simp only [pow_zero] at h1 h; omega)
      · rcases (ih' _ hn).2 h0 with h | h <;> (simp only [pow_zero] at h1 h; omega)
    · have hqk : q ≤ q ^ k := Nat.le_self_pow hk0 q
      have hmem : (0 ∈ k :: ks) ↔ (0 ∈ ks) := by
        simp [Ne.symm hk0]
      rw [hmem]
      rcases hn with hn | ⟨h1, hn⟩ | ⟨h1, hn⟩
      · exact ih' n hn
      · exact ⟨fun _ => Or.inr (by omega), fun _ => Or.inr (by omega)⟩
      · exact ⟨fun _ => Or.inr (by omega), fun _ => Or.inr (by omega)⟩

theorem coeff_one_prodList {q : ℕ} (hq : 2 ≤ q) (a b : ℕ → A) (ks : List ℕ) (hnd : ks.Nodup) :
    (prodList q a b ks).coeff 1 = if 0 ∈ ks then a 0 else 0 := by
  induction ks with
  | nil => simp [prodList, coeff_one]
  | cons k ks ih =>
    have hk : k ∉ ks := (List.nodup_cons.1 hnd).1
    have ih' := ih (List.nodup_cons.1 hnd).2
    rw [prodList_cons, coeff_fac_mul, ih']
    by_cases hk0 : k = 0
    · subst hk0
      have h0 : (0 : ℕ) ∉ ks := hk
      simp [h0, coeff_zero_prodList (by omega : 1 ≤ q)]
    · have hqk : q ≤ q ^ k := Nat.le_self_pow hk0 q
      have h1 : ¬ q ^ k ≤ 1 := by omega
      have h2 : ¬ 2 * q ^ k ≤ 1 := by omega
      have hmem : (0 ∈ k :: ks) ↔ (0 ∈ ks) := by simp [Ne.symm hk0]
      simp [h1, h2, hmem]

theorem coeff_two_prodList {q : ℕ} (hq : 3 ≤ q) (a b : ℕ → A) (ks : List ℕ) (hnd : ks.Nodup) :
    (prodList q a b ks).coeff 2 = if 0 ∈ ks then b 0 else 0 := by
  induction ks with
  | nil => simp [prodList, coeff_one]
  | cons k ks ih =>
    have hk : k ∉ ks := (List.nodup_cons.1 hnd).1
    have ih' := ih (List.nodup_cons.1 hnd).2
    rw [prodList_cons, coeff_fac_mul, ih']
    by_cases hk0 : k = 0
    · subst hk0
      have h0 : (0 : ℕ) ∉ ks := hk
      have h1 : (prodList q a b ks).coeff 1 = 0 := by
        rw [coeff_one_prodList (by omega) a b ks (List.nodup_cons.1 hnd).2]
        simp [h0]
      simp [h0, h1, coeff_zero_prodList (by omega : 1 ≤ q)]
    · have hqk : q ≤ q ^ k := Nat.le_self_pow hk0 q
      have h1 : ¬ q ^ k ≤ 2 := by omega
      have h2 : ¬ 2 * q ^ k ≤ 2 := by omega
      have hmem : (0 ∈ k :: ks) ↔ (0 ∈ ks) := by simp [Ne.symm hk0]
      simp [h1, h2, hmem]

end Bounds

theorem geom_sum_aux (q s : ℕ) (hq : 1 ≤ q) :
    (q - 1) * ∑ k ∈ Finset.range s, q ^ k + 1 = q ^ s := by
  obtain ⟨m, rfl⟩ : ∃ m, q = m + 1 := ⟨q - 1, by omega⟩
  induction s with
  | zero => simp
  | succ s ih =>
    rw [Finset.sum_range_succ, Nat.add_sub_cancel, pow_succ]
    simp only [Nat.add_sub_cancel] at ih
    nlinarith [ih]

theorem sum_pow_list_le (q s : ℕ) (ks : List ℕ) (hnd : ks.Nodup) (hks : ∀ k ∈ ks, k < s) :
    (ks.map (q ^ ·)).sum ≤ ∑ k ∈ Finset.range s, q ^ k := by
  rw [← List.sum_toFinset (fun k => q ^ k) hnd]
  refine Finset.sum_le_sum_of_subset ?_
  intro k hk
  rw [List.mem_toFinset] at hk
  exact Finset.mem_range.2 (hks k hk)

section Char

variable {K L A : Type*} [Field K] [Fintype K] [DecidableEq K] [Field L] [Ring A] [Algebra L A]

theorem sum_units_pow_smul_evAt (ι : K →+* L) (ν e : ℕ) (p : A[X]) :
    ∑ u : Kˣ, (ι (u : K)) ^ ν • evAt ((ι (u : K)) ^ e) p =
      -(∑ n ∈ p.support, if Fintype.card K - 1 ∣ ν + e * n then p.coeff n else 0) := by
  simp_rw [evAt_eq_sum, Finset.smul_sum, smul_smul, ← pow_mul, ← pow_add]
  rw [Finset.sum_comm, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [← Finset.sum_smul]
  have h := FiniteField.sum_pow_units K (ν + e * n)
  have h2 : ∑ u : Kˣ, (ι (u : K)) ^ (ν + e * n) =
      ι (∑ u : Kˣ, ((u : K) ^ (ν + e * n))) := by
    simp [map_sum, map_pow]
  rw [h2, h]
  split_ifs <;> simp

end Char

section Main

variable {K L A : Type*} [Field K] [Fintype K] [DecidableEq K] [Field L] [Ring A] [Algebra L A]

theorem conj_eq_zero (z : Aˣ) (x : A) (h : (z : A) * x * (↑z⁻¹ : A) = 0) : x = 0 := by
  have := congrArg (fun m => (↑z⁻¹ : A) * m * (z : A)) h
  simpa [mul_assoc] using this

theorem eq_one_of_dvd_add_pred {N n : ℕ} (hN : 2 ≤ N) (hn : n < N) (h : N ∣ n + (N - 1)) :
    n = 1 := by
  have := Nat.eq_of_dvd_of_lt_two_mul (by omega) h (by omega)
  omega

theorem support_bound {q s : ℕ} (ks : List ℕ) (hnd : ks.Nodup)
    (h0 : 0 ∈ ks) (hks : ∀ k ∈ ks, k < s) (a b : ℕ → A) (n : ℕ)
    (hn : (prodList q a b ks).coeff n ≠ 0) :
    n ≤ 2 * ∑ k ∈ Finset.range s, q ^ k ∧ (n ≤ 2 ∨ q ≤ n) := by
  have hmem := mem_Aset_of_coeff_ne_zero q a b ks n hn
  refine ⟨(Aset_le q ks n hmem).trans (Nat.mul_le_mul_left _ (sum_pow_list_le q s ks hnd hks)),
    (Aset_small q ks hnd n hmem).1 h0⟩

theorem no_twisted_conj (ι : K →+* L) {r f j s : ℕ} (hr : r.Prime) (hj0 : 0 < j) (hjf : j < f)
    (hs : 0 < s) (hQ : Fintype.card K = (r ^ f) ^ s) (hq4 : 4 ≤ r ^ f)
    (hc2 : r ^ j = 2 → 8 ≤ r ^ f)
    (ks : List ℕ) (hnd : ks.Nodup) (h0 : 0 ∈ ks) (hks : ∀ k ∈ ks, k < s)
    (a b a' b' : ℕ → A) (ha : a 0 ≠ 0) (ha' : a' 0 ≠ 0) (z : Aˣ)
    (h : ∀ t : K, (z : A) * evAt ((ι t) ^ (r ^ j)) (prodList (r ^ f) a' b' ks) * (↑z⁻¹ : A) =
      evAt (ι t) (prodList (r ^ f) a b ks)) : False := by
  classical
  set q := r ^ f with hqdef
  set c := r ^ j with hcdef
  set σ := ∑ k ∈ Finset.range s, q ^ k with hσdef
  have hr2 := hr.two_le
  have hcq : c < q := Nat.pow_lt_pow_right hr.one_lt hjf
  have hc2' : 2 ≤ c := (le_trans hr2 (Nat.le_self_pow hj0.ne' r))
  have hσ : (q - 1) * σ + 1 = q ^ s := geom_sum_aux q s (by omega)
  set N := Fintype.card K - 1 with hNdef
  have hQq : q ≤ q ^ s := Nat.le_self_pow hs.ne' q
  have hNeq : N + 1 = q ^ s := by
    have : 1 ≤ Fintype.card K := Fintype.card_pos
    omega
  have hNσ : N = (q - 1) * σ := by omega
  have hσ1 : 1 ≤ σ := by
    rw [hσdef]
    exact (Finset.single_le_sum (f := fun k => q ^ k) (fun _ _ => Nat.zero_le _)
      (Finset.mem_range.2 hs)).trans' (by simp)
  have h3σ : 3 * σ ≤ N := by
    rw [hNσ]
    exact Nat.mul_le_mul_right σ (by omega)
  have hN3 : 3 ≤ N := by omega
  have hcop : Nat.Coprime c N := by
    refine Nat.Coprime.pow_left j ?_
    refine (Nat.Prime.coprime_iff_not_dvd hr).2 fun hdvd => ?_
    have h1 : r ∣ q ^ s := by
      rw [hqdef, ← pow_mul]
      exact dvd_pow_self r (Nat.mul_ne_zero (by omega) hs.ne')
    have h2 : r ∣ N + 1 := by rw [hNeq]; exact h1
    have h3 := (Nat.dvd_add_right hdvd).1 h2
    exact hr.one_lt.ne' (Nat.dvd_one.1 h3)
  have hcN : c < N := by
    by_contra hge
    have hle : c ≤ N := by
      have : q ≤ N + 1 := by omega
      omega
    have hceq : c = N := by omega
    rw [hceq] at hcop
    have := (Nat.coprime_self N).1 hcop
    omega
  have hsupp := fun (a b : ℕ → A) n (hn : (prodList q a b ks).coeff n ≠ 0) =>
    support_bound ks hnd h0 hks a b n hn
  have key : ∀ ν : ℕ,
      (z : A) * (-(∑ n ∈ (prodList q a' b' ks).support,
          if N ∣ ν + c * n then (prodList q a' b' ks).coeff n else 0)) * (↑z⁻¹ : A) =
        -(∑ n ∈ (prodList q a b ks).support,
          if N ∣ ν + 1 * n then (prodList q a b ks).coeff n else 0) := by
    intro ν
    have e1 := sum_units_pow_smul_evAt (A := A) ι ν c (prodList q a' b' ks)
    have e2 := sum_units_pow_smul_evAt (A := A) ι ν 1 (prodList q a b ks)
    simp only [pow_one] at e2
    rw [← e1, ← e2]
    rw [Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun u _ => ?_
    rw [mul_smul_comm, smul_mul_assoc, h (u : K)]
  have hcoef1 : ∀ (a b : ℕ → A), (prodList q a b ks).coeff 1 = a 0 := fun a b => by
    rw [coeff_one_prodList (by omega) a b ks hnd]
    simp only [h0, ↓reduceIte]
  by_cases hc : c = 2
  ·
    have hq8 : 8 ≤ q := hc2 hc
    have h7σ : 7 * σ ≤ N := by
      rw [hNσ]
      exact Nat.mul_le_mul_right σ (by omega)
    have hk := key (N - 1)
    have hL : (∑ n ∈ (prodList q a' b' ks).support,
        if N ∣ (N - 1) + c * n then (prodList q a' b' ks).coeff n else 0) = 0 := by
      refine Finset.sum_eq_zero fun n hn => ?_
      rw [Polynomial.mem_support_iff] at hn
      obtain ⟨hn1, -⟩ := hsupp a' b' n hn
      have hnd' : ¬ N ∣ (N - 1) + c * n := by
        intro hd
        rw [hc] at hd
        have h1 := Nat.eq_of_dvd_of_lt_two_mul (by omega) hd (by omega)
        omega
      simp only [hnd', ↓reduceIte]
    have hR : (∑ n ∈ (prodList q a b ks).support,
        if N ∣ (N - 1) + 1 * n then (prodList q a b ks).coeff n else 0) = a 0 := by
      rw [Finset.sum_eq_single 1]
      · have hdv : N ∣ (N - 1) + 1 * 1 := by
          rw [one_mul]
          exact ⟨1, by omega⟩
        simp only [hdv, ↓reduceIte]
        exact hcoef1 a b
      · intro n hn hn1
        rw [Polynomial.mem_support_iff] at hn
        obtain ⟨hn2, -⟩ := hsupp a b n hn
        have hnd' : ¬ N ∣ (N - 1) + 1 * n := by
          intro hd
          rw [one_mul, add_comm] at hd
          have := eq_one_of_dvd_add_pred (by omega) (by omega) hd
          omega
        simp only [hnd', ↓reduceIte]
      · intro hn
        rw [Polynomial.mem_support_iff, not_not] at hn
        simp [hn]
    rw [hL, hR] at hk
    simp only [neg_zero, mul_zero, zero_mul] at hk
    exact ha (neg_eq_zero.1 hk.symm)
  ·
    have hc3 : 3 ≤ c := by omega
    have hk := key (c * (N - 1))
    have hL : (∑ n ∈ (prodList q a' b' ks).support,
        if N ∣ c * (N - 1) + c * n then (prodList q a' b' ks).coeff n else 0) = a' 0 := by
      rw [Finset.sum_eq_single 1]
      · have hdv : N ∣ c * (N - 1) + c * 1 := ⟨c, by
          rw [mul_one, Nat.mul_sub_one, Nat.mul_comm N c]
          have := Nat.le_mul_of_pos_right c (show 0 < N by omega)
          omega⟩
        simp only [hdv, ↓reduceIte]
        exact hcoef1 a' b'
      · intro n hn hn1
        rw [Polynomial.mem_support_iff] at hn
        obtain ⟨hn2, -⟩ := hsupp a' b' n hn
        have hnd' : ¬ N ∣ c * (N - 1) + c * n := by
          intro hd
          rw [← Nat.mul_add] at hd
          have h1 := (Nat.Coprime.dvd_of_dvd_mul_left hcop.symm hd)
          rw [add_comm] at h1
          have := eq_one_of_dvd_add_pred (by omega) (by omega) h1
          omega
        simp only [hnd', ↓reduceIte]
      · intro hn
        rw [Polynomial.mem_support_iff, not_not] at hn
        simp [hn]
    have hR : (∑ n ∈ (prodList q a b ks).support,
        if N ∣ c * (N - 1) + 1 * n then (prodList q a b ks).coeff n else 0) = 0 := by
      refine Finset.sum_eq_zero fun n hn => ?_
      rw [Polynomial.mem_support_iff] at hn
      obtain ⟨hn1, hn2⟩ := hsupp a b n hn
      have hnd' : ¬ N ∣ c * (N - 1) + 1 * n := by
        intro hd
        have hd' : (N : ℤ) ∣ (c : ℤ) * ((N : ℤ) - 1) + n := by
          have := Int.natCast_dvd_natCast.2 hd
          push_cast [Nat.cast_sub (by omega : 1 ≤ N)] at this
          simpa using this
        have hd'' : (N : ℤ) ∣ (n : ℤ) - c := by
          have h2 : (N : ℤ) ∣ (c : ℤ) * N := dvd_mul_left _ _
          have h3 := dvd_sub hd' h2
          have e : (c : ℤ) * ((N : ℤ) - 1) + n - (c : ℤ) * N = (n : ℤ) - c := by ring
          rwa [e] at h3
        have h4 := Int.eq_zero_of_abs_lt_dvd hd'' (abs_lt.2 ⟨by omega, by omega⟩)
        have h5 : n = c := by omega
        omega
      simp only [hnd', ↓reduceIte]
    rw [hL, hR, neg_zero] at hk
    exact ha' (neg_eq_zero.1 (conj_eq_zero z _ hk))

theorem twisted_conj_q4 (ι : K →+* L) {s : ℕ} (hs : 0 < s) (hQ : Fintype.card K = 4 ^ s)
    (ks : List ℕ) (hnd : ks.Nodup) (h0 : 0 ∈ ks) (hks : ∀ k ∈ ks, k < s)
    (a b a' b' : ℕ → A) (z : Aˣ)
    (h : ∀ t : K, (z : A) * evAt ((ι t) ^ 2) (prodList 4 a' b' ks) * (↑z⁻¹ : A) =
      evAt (ι t) (prodList 4 a b ks)) : (z : A) * a' 0 * (↑z⁻¹ : A) = b 0 := by
  classical
  set σ := ∑ k ∈ Finset.range s, 4 ^ k with hσdef
  have hσ : (4 - 1) * σ + 1 = 4 ^ s := geom_sum_aux 4 s (by omega)
  set N := Fintype.card K - 1 with hNdef
  have hQq : 4 ≤ 4 ^ s := Nat.le_self_pow hs.ne' 4
  have hNeq : N + 1 = 4 ^ s := by
    have : 1 ≤ Fintype.card K := Fintype.card_pos
    omega
  have hσ1 : 1 ≤ σ := by
    rw [hσdef]
    exact (Finset.single_le_sum (f := fun k => 4 ^ k) (fun _ _ => Nat.zero_le _)
      (Finset.mem_range.2 hs)).trans' (by simp)
  have h3σ : 3 * σ = N := by omega
  have hN3 : 3 ≤ N := by omega
  have hNodd : N % 2 = 1 := by
    have : 2 ∣ 4 ^ s := dvd_pow (by norm_num) hs.ne'
    omega
  have hcop : Nat.Coprime N 2 := Nat.coprime_two_right.2 (Nat.odd_iff.2 hNodd)
  have hsupp := fun (a b : ℕ → A) n (hn : (prodList 4 a b ks).coeff n ≠ 0) =>
    support_bound ks hnd h0 hks a b n hn
  have key : ∀ ν : ℕ,
      (z : A) * (-(∑ n ∈ (prodList 4 a' b' ks).support,
          if N ∣ ν + 2 * n then (prodList 4 a' b' ks).coeff n else 0)) * (↑z⁻¹ : A) =
        -(∑ n ∈ (prodList 4 a b ks).support,
          if N ∣ ν + 1 * n then (prodList 4 a b ks).coeff n else 0) := by
    intro ν
    have e1 := sum_units_pow_smul_evAt (A := A) ι ν 2 (prodList 4 a' b' ks)
    have e2 := sum_units_pow_smul_evAt (A := A) ι ν 1 (prodList 4 a b ks)
    simp only [pow_one] at e2
    rw [← e1, ← e2]
    rw [Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun u _ => ?_
    rw [mul_smul_comm, smul_mul_assoc, h (u : K)]
  have hk := key (2 * (N - 1))
  have hL : (∑ n ∈ (prodList 4 a' b' ks).support,
      if N ∣ 2 * (N - 1) + 2 * n then (prodList 4 a' b' ks).coeff n else 0) = a' 0 := by
    rw [Finset.sum_eq_single 1]
    · have hdv : N ∣ 2 * (N - 1) + 2 * 1 := ⟨2, by omega⟩
      simp only [hdv, ↓reduceIte]
      rw [coeff_one_prodList (by omega) a' b' ks hnd]
      simp [h0]
    · intro n hn hn1
      rw [Polynomial.mem_support_iff] at hn
      obtain ⟨hn2, -⟩ := hsupp a' b' n hn
      have hnd' : ¬ N ∣ 2 * (N - 1) + 2 * n := by
        intro hd
        rw [← Nat.mul_add] at hd
        have h1 := Nat.Coprime.dvd_of_dvd_mul_left hcop hd
        rw [add_comm] at h1
        have := eq_one_of_dvd_add_pred (by omega) (by omega) h1
        omega
      simp only [hnd', ↓reduceIte]
    · intro hn
      rw [Polynomial.mem_support_iff, not_not] at hn
      simp [hn]
  have hR : (∑ n ∈ (prodList 4 a b ks).support,
      if N ∣ 2 * (N - 1) + 1 * n then (prodList 4 a b ks).coeff n else 0) = b 0 := by
    rw [Finset.sum_eq_single 2]
    · have hdv : N ∣ 2 * (N - 1) + 1 * 2 := ⟨2, by omega⟩
      simp only [hdv, ↓reduceIte]
      rw [coeff_two_prodList (by norm_num) a b ks hnd]
      simp [h0]
    · intro n hn hn1
      rw [Polynomial.mem_support_iff] at hn
      obtain ⟨hn2, -⟩ := hsupp a b n hn
      have hnd' : ¬ N ∣ 2 * (N - 1) + 1 * n := by
        intro hd
        have hd' : (N : ℤ) ∣ 2 * ((N : ℤ) - 1) + n := by
          have := Int.natCast_dvd_natCast.2 hd
          push_cast [Nat.cast_sub (by omega : 1 ≤ N)] at this
          simpa using this
        have hd'' : (N : ℤ) ∣ (n : ℤ) - 2 := by
          have h2 : (N : ℤ) ∣ 2 * (N : ℤ) := dvd_mul_left _ _
          have h3 := dvd_sub hd' h2
          have e : 2 * ((N : ℤ) - 1) + n - 2 * (N : ℤ) = (n : ℤ) - 2 - 0 := by ring
          rw [e] at h3
          simpa using h3
        have h4 := Int.eq_zero_of_abs_lt_dvd hd'' (abs_lt.2 ⟨by omega, by omega⟩)
        omega
      simp only [hnd', ↓reduceIte]
    · intro hn
      rw [Polynomial.mem_support_iff, not_not] at hn
      simp [hn]
  rw [hL, hR] at hk
  rw [mul_neg, neg_mul] at hk
  exact neg_inj.1 hk

end Main

end CFSG.HardMathSupport.Timmesfeld.LangTorus

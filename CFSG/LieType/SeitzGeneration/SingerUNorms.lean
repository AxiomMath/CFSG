module

public import CFSG.LieType.SeitzGeneration.HeisTorusUDefs

public section

namespace CFSG.LieType.SeitzGeneration

open Matrix CFSG.LocalAnalysis.ComponentInitial

variable {ℓ f : ℕ} {K : Type} [Field K]

theorem singer_seq_no_reflection {F : Type} [Field F] {p : ℕ} (hp5 : 5 ≤ p)
    {n n₀ : F} (hn : n ≠ 0) (hn2 : n ^ 2 ≠ 1) (hn₀ : n₀ ≠ 0) {N : ZMod p → F}
    (h0 : N 0 = n₀) (hk : ∀ k : ℕ, 2 ≤ k → k < p → N (k : ZMod p) = n ^ (p - k) * n₀) :
    ¬ ∃ r : ZMod p, ∀ j : ZMod p, N j = N (r - j) := by
  haveI : NeZero p := ⟨by omega⟩
  rintro ⟨r, hr⟩
  have hval : ∀ x : ZMod p, x ≠ 0 → x ≠ 1 →
      2 ≤ x.val ∧ x.val < p ∧ N x = n ^ (p - x.val) * n₀ := by
    intro x hx0 hx1
    have hxv : ((x.val : ℕ) : ZMod p) = x := ZMod.natCast_zmod_val x
    have h2 : 2 ≤ x.val := by
      by_contra hlt
      rcases (by omega : x.val = 0 ∨ x.val = 1) with h | h
      · exact hx0 (by rw [← hxv, h, Nat.cast_zero])
      · exact hx1 (by rw [← hxv, h, Nat.cast_one])
    have hlt : x.val < p := ZMod.val_lt x
    refine ⟨h2, hlt, ?_⟩
    have := hk x.val h2 hlt
    rw [hxv] at this
    exact this
  have hreg : ∀ x : ZMod p, x ≠ 0 → x ≠ 1 → N x = n * N (x + 1) := by
    intro x hx0 hx1
    obtain ⟨h2, hlt, hNx⟩ := hval x hx0 hx1
    have hxv : ((x.val : ℕ) : ZMod p) = x := ZMod.natCast_zmod_val x
    have hsucc : x + 1 = ((x.val + 1 : ℕ) : ZMod p) := by
      push_cast
      rw [hxv]
    rcases Nat.lt_or_ge (x.val + 1) p with hs | hs
    · rw [hsucc, hk (x.val + 1) (by omega) hs, hNx]
      have he : p - x.val = (p - (x.val + 1)) + 1 := by omega
      rw [he, pow_succ]
      ring
    · have hpv : x.val + 1 = p := by omega
      have hx1' : x + 1 = 0 := by
        rw [hsucc, hpv, ZMod.natCast_self]
      rw [hx1', h0, hNx]
      have he : p - x.val = 1 := by omega
      rw [he, pow_one]
  have hB : ∀ x : ZMod p, x ≠ r - 1 → x ≠ r - 2 → N (x + 1) = n * N x := by
    intro x h1 h2
    have hj0 : r - 1 - x ≠ 0 := fun h => h1 (by linear_combination -h)
    have hj1 : r - 1 - x ≠ 1 := fun h => h2 (by linear_combination -h)
    have e1 := hr (r - 1 - x)
    have e2 := hr (r - 1 - x + 1)
    have f1 : r - (r - 1 - x) = x + 1 := by ring
    have f2 : r - (r - 1 - x + 1) = x := by ring
    rw [f1] at e1
    rw [f2] at e2
    have hA := hreg (r - 1 - x) hj0 hj1
    rw [← e1, hA, e2]
  obtain ⟨x, hx⟩ : ∃ x : ZMod p, x ∉ ({0, 1, r - 1, r - 2} : Finset (ZMod p)) := by
    by_contra hcon
    push Not at hcon
    have hsub : (Finset.univ : Finset (ZMod p)) ⊆ {0, 1, r - 1, r - 2} :=
      fun y _ => hcon y
    have h1 := Finset.card_le_card hsub
    rw [Finset.card_univ, ZMod.card] at h1
    have h2 := (Finset.card_le_four : ({0, 1, r - 1, r - 2} : Finset (ZMod p)).card ≤ 4)
    omega
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hx
  obtain ⟨hx0, hx1, hx2, hx3⟩ := hx
  have hA := hreg x hx0 hx1
  have hB' := hB x hx2 hx3
  obtain ⟨-, -, hNx⟩ := hval x hx0 hx1
  have hNx0 : N x ≠ 0 := by
    rw [hNx]
    exact mul_ne_zero (pow_ne_zero _ hn) hn₀
  have key : N x * n ^ 2 = N x * 1 := by
    linear_combination (-1 : F) * hA - n * hB'
  exact hn2 (mul_left_cancel₀ hNx0 key)

theorem singerU_nat_sq_sub_one (q : ℕ) (hq : 1 ≤ q) : q * q - 1 = (q - 1) * (q + 1) := by
  obtain ⟨m, rfl⟩ : ∃ m, q = m + 1 := ⟨q - 1, by omega⟩
  rw [Nat.add_sub_cancel, show (m + 1) * (m + 1) = m * (m + 1 + 1) + 1 by ring,
    Nat.add_sub_cancel]

theorem singerU_norm_eq_pow (h : UnitaryFieldData ℓ f K) (x : K) :
    h.norm x = x ^ (ℓ ^ f + 1) := by
  rw [UnitaryFieldData.norm, UnitaryFieldData.bar_apply, pow_succ']

theorem singerU_norm_fixed (h : UnitaryFieldData ℓ f K) (x : K) :
    h.bar (h.norm x) = h.norm x := by
  rw [UnitaryFieldData.norm, map_mul, h.bar_bar, mul_comm]

theorem singerU_norm_mul (h : UnitaryFieldData ℓ f K) (x y : K) :
    h.norm (x * y) = h.norm x * h.norm y := by
  simp only [UnitaryFieldData.norm, map_mul]
  ring

theorem singerU_norm_pow (h : UnitaryFieldData ℓ f K) (x : K) (k : ℕ) :
    h.norm (x ^ k) = h.norm x ^ k := by
  simp only [UnitaryFieldData.norm, map_pow]
  rw [mul_pow]

theorem singerU_bar_eq_inv_of_norm_one (h : UnitaryFieldData ℓ f K) {x : K}
    (hx : h.norm x = 1) : h.bar x = x⁻¹ := by
  have hx' : x * h.bar x = 1 := hx
  exact eq_inv_of_mul_eq_one_right hx'

theorem singerU_norm_ne_zero (h : UnitaryFieldData ℓ f K) {x : K} (hx : x ≠ 0) :
    h.norm x ≠ 0 :=
  mul_ne_zero hx ((map_ne_zero h.bar).2 hx)

theorem singerU_pow_card_of_fixed (h : UnitaryFieldData ℓ f K) {x : K} (hx : h.bar x = x) :
    x ^ (ℓ ^ f) = x := by
  rw [← UnitaryFieldData.bar_apply]
  exact hx

theorem singerU_exists_norm_one_eval_ne (h : UnitaryFieldData ℓ f K) {P : Polynomial K}
    (hP : P ≠ 0) (hdeg : P.natDegree < ℓ ^ f + 1) :
    ∃ x : K, h.norm x = 1 ∧ P.eval x ≠ 0 := by
  classical
  by_contra hcon
  push Not at hcon
  haveI := h.finite
  have hℓ := h.prime.two_le
  have hf := h.one_le
  have hq2 : 2 ≤ ℓ ^ f := le_trans hℓ (Nat.le_self_pow (by omega) ℓ)
  have hq1 : 1 ≤ ℓ ^ f := by omega
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := Kˣ)
  have hcardK : Nat.card Kˣ = ℓ ^ f * ℓ ^ f - 1 := by
    rw [Nat.card_units, h.card, two_mul, pow_add]
  have hord : orderOf g = (ℓ ^ f - 1) * (ℓ ^ f + 1) := by
    rw [orderOf_eq_card_of_forall_mem_zpowers hg, hcardK, singerU_nat_sq_sub_one _ hq1]
  have hq1' : 0 < ℓ ^ f - 1 := by omega
  have hdvd : ℓ ^ f - 1 ∣ orderOf g := ⟨ℓ ^ f + 1, hord⟩
  have hou : orderOf (g ^ (ℓ ^ f - 1)) = ℓ ^ f + 1 := by
    rw [orderOf_pow_of_dvd (by omega) hdvd, hord, Nat.mul_div_cancel_left _ hq1']
  set u : Kˣ := g ^ (ℓ ^ f - 1) with hu
  have hu1 : u ^ (ℓ ^ f + 1) = 1 := by
    rw [← hou]
    exact pow_orderOf_eq_one u
  have hinj : Set.InjOn (fun k : ℕ => ((u ^ k : Kˣ) : K)) ↑(Finset.range (ℓ ^ f + 1)) := by
    intro i hi j hj hij
    rw [Finset.coe_range, Set.mem_Iio] at hi hj
    have hu_ij : u ^ i = u ^ j := Units.ext hij
    rw [← hou] at hi hj
    exact pow_injOn_Iio_orderOf hi hj hu_ij
  have hsub : (Finset.range (ℓ ^ f + 1)).image (fun k : ℕ => ((u ^ k : Kˣ) : K)) ⊆
      P.roots.toFinset := by
    intro t ht
    obtain ⟨k, -, rfl⟩ := Finset.mem_image.1 ht
    have hnorm : h.norm ((u ^ k : Kˣ) : K) = 1 := by
      rw [singerU_norm_eq_pow, ← Units.val_pow_eq_pow_val, ← pow_mul, mul_comm, pow_mul, hu1,
        one_pow, Units.val_one]
    rw [Multiset.mem_toFinset, Polynomial.mem_roots hP, Polynomial.IsRoot.def]
    exact hcon _ hnorm
  have hcard : ((Finset.range (ℓ ^ f + 1)).image
      (fun k : ℕ => ((u ^ k : Kˣ) : K))).card = ℓ ^ f + 1 := by
    rw [Finset.card_image_of_injOn hinj, Finset.card_range]
  have h1 := Finset.card_le_card hsub
  rw [hcard] at h1
  have h2 := Multiset.toFinset_card_le P.roots
  have h3 := Polynomial.card_roots' P
  omega

theorem singerU_exists_norm_eq_of_fixed (h : UnitaryFieldData ℓ f K) {n : K}
    (hn : h.bar n = n) (hn0 : n ≠ 0) : ∃ ε : K, ε ≠ 0 ∧ h.norm ε = n := by
  haveI := h.finite
  have hℓ := h.prime.two_le
  have hf := h.one_le
  have hq2 : 2 ≤ ℓ ^ f := le_trans hℓ (Nat.le_self_pow (by omega) ℓ)
  have hq1 : 1 ≤ ℓ ^ f := by omega
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := Kˣ)
  have hcardK : Nat.card Kˣ = ℓ ^ f * ℓ ^ f - 1 := by
    rw [Nat.card_units, h.card, two_mul, pow_add]
  have hord : orderOf g = (ℓ ^ f - 1) * (ℓ ^ f + 1) := by
    rw [orderOf_eq_card_of_forall_mem_zpowers hg, hcardK, singerU_nat_sq_sub_one _ hq1]
  have hnq : n ^ (ℓ ^ f) = n := singerU_pow_card_of_fixed h hn
  have hn1 : n ^ (ℓ ^ f - 1) = 1 := by
    have h1 : n * n ^ (ℓ ^ f - 1) = n * 1 := by
      rw [mul_one, ← pow_succ', Nat.sub_add_cancel hq1, hnq]
    exact mul_left_cancel₀ hn0 h1
  have hmem : Units.mk0 n hn0 ∈ Submonoid.powers g :=
    mem_powers_iff_mem_zpowers.2 (hg _)
  obtain ⟨m, hm⟩ := (Submonoid.mem_powers_iff _ _).1 hmem
  have hmpow : (g ^ m) ^ (ℓ ^ f - 1) = 1 := by
    apply Units.ext
    rw [Units.val_pow_eq_pow_val, hm, Units.val_mk0, Units.val_one]
    exact hn1
  have hdvd : orderOf g ∣ m * (ℓ ^ f - 1) :=
    orderOf_dvd_of_pow_eq_one (by rw [pow_mul]; exact hmpow)
  rw [hord, mul_comm m] at hdvd
  have hqm : ℓ ^ f + 1 ∣ m :=
    Nat.dvd_of_mul_dvd_mul_left (by omega : 0 < ℓ ^ f - 1) hdvd
  obtain ⟨k, hk⟩ := hqm
  refine ⟨((g ^ k : Kˣ) : K), Units.ne_zero _, ?_⟩
  rw [singerU_norm_eq_pow, ← Units.val_pow_eq_pow_val, ← pow_mul]
  have hkm : k * (ℓ ^ f + 1) = m := by rw [hk, mul_comm]
  rw [hkm, hm, Units.val_mk0]

theorem singerU_fixed_pow_eq_one (h : UnitaryFieldData ℓ f K) {p : ℕ} (hp : p.Prime)
    (hp5 : 5 ≤ p) (hpq : p ∣ ℓ ^ f + 1) {x : K} (hx : h.bar x = x) (hx0 : x ≠ 0)
    (hxp : x ^ p = 1) : x = 1 := by
  have hℓ := h.prime.two_le
  have hf := h.one_le
  have hq2 : 2 ≤ ℓ ^ f := le_trans hℓ (Nat.le_self_pow (by omega) ℓ)
  have hq1 : 1 ≤ ℓ ^ f := by omega
  have hxq : x ^ (ℓ ^ f - 1) = 1 := by
    have h1 : x * x ^ (ℓ ^ f - 1) = x * 1 := by
      rw [mul_one, ← pow_succ', Nat.sub_add_cancel hq1, singerU_pow_card_of_fixed h hx]
    exact mul_left_cancel₀ hx0 h1
  have hcop : Nat.Coprime p (ℓ ^ f - 1) := by
    rw [Nat.Prime.coprime_iff_not_dvd hp]
    intro hd
    have h2 : p ∣ 2 := by
      have h3 : p ∣ (ℓ ^ f - 1) + 2 := by
        rwa [show ℓ ^ f - 1 + 2 = ℓ ^ f + 1 by omega]
      exact (Nat.dvd_add_right hd).1 h3
    have := Nat.le_of_dvd (by norm_num) h2
    omega
  have h4 : x ^ (p.gcd (ℓ ^ f - 1)) = 1 := pow_gcd_eq_one.2 ⟨hxp, hxq⟩
  rw [Nat.Coprime.gcd_eq_one hcop, pow_one] at h4
  exact h4

theorem singerU_eq_neg_one_of_add_inv (h : UnitaryFieldData ℓ f K) {ξ : K}
    (hξ : h.norm ξ = 1) (hs : ξ + ξ⁻¹ = -2) : ξ = -1 := by
  have hξ0 : ξ ≠ 0 := by
    intro h0
    rw [h0, UnitaryFieldData.norm, zero_mul] at hξ
    exact zero_ne_one hξ
  have hinv : ξ * ξ⁻¹ = 1 := mul_inv_cancel₀ hξ0
  have hsq : (ξ + 1) ^ 2 = 0 := by linear_combination ξ * hs - hinv
  have h1 : ξ + 1 = 0 := (pow_eq_zero_iff two_ne_zero).1 hsq
  linear_combination h1

theorem singerU_exists_norm_one_good (h : UnitaryFieldData ℓ f K) (hq : 10 ≤ ℓ ^ f + 1) :
    ∃ ρ : K, h.norm ρ = 1 ∧ h.norm (1 + ρ) ≠ 0 ∧ h.norm (1 + ρ) ≠ 1 ∧ h.norm (1 + ρ) ≠ -1 := by
  have hPeval : ∀ x : K, ((Polynomial.X + 1) * (Polynomial.X ^ 2 + Polynomial.X + 1) *
      (Polynomial.X ^ 2 + 3 * Polynomial.X + 1) : Polynomial K).eval x =
      (x + 1) * (x ^ 2 + x + 1) * (x ^ 2 + 3 * x + 1) := by
    intro x
    simp only [Polynomial.eval_mul, Polynomial.eval_add, Polynomial.eval_pow,
      Polynomial.eval_X, Polynomial.eval_one, Polynomial.eval_ofNat]
  have hPne : ((Polynomial.X + 1) * (Polynomial.X ^ 2 + Polynomial.X + 1) *
      (Polynomial.X ^ 2 + 3 * Polynomial.X + 1) : Polynomial K) ≠ 0 := by
    intro h0
    have h1 := hPeval 0
    rw [h0, Polynomial.eval_zero] at h1
    norm_num at h1
  have hdeg : ((Polynomial.X + 1) * (Polynomial.X ^ 2 + Polynomial.X + 1) *
      (Polynomial.X ^ 2 + 3 * Polynomial.X + 1) : Polynomial K).natDegree < ℓ ^ f + 1 := by
    have : ((Polynomial.X + 1) * (Polynomial.X ^ 2 + Polynomial.X + 1) *
        (Polynomial.X ^ 2 + 3 * Polynomial.X + 1) : Polynomial K).natDegree ≤ 5 := by
      compute_degree
    omega
  obtain ⟨ρ, hρ, hPρ⟩ := singerU_exists_norm_one_eval_ne h hPne hdeg
  have hρ0 : ρ ≠ 0 := by
    intro h0
    rw [h0, UnitaryFieldData.norm, zero_mul] at hρ
    exact zero_ne_one hρ
  have hbar := singerU_bar_eq_inv_of_norm_one h hρ
  have hN : h.norm (1 + ρ) = (1 + ρ) * (1 + ρ⁻¹) := by
    rw [UnitaryFieldData.norm, map_add, map_one, hbar]
  have hinv : ρ * ρ⁻¹ = 1 := mul_inv_cancel₀ hρ0
  have key : ∀ c : K, h.norm (1 + ρ) = c → ρ ^ 2 + (2 - c) * ρ + 1 = 0 := by
    intro c hc
    rw [hN] at hc
    linear_combination ρ * hc - (1 + ρ) * hinv
  refine ⟨ρ, hρ, ?_, ?_, ?_⟩
  · intro hc
    have k := key 0 hc
    have h1 : ρ + 1 = 0 := by
      have : (ρ + 1) ^ 2 = 0 := by linear_combination k
      exact (pow_eq_zero_iff two_ne_zero).1 this
    apply hPρ
    rw [hPeval, h1]
    ring
  · intro hc
    have k := key 1 hc
    apply hPρ
    rw [hPeval]
    linear_combination (ρ + 1) * (ρ ^ 2 + 3 * ρ + 1) * k
  · intro hc
    have k := key (-1) hc
    apply hPρ
    rw [hPeval]
    linear_combination (ρ + 1) * (ρ ^ 2 + ρ + 1) * k

theorem singerU_exists_unique_inv_pow (h : UnitaryFieldData ℓ f K) {p : ℕ} (hp : p.Prime)
    (hp5 : 5 ≤ p) (hpq : p ∣ ℓ ^ f + 1) {M : K} (hM : h.bar M = M) (hM0 : M ≠ 0) :
    ∃! n : K, h.bar n = n ∧ n ≠ 0 ∧ n⁻¹ ^ p = M := by
  haveI := h.finite
  have hinj : Function.Injective (fun y : h.fixedField ˣ => y ^ p) := by
    intro y y' hyy
    simp only at hyy
    have hy : ((y : h.fixedField) : K) ^ p = ((y' : h.fixedField) : K) ^ p := by
      have := congrArg (fun z : h.fixedField ˣ => ((z : h.fixedField) : K)) hyy
      simpa using this
    have hyf : h.bar ((y : h.fixedField) : K) = ((y : h.fixedField) : K) :=
      (h.mem_fixedField).1 (y : h.fixedField).2
    have hyf' : h.bar ((y' : h.fixedField) : K) = ((y' : h.fixedField) : K) :=
      (h.mem_fixedField).1 (y' : h.fixedField).2
    have hb0 : ((y' : h.fixedField) : K) ≠ 0 := by
      intro h0
      exact y'.ne_zero (Subtype.ext h0)
    have hw : h.bar (((y : h.fixedField) : K) * ((y' : h.fixedField) : K)⁻¹) =
        ((y : h.fixedField) : K) * ((y' : h.fixedField) : K)⁻¹ := by
      rw [map_mul, map_inv₀, hyf, hyf']
    have hw0 : ((y : h.fixedField) : K) * ((y' : h.fixedField) : K)⁻¹ ≠ 0 := by
      refine mul_ne_zero ?_ (inv_ne_zero hb0)
      intro h0
      exact y.ne_zero (Subtype.ext h0)
    have hwp : (((y : h.fixedField) : K) * ((y' : h.fixedField) : K)⁻¹) ^ p = 1 := by
      rw [mul_pow, inv_pow, hy, mul_inv_cancel₀ (pow_ne_zero _ hb0)]
    have hw1 := singerU_fixed_pow_eq_one h hp hp5 hpq hw hw0 hwp
    have hab : ((y : h.fixedField) : K) = ((y' : h.fixedField) : K) :=
      (mul_inv_eq_one₀ hb0).1 hw1
    exact Units.ext (Subtype.ext hab)
  have hsurj : Function.Surjective (fun y : h.fixedField ˣ => y ^ p) :=
    Finite.surjective_of_injective hinj
  have hM' : h.bar M = M := hM
  have hMf : (⟨M, (h.mem_fixedField).2 hM'⟩ : h.fixedField) ≠ 0 := by
    intro h0
    apply hM0
    simpa using congrArg Subtype.val h0
  obtain ⟨y, hy⟩ := hsurj (Units.mk0 _ hMf)
  have hyM : ((y : h.fixedField) : K) ^ p = M := by
    have := congrArg (fun z : h.fixedField ˣ => ((z : h.fixedField) : K)) hy
    simpa using this
  have hyf : h.bar ((y : h.fixedField) : K) = ((y : h.fixedField) : K) :=
    (h.mem_fixedField).1 (y : h.fixedField).2
  have hy0 : ((y : h.fixedField) : K) ≠ 0 := by
    intro h0
    exact y.ne_zero (Subtype.ext h0)
  refine ⟨((y : h.fixedField) : K)⁻¹, ⟨?_, inv_ne_zero hy0, ?_⟩, ?_⟩
  · rw [map_inv₀, hyf]
  · rw [inv_inv, hyM]
  · rintro n' ⟨hn'f, hn'0, hn'p⟩
    have hmem : h.bar n'⁻¹ = n'⁻¹ := by rw [map_inv₀, hn'f]
    obtain ⟨y', hy'⟩ : ∃ y' : h.fixedField ˣ, ((y' : h.fixedField) : K) = n'⁻¹ :=
      ⟨Units.mk0 ⟨n'⁻¹, (h.mem_fixedField).2 hmem⟩
        (fun h0 => hn'0 (inv_eq_zero.1 (congrArg Subtype.val h0))), rfl⟩
    have hy'p : y' ^ p = Units.mk0 _ hMf := by
      apply Units.ext
      rw [Units.val_pow_eq_pow_val, Units.val_mk0]
      apply Subtype.ext
      show ((y' : h.fixedField) : K) ^ p = M
      rw [hy']
      exact hn'p
    have hyy' : y' = y := hinj (hy'p.trans hy.symm)
    have hval : n'⁻¹ = ((y : h.fixedField) : K) := by
      rw [← hy', hyy']
    rw [← inv_inv n', hval]

theorem singerU_ne_one_neg_one_of_inv_pow {p : ℕ} (hp : p.Prime)
    (hp5 : 5 ≤ p) {M : K} (hM1 : M ≠ 1) (hM2 : M ≠ -1) {n : K} (hnp : n⁻¹ ^ p = M) :
    n ≠ 1 ∧ n ≠ -1 := by
  have hodd : Odd p := hp.odd_of_ne_two (by omega)
  constructor
  · rintro rfl
    apply hM1
    rw [← hnp]
    simp
  · rintro rfl
    apply hM2
    rw [← hnp, inv_neg, inv_one, hodd.neg_one_pow]

theorem singerU_exists_norm_eq_good (h : UnitaryFieldData ℓ f K) {p : ℕ} (hp : p.Prime)
    (hlt : p < ℓ ^ f + 1) {c : K} (hc : h.norm c = 1) {n : K} (hn : h.bar n = n) (hn0 : n ≠ 0) :
    ∃ ε : K, h.norm ε = n ∧ h.bar ε ^ (p - 1) + c * ε ≠ 0 := by
  obtain ⟨ε₀, hε₀0, hε₀⟩ := singerU_exists_norm_eq_of_fixed h hn hn0
  have hbar0 : h.bar ε₀ ≠ 0 := (map_ne_zero h.bar).2 hε₀0
  have hQeval : ∀ x : K, ((Polynomial.C (c * ε₀) * Polynomial.X ^ p +
      Polynomial.C ((h.bar ε₀) ^ (p - 1)) : Polynomial K)).eval x =
      c * ε₀ * x ^ p + (h.bar ε₀) ^ (p - 1) := by
    intro x
    simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C,
      Polynomial.eval_pow, Polynomial.eval_X]
  have hQne : (Polynomial.C (c * ε₀) * Polynomial.X ^ p +
      Polynomial.C ((h.bar ε₀) ^ (p - 1)) : Polynomial K) ≠ 0 := by
    intro h0
    have h1 := hQeval 0
    rw [h0, Polynomial.eval_zero, zero_pow hp.ne_zero, mul_zero, zero_add] at h1
    exact pow_ne_zero _ hbar0 h1.symm
  have hdeg : (Polynomial.C (c * ε₀) * Polynomial.X ^ p +
      Polynomial.C ((h.bar ε₀) ^ (p - 1)) : Polynomial K).natDegree < ℓ ^ f + 1 := by
    have h1 : (Polynomial.C (c * ε₀) * Polynomial.X ^ p +
        Polynomial.C ((h.bar ε₀) ^ (p - 1)) : Polynomial K).natDegree ≤ p :=
      (Polynomial.natDegree_add_le _ _).trans
        (max_le (Polynomial.natDegree_C_mul_X_pow_le _ _) (by simp))
    omega
  obtain ⟨ζ, hζN, hζQ⟩ := singerU_exists_norm_one_eval_ne h hQne hdeg
  have hζ0 : ζ ≠ 0 := by
    intro h0
    rw [h0, UnitaryFieldData.norm, zero_mul] at hζN
    exact zero_ne_one hζN
  refine ⟨ε₀ * ζ, ?_, ?_⟩
  · rw [singerU_norm_mul, hε₀, hζN, mul_one]
  · intro H
    rw [map_mul, singerU_bar_eq_inv_of_norm_one h hζN] at H
    apply hζQ
    obtain ⟨k, hk⟩ : ∃ k, p - 1 = k := ⟨_, rfl⟩
    have hpk : k + 1 = p := by have := hp.pos; omega
    rw [hQeval, hk]
    rw [hk] at H
    rw [← hpk]
    have hk1 : ζ ^ k * ζ⁻¹ ^ k = 1 := by
      rw [← mul_pow, mul_inv_cancel₀ hζ0, one_pow]
    linear_combination ζ ^ k * H - (h.bar ε₀) ^ k * hk1

theorem singerU_exists_norm_one_pow_ne_one (h : UnitaryFieldData ℓ f K) {p : ℕ} (hp : p.Prime)
    (hpq : p ∣ ℓ ^ f + 1) (hne : ℓ ^ f + 1 ≠ p) :
    ∃ κ : K, h.norm κ = 1 ∧ κ ^ p ≠ 1 := by
  have hlt : p < ℓ ^ f + 1 :=
    lt_of_le_of_ne (Nat.le_of_dvd (by positivity) hpq) (Ne.symm hne)
  have hP : (Polynomial.X ^ p - Polynomial.C (1 : K)) ≠ 0 :=
    Polynomial.X_pow_sub_C_ne_zero hp.pos 1
  have hdeg : (Polynomial.X ^ p - Polynomial.C (1 : K)).natDegree < ℓ ^ f + 1 := by
    rw [Polynomial.natDegree_X_pow_sub_C]
    exact hlt
  obtain ⟨κ, hκ, hκp⟩ := singerU_exists_norm_one_eval_ne h hP hdeg
  refine ⟨κ, hκ, fun h1 => hκp ?_⟩
  simp [h1]

theorem singerU_not_pow_norm_one_iff (h : UnitaryFieldData ℓ f K) {p : ℕ} (hp : p.Prime)
    (hp5 : 5 ≤ p) (hpq : p ∣ ℓ ^ f + 1) {c : K} (hc : h.norm c = 1) :
    (¬ ∃ μ : K, h.norm μ = 1 ∧ μ ^ p = c) ↔ ¬ ∃ z : K, z ^ p = c := by
  constructor
  · rintro hno ⟨z, hz⟩
    apply hno
    refine ⟨z, ?_, hz⟩
    have hc0 : c ≠ 0 := by
      intro h0
      rw [h0, UnitaryFieldData.norm, zero_mul] at hc
      exact zero_ne_one hc
    have hz0 : z ≠ 0 := by
      intro h0
      apply hc0
      rw [← hz, h0, zero_pow hp.ne_zero]
    have hnp : h.norm z ^ p = 1 := by
      rw [← singerU_norm_pow, hz, hc]
    exact singerU_fixed_pow_eq_one h hp hp5 hpq (singerU_norm_fixed h z)
      (singerU_norm_ne_zero h hz0) hnp
  · rintro hno ⟨μ, -, hμ⟩
    exact hno ⟨μ, hμ⟩

theorem singerU_ne_one_neg_one_of_not_pow (h : UnitaryFieldData ℓ f K) {p : ℕ} (hp : p.Prime)
    (hp5 : 5 ≤ p) {c : K} (hnp : ¬ ∃ μ : K, h.norm μ = 1 ∧ μ ^ p = c) : c ≠ 1 ∧ c ≠ -1 := by
  have hodd : Odd p := hp.odd_of_ne_two (by omega)
  constructor
  · rintro rfl
    exact hnp ⟨1, by simp [UnitaryFieldData.norm], by simp⟩
  · rintro rfl
    refine hnp ⟨-1, ?_, ?_⟩
    · simp [UnitaryFieldData.norm]
    · exact hodd.neg_one_pow

theorem singerU_mulVec_single_apply {m : ℕ} (M : Matrix (Fin m) (Fin m) K) (k i : Fin m) :
    (M *ᵥ Pi.single k 1) i = M i k := by
  simp [Matrix.mulVec, dotProduct, Pi.single_apply]

theorem singerU_diagonal_mulVec_single {m : ℕ} (c : Fin m → K) (i : Fin m) :
    Matrix.diagonal c *ᵥ Pi.single i 1 = c i • Pi.single i 1 := by
  funext k
  rw [Matrix.mulVec_diagonal, Pi.smul_apply, smul_eq_mul]
  by_cases hk : k = i
  · subst hk
    simp
  · simp [Pi.single_apply, hk]

theorem singerU_monomial_diag_of_cubic {n : ℕ} {a b : K} (hab : a * b = 1)
    (h0 : a + b ≠ 0) (h1 : a + b + 1 ≠ 0) (h2 : a + b + 2 ≠ 0)
    {g : Matrix (Fin n) (Fin n) K} (hg : IsMonomialMat g)
    (hinj : ∀ v : Fin n → K, g *ᵥ v = 0 → v = 0)
    (hcub : (g - a • (1 : Matrix (Fin n) (Fin n) K)) * (g - b • 1) * (g - 1) = 0) :
    ∃ d : Fin n → K, g = Matrix.diagonal d := by
  classical
  have hcol : ∀ k : Fin n, ∃ i, g i k ≠ 0 := by
    intro k
    by_contra hk
    push Not at hk
    have hv : g *ᵥ Pi.single k 1 = 0 := by
      funext i
      rw [singerU_mulVec_single_apply, hk i, Pi.zero_apply]
    have := congrFun (hinj _ hv) k
    simp at this
  choose σ hσ using hcol
  have hu : ∀ k i, g i k ≠ 0 → i = σ k := fun k i hi => hg k i (σ k) hi (hσ k)
  have hz : ∀ k i, i ≠ σ k → g i k = 0 := by
    intro k i hi
    by_contra hne
    exact hi (hu k i hne)
  have hgE : ∀ k, g *ᵥ Pi.single k 1 = g (σ k) k • Pi.single (σ k) 1 := by
    intro k
    funext i
    rw [singerU_mulVec_single_apply, Pi.smul_apply, smul_eq_mul]
    by_cases hi : i = σ k
    · subst hi
      simp
    · rw [hz k i hi, Pi.single_apply, if_neg hi, mul_zero]
  have hσinj : Function.Injective σ := by
    intro k k' hkk
    by_contra hne
    have hv : g *ᵥ (g (σ k') k' • Pi.single k 1 - g (σ k) k • Pi.single k' 1) = 0 := by
      rw [Matrix.mulVec_sub, Matrix.mulVec_smul, Matrix.mulVec_smul, hgE k, hgE k', hkk,
        smul_smul, smul_smul, mul_comm, sub_self]
    have hc := congrFun (hinj _ hv) k'
    rw [Pi.sub_apply, Pi.smul_apply, Pi.smul_apply, Pi.single_apply, Pi.single_apply,
      if_neg (Ne.symm hne), if_pos rfl, smul_eq_mul, smul_eq_mul] at hc
    exact hσ k (by simpa using hc)
  have hvec : ∀ x : Fin n, (g - a • (1 : Matrix (Fin n) (Fin n) K)) *ᵥ
      ((g - b • 1) *ᵥ ((g - 1) *ᵥ Pi.single x 1)) = 0 := by
    intro x
    have h' := congrArg (fun M : Matrix (Fin n) (Fin n) K => M *ᵥ Pi.single x 1) hcub
    simpa only [Matrix.zero_mulVec, ← Matrix.mulVec_mulVec] using h'
  have hexp : ∀ x : Fin n, (g - a • (1 : Matrix (Fin n) (Fin n) K)) *ᵥ
      ((g - b • 1) *ᵥ ((g - 1) *ᵥ Pi.single x 1)) =
      (g (σ (σ (σ x))) (σ (σ x)) * (g (σ (σ x)) (σ x) * g (σ x) x)) • Pi.single (σ (σ (σ x))) 1
      - ((a + b + 1) * (g (σ (σ x)) (σ x) * g (σ x) x)) • Pi.single (σ (σ x)) 1
      + ((a + b + a * b) * g (σ x) x) • Pi.single (σ x) 1
      - (a * b) • Pi.single x 1 := by
    intro x
    simp only [Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec, Matrix.mulVec_sub,
      Matrix.mulVec_smul, hgE]
    module
  have hcoord : ∀ x z : Fin n,
      g (σ (σ (σ x))) (σ (σ x)) * (g (σ (σ x)) (σ x) * g (σ x) x) *
          (if z = σ (σ (σ x)) then 1 else 0)
      - (a + b + 1) * (g (σ (σ x)) (σ x) * g (σ x) x) * (if z = σ (σ x) then 1 else 0)
      + (a + b + a * b) * g (σ x) x * (if z = σ x then 1 else 0)
      - a * b * (if z = x then 1 else 0) = 0 := by
    intro x z
    have h' := congrFun (hvec x) z
    rw [hexp x] at h'
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, Pi.single_apply, smul_eq_mul,
      Pi.zero_apply] at h'
    linear_combination h'
  have hfix : ∀ x, σ x = x := by
    intro x
    by_contra hx
    have hx' : x ≠ σ x := fun h => hx h.symm
    rcases eq_or_ne (σ (σ x)) x with h2x | h2x
    ·
      have eX := hcoord x x
      have eS := hcoord x (σ x)
      simp only [h2x, hx, hx', ↓reduceIte, eq_self_iff_true, mul_one, mul_zero, zero_mul,
        add_zero, zero_add, sub_zero, zero_sub] at eX eS
      have hD : g (σ x) x * (g x (σ x) * g (σ x) x + (a + b + a * b)) = 0 := by
        linear_combination eS
      have hD' := (mul_eq_zero.1 hD).resolve_left (hσ x)
      have e1 : (a + b + 1) * (g x (σ x) * g (σ x) x) + a * b = 0 := by
        linear_combination -eX
      have hs : (a + b) * (a + b + 2) = 0 := by
        linear_combination (a + b + 1) * hD' - e1 - (a + b) * hab
      rcases mul_eq_zero.1 hs with hs | hs
      · exact h0 hs
      · exact h2 hs
    · rcases eq_or_ne (σ (σ (σ x))) x with h3x | h3x
      ·
        have hne12 : σ (σ x) ≠ σ x := fun h => hx' (hσinj h.symm)
        have eS := hcoord x (σ x)
        simp only [h3x, hne12, Ne.symm hne12, hx, ↓reduceIte, eq_self_iff_true, mul_one,
          mul_zero, zero_mul, add_zero, zero_add, sub_zero, zero_sub] at eS
        have hc : (a + b + a * b) * g (σ x) x = 0 := by
          linear_combination eS
        have hc' := (mul_eq_zero.1 hc).resolve_right (hσ x)
        exact h1 (by linear_combination hc' - hab)
      ·
        have eX := hcoord x x
        have h2x' : x ≠ σ (σ x) := Ne.symm h2x
        have h3x' : x ≠ σ (σ (σ x)) := Ne.symm h3x
        simp only [h2x', h3x', hx', hx, ↓reduceIte, eq_self_iff_true, mul_one, mul_zero,
          zero_mul, add_zero, zero_add, sub_zero, zero_sub] at eX
        exact one_ne_zero (by linear_combination -hab - eX)
  refine ⟨fun k => g k k, ?_⟩
  ext i k
  rw [Matrix.diagonal_apply]
  split_ifs with hik
  · subst hik
    rfl
  · exact hz k i (by rw [hfix k]; exact hik)

theorem singerU_zeta_facts {ζ : K} (hodd : Odd (orderOf ζ)) (hgt : 3 < orderOf ζ) :
    ζ ≠ 0 ∧ ζ * ζ⁻¹ = 1 ∧ ζ + ζ⁻¹ ≠ 0 ∧ ζ + ζ⁻¹ + 1 ≠ 0 ∧ ζ + ζ⁻¹ + 2 ≠ 0 ∧ ζ ≠ 1 ∧
      ζ⁻¹ ≠ ζ := by
  have hζ0 : ζ ≠ 0 := by
    intro h0
    subst h0
    have := pow_orderOf_eq_one (0 : K)
    rw [zero_pow (by omega)] at this
    exact zero_ne_one this
  have hinv : ζ * ζ⁻¹ = 1 := mul_inv_cancel₀ hζ0
  have hodd' := Nat.odd_iff.mp hodd
  refine ⟨hζ0, hinv, ?_, ?_, ?_, ?_, ?_⟩
  · intro hs
    have e : ζ ^ 2 + 1 = 0 := by linear_combination ζ * hs - hinv
    have e4 : ζ ^ 4 = 1 := by linear_combination (ζ ^ 2 - 1) * e
    have hle := Nat.le_of_dvd (by norm_num) (orderOf_dvd_of_pow_eq_one e4)
    omega
  · intro hs
    have e : ζ ^ 2 + ζ + 1 = 0 := by linear_combination ζ * hs - hinv
    have e3 : ζ ^ 3 = 1 := by linear_combination (ζ - 1) * e
    have hle := Nat.le_of_dvd (by norm_num) (orderOf_dvd_of_pow_eq_one e3)
    omega
  · intro hs
    have e : (ζ + 1) ^ 2 = 0 := by linear_combination ζ * hs - hinv
    have h1 : ζ + 1 = 0 := (pow_eq_zero_iff two_ne_zero).1 e
    have e2 : ζ ^ 2 = 1 := by
      have hζ : ζ = -1 := by linear_combination h1
      rw [hζ]
      norm_num
    have hle := Nat.le_of_dvd (by norm_num) (orderOf_dvd_of_pow_eq_one e2)
    omega
  · intro hs
    rw [hs, orderOf_one] at hgt
    omega
  · intro hs
    have e : ζ ^ 2 = 1 := by linear_combination (-ζ) * hs + hinv
    have hle := Nat.le_of_dvd (by norm_num) (orderOf_dvd_of_pow_eq_one e)
    omega

theorem singerU_monomial_conj_diag {n : ℕ} {ζ : K} (hodd : Odd (orderOf ζ))
    (hgt : 3 < orderOf ζ) (y yi : Matrix (Fin n) (Fin n) K) (hyi : yi * y = 1)
    (hy : y * yi = 1) (t : Fin n → K) (htc : ∀ i, (t i - ζ) * (t i - ζ⁻¹) * (t i - 1) = 0)
    (hmono : IsMonomialMat (yi * Matrix.diagonal t * y)) :
    ∃ d : Fin n → K, yi * Matrix.diagonal t * y = Matrix.diagonal d := by
  classical
  obtain ⟨-, hinv, h0, h1, h2, -, -⟩ := singerU_zeta_facts hodd hgt
  have hmv : ∀ (M N : Matrix (Fin n) (Fin n) K) (w : Fin n → K),
      (M * N) *ᵥ w = M *ᵥ (N *ᵥ w) := fun M N w => (Matrix.mulVec_mulVec w M N).symm
  have hyyi : ∀ w : Fin n → K, y *ᵥ (yi *ᵥ w) = w := fun w => by
    rw [Matrix.mulVec_mulVec, hy, Matrix.one_mulVec]
  have hyiy : ∀ w : Fin n → K, yi *ᵥ (y *ᵥ w) = w := fun w => by
    rw [Matrix.mulVec_mulVec, hyi, Matrix.one_mulVec]
  have hyy : ∀ A B : Matrix (Fin n) (Fin n) K, (yi * A * y) * (yi * B * y) = yi * (A * B) * y := by
    intro A B
    have e : (yi * A * y) * (yi * B * y) = yi * A * (y * yi) * B * y := by
      simp only [Matrix.mul_assoc]
    rw [e, hy, Matrix.mul_one]
    simp only [Matrix.mul_assoc]
  have hfac : ∀ c : K, yi * Matrix.diagonal t * y - c • (1 : Matrix (Fin n) (Fin n) K) =
      yi * (Matrix.diagonal t - c • 1) * y := by
    intro c
    simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one,
      hyi]
  have hg1 : yi * Matrix.diagonal t * y - (1 : Matrix (Fin n) (Fin n) K) =
      yi * (Matrix.diagonal t - 1) * y := by
    simpa only [one_smul] using hfac 1
  have hdiagprod : (Matrix.diagonal t - ζ • 1) * (Matrix.diagonal t - ζ⁻¹ • 1) *
      (Matrix.diagonal t - 1) = 0 := by
    have e : (Matrix.diagonal t - ζ • 1) * (Matrix.diagonal t - ζ⁻¹ • 1) *
        (Matrix.diagonal t - 1) =
          Matrix.diagonal (fun i => (t i - ζ) * (t i - ζ⁻¹) * (t i - 1)) := by
      rw [Matrix.smul_one_eq_diagonal, Matrix.smul_one_eq_diagonal, ← Matrix.diagonal_one,
        Matrix.diagonal_sub, Matrix.diagonal_sub, Matrix.diagonal_sub,
        Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]
    rw [e]
    have hfun : (fun i => (t i - ζ) * (t i - ζ⁻¹) * (t i - 1)) = 0 := funext htc
    rw [hfun]
    exact Matrix.diagonal_zero
  have hcub : (yi * Matrix.diagonal t * y - ζ • (1 : Matrix (Fin n) (Fin n) K)) *
      (yi * Matrix.diagonal t * y - ζ⁻¹ • 1) * (yi * Matrix.diagonal t * y - 1) = 0 := by
    rw [hfac ζ, hfac ζ⁻¹, hg1, hyy, hyy, hdiagprod, Matrix.mul_zero, Matrix.zero_mul]
  have ht0 : ∀ i, t i ≠ 0 := by
    intro i h0'
    have h' := htc i
    rw [h0'] at h'
    have e : (0 - ζ) * (0 - ζ⁻¹) * (0 - 1) = -1 := by linear_combination -hinv
    rw [e] at h'
    norm_num at h'
  have hinj : ∀ v : Fin n → K, (yi * Matrix.diagonal t * y) *ᵥ v = 0 → v = 0 := by
    intro v hv
    rw [hmv, hmv] at hv
    have h2' : Matrix.diagonal t *ᵥ (y *ᵥ v) = 0 := by
      have := congrArg (fun w => y *ᵥ w) hv
      simpa only [hyyi, Matrix.mulVec_zero] using this
    have h3 : y *ᵥ v = 0 := by
      funext i
      have := congrFun h2' i
      rw [Matrix.mulVec_diagonal] at this
      rcases mul_eq_zero.1 this with h4 | h4
      · exact absurd h4 (ht0 i)
      · exact h4
    rw [← hyiy v, h3, Matrix.mulVec_zero]
  exact singerU_monomial_diag_of_cubic hinv h0 h1 h2 hmono hinj hcub

theorem singerU_monomial_conj_column {n : ℕ} {ζ : K} (hodd : Odd (orderOf ζ))
    (hgt : 3 < orderOf ζ) (y yi : Matrix (Fin n) (Fin n) K) (hyi : yi * y = 1)
    (hy : y * yi = 1) (t : Fin n → K) (a0 : Fin n) (hta : t a0 = ζ)
    (htne : ∀ i, i ≠ a0 → t i ≠ ζ) (htc : ∀ i, (t i - ζ) * (t i - ζ⁻¹) * (t i - 1) = 0)
    (hmono : IsMonomialMat (yi * Matrix.diagonal t * y)) :
    ∃ a : Fin n, ∀ i, i ≠ a → yi i a0 = 0 := by
  classical
  obtain ⟨d, hd⟩ := singerU_monomial_conj_diag hodd hgt y yi hyi hy t htc hmono
  have hmv : ∀ (M N : Matrix (Fin n) (Fin n) K) (w : Fin n → K),
      (M * N) *ᵥ w = M *ᵥ (N *ᵥ w) := fun M N w => (Matrix.mulVec_mulVec w M N).symm
  have hyyi : ∀ w : Fin n → K, y *ᵥ (yi *ᵥ w) = w := fun w => by
    rw [Matrix.mulVec_mulVec, hy, Matrix.one_mulVec]
  have hyiy : ∀ w : Fin n → K, yi *ᵥ (y *ᵥ w) = w := fun w => by
    rw [Matrix.mulVec_mulVec, hyi, Matrix.one_mulVec]
  obtain ⟨v, hv⟩ : ∃ v : Fin n → K, v = yi *ᵥ Pi.single a0 1 := ⟨_, rfl⟩
  have hvne : v ≠ 0 := by
    intro h0v
    have : Pi.single a0 1 = (0 : Fin n → K) := by
      rw [← hyyi (Pi.single a0 1), ← hv, h0v, Matrix.mulVec_zero]
    have := congrFun this a0
    simp at this
  have hgv : Matrix.diagonal d *ᵥ v = ζ • v := by
    rw [← hd, hv, hmv, hmv, hyyi, singerU_diagonal_mulVec_single, hta, Matrix.mulVec_smul]
  have hcomp : ∀ i, d i * v i = ζ * v i := fun i => by
    have := congrFun hgv i
    rw [Matrix.mulVec_diagonal, Pi.smul_apply, smul_eq_mul] at this
    exact this
  have hsupp : ∀ i, v i ≠ 0 → d i = ζ := fun i hi => mul_right_cancel₀ hi (hcomp i)
  have hDy : ∀ i, d i = ζ →
      Matrix.diagonal t *ᵥ (y *ᵥ Pi.single i 1) = ζ • (y *ᵥ Pi.single i 1) := by
    intro i hi
    have hX : Matrix.diagonal t *ᵥ (y *ᵥ Pi.single i 1) =
        y *ᵥ ((yi * Matrix.diagonal t * y) *ᵥ Pi.single i 1) := by
      rw [hmv, hmv, hyyi]
    rw [hX, hd, singerU_diagonal_mulVec_single, hi, Matrix.mulVec_smul]
  have hcol_i : ∀ i, d i = ζ → ∀ k, k ≠ a0 → (y *ᵥ Pi.single i 1) k = 0 := by
    intro i hi k hk
    have hk' := congrFun (hDy i hi) k
    rw [Matrix.mulVec_diagonal, Pi.smul_apply, smul_eq_mul] at hk'
    have h' : (t k - ζ) * (y *ᵥ Pi.single i 1) k = 0 := by linear_combination hk'
    rcases mul_eq_zero.1 h' with h'' | h''
    · exact absurd (sub_eq_zero.1 h'') (htne k hk)
    · exact h''
  have hei : ∀ i, d i = ζ → Pi.single i 1 = (y *ᵥ Pi.single i 1) a0 • v := by
    intro i hi
    have hu : y *ᵥ Pi.single i 1 = (y *ᵥ Pi.single i 1) a0 • Pi.single a0 1 := by
      funext k
      by_cases hk : k = a0
      · subst hk
        simp
      · rw [Pi.smul_apply, smul_eq_mul, Pi.single_apply, if_neg hk, mul_zero]
        exact hcol_i i hi k hk
    calc Pi.single i 1 = yi *ᵥ (y *ᵥ Pi.single i 1) := (hyiy _).symm
      _ = yi *ᵥ ((y *ᵥ Pi.single i 1) a0 • Pi.single a0 1) := by rw [← hu]
      _ = (y *ᵥ Pi.single i 1) a0 • v := by rw [Matrix.mulVec_smul, hv]
  have hi_eq : ∀ i j, d i = ζ → d j = ζ → i = j := by
    intro i j hi hj
    by_contra hij
    have e1 := hei i hi
    have e2 := hei j hj
    have c1 := congrFun e1 i
    have c2 := congrFun e1 j
    have c3 := congrFun e2 j
    rw [Pi.single_apply, if_pos rfl, Pi.smul_apply, smul_eq_mul] at c1
    rw [Pi.single_apply, if_neg (Ne.symm hij), Pi.smul_apply, smul_eq_mul] at c2
    rw [Pi.single_apply, if_pos rfl, Pi.smul_apply, smul_eq_mul] at c3
    have hvj : v j ≠ 0 := by
      intro h0j
      rw [h0j, mul_zero] at c3
      exact one_ne_zero c3
    have hα : (y *ᵥ Pi.single i 1) a0 = 0 := (mul_eq_zero.1 c2.symm).resolve_right hvj
    rw [hα, zero_mul] at c1
    exact one_ne_zero c1
  obtain ⟨a, ha⟩ : ∃ a, v a ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact hvne (funext hcon)
  refine ⟨a, fun i hi => ?_⟩
  have hvi : yi i a0 = v i := by
    rw [hv, singerU_mulVec_single_apply]
  rw [hvi]
  by_contra hvi0
  exact hi (hi_eq i a (hsupp i hvi0) (hsupp a ha))

end CFSG.LieType.SeitzGeneration

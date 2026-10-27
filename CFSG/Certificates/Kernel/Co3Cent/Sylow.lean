module

public import CFSG.Certificates.Kernel.OrbRow.CentGrp

public section

namespace CFSG.KC.Co3Cent

open Subgroup

variable {H : Type*} [Group H] [Finite H]

theorem card_dvd_of_two_five (N : Subgroup H) [N.Normal] {a b : ℕ}
    (hH : Nat.card H = 2 ^ a * 3 ^ b * 5) (T : Subgroup H) (hT : Nat.card T = 2 ^ a)
    (hTN : ∀ t ∈ T, t ∈ N → t = 1) {c : H} (hc : orderOf c = 5) (hcN : c ∉ N) :
    Nat.card N ∣ 3 ^ b := by
  set f : T →* H ⧸ N := (QuotientGroup.mk' N).comp T.subtype
  have hinj : Function.Injective f := by
    rw [injective_iff_map_eq_one]
    intro t ht
    exact Subtype.ext (hTN _ t.2 ((QuotientGroup.eq_one_iff _).1 ht))
  have hdvd : Nat.card T ∣ Nat.card (H ⧸ N) := Subgroup.card_dvd_of_injective f hinj
  rw [hT] at hdvd
  obtain ⟨q, hq⟩ := hdvd
  have hHN := Subgroup.card_eq_card_quotient_mul_card_subgroup N
  rw [hH, hq] at hHN
  have h1 : q * Nat.card N = 3 ^ b * 5 := by
    have : 2 ^ a * (q * Nat.card N) = 2 ^ a * (3 ^ b * 5) := by rw [← mul_assoc, ← hHN]; ring
    exact Nat.eq_of_mul_eq_mul_left (by positivity) this
  have h5 : ¬ 5 ∣ Nat.card N := by
    intro h5
    have hcop : Nat.Coprime 5 (Nat.card (H ⧸ N)) := by
      rw [Nat.Prime.coprime_iff_not_dvd Nat.prime_five, hq]
      intro hd
      have hq5 : 5 ∣ q :=
        Nat.Coprime.dvd_of_dvd_mul_left (Nat.Coprime.pow_right a (by norm_num)) hd
      have h25 : 5 * 5 ∣ 3 ^ b * 5 := h1 ▸ Nat.mul_dvd_mul hq5 h5
      have h53 : 5 ∣ 3 ^ b := Nat.dvd_of_mul_dvd_mul_right (by norm_num) h25
      have := Nat.le_of_dvd (by norm_num) (Nat.Prime.dvd_of_dvd_pow Nat.prime_five h53)
      omega
    exact hcN (CFSG.KC.OrbRow.CentGrp.mem_of_orderOf_coprime N (by rw [hc]) hcop)
  have hN : Nat.card N ∣ 3 ^ b * 5 := Dvd.intro_left q h1
  exact (Nat.Coprime.dvd_mul_right ((Nat.Prime.coprime_iff_not_dvd Nat.prime_five).2 h5).symm).1 hN

theorem le_of_normal_of_card {p : ℕ} [hp : Fact p.Prime] (N T : Subgroup H) [N.Normal] {k b m : ℕ}
    (hN : Nat.card N = p ^ k) (hT : Nat.card T = p ^ b) (hH : Nat.card H = p ^ b * m)
    (hm : ¬ p ∣ m) : N ≤ T := by
  have hm0 : m ≠ 0 := by
    rintro rfl
    exact hm (dvd_zero p)
  have hf : (Nat.card H).factorization p = b := by
    rw [hH, Nat.factorization_mul (pow_ne_zero _ hp.out.ne_zero) hm0, Finsupp.add_apply,
      Nat.Prime.factorization_pow hp.out, Finsupp.single_eq_same,
      Nat.factorization_eq_zero_of_not_dvd hm, add_zero]
  obtain ⟨Q, hQ⟩ := (IsPGroup.of_card hN).exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq H Q (Sylow.ofCard T (by rw [hT, hf]))
  intro n hn
  have hmem : n ∈ ((g • Q : Sylow p H) : Subgroup H) := by
    rw [Sylow.coe_subgroup_smul, Subgroup.mem_smul_pointwise_iff_exists]
    refine ⟨g⁻¹ * n * g, hQ ?_, ?_⟩
    · have := ‹N.Normal›.conj_mem n hn g⁻¹
      simpa using this
    · simp [MulAut.smul_def, MulAut.conj_apply, mul_assoc]
  rw [hg] at hmem
  exact hmem

theorem cent_le_of_index3 (D N : Subgroup H) [D.Normal] [N.Normal] {b m : ℕ}
    (hH : Nat.card H = 3 ^ (b + 1) * m) (hm : ¬ 3 ∣ m) (hD : Nat.card D = 3 ^ b)
    (hDab : ∀ a ∈ D, ∀ d ∈ D, a * d = d * a) {c : H} (hc3 : c ^ 3 = 1)
    (hcD : ∃ d ∈ D, c * d ≠ d * c) (hN : Nat.card N ∣ 3 ^ (b + 1))
    (hNc : ∀ n ∈ N, ∀ d ∈ D, n * d = d * n) : N ≤ D := by
  have h3 : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hm0 : m ≠ 0 := by
    rintro rfl
    exact hm (dvd_zero 3)
  have hf : (Nat.card H).factorization 3 = b + 1 := by
    rw [hH, Nat.factorization_mul (pow_ne_zero _ (by norm_num)) hm0, Finsupp.add_apply,
      Nat.Prime.factorization_pow Nat.prime_three, Finsupp.single_eq_same,
      Nat.factorization_eq_zero_of_not_dvd hm, add_zero]
  have hc1 : c ≠ 1 := by
    rintro rfl
    obtain ⟨d, -, hd⟩ := hcD
    exact hd (by simp)
  have hco : orderOf c = 3 := orderOf_eq_prime hc3 hc1
  obtain ⟨Q, hQ⟩ := (IsPGroup.of_card (p := 3) (n := 1)
    (by rw [Nat.card_zpowers, hco, pow_one] : Nat.card (zpowers c) = 3 ^ 1)).exists_le_sylow
  have hQc : Nat.card (Q : Subgroup H) = 3 ^ (b + 1) := by rw [Sylow.card_eq_multiplicity, hf]
  obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow Nat.prime_three).1 hN
  have hNQ : N ≤ Q := le_of_normal_of_card N Q hk hQc hH hm
  have hDQ : D ≤ Q := le_of_normal_of_card D Q hD hQc hH hm
  set Z := (Q : Subgroup H) ⊓ centralizer (D : Set H)
  have hDZ : D ≤ Z := fun a ha => ⟨hDQ ha, mem_centralizer_iff.2 fun d hd => (hDab a ha d hd).symm⟩
  have hcZ : c ∉ Z := by
    rintro ⟨-, hz⟩
    obtain ⟨d, hd, hne⟩ := hcD
    exact hne ((mem_centralizer_iff.1 hz d hd).symm)
  have hZ : Nat.card Z ∣ 3 ^ (b + 1) := hQc ▸ Subgroup.card_dvd_of_le inf_le_left
  obtain ⟨j, hj, hjZ⟩ := (Nat.dvd_prime_pow Nat.prime_three).1 hZ
  have hjb : b ≤ j := by
    have := Subgroup.card_le_of_le hDZ
    rw [hD, hjZ] at this
    exact (Nat.pow_le_pow_iff_right (by norm_num)).1 this
  have hjne : j ≠ b + 1 := by
    rintro rfl
    have hZQ : Z = Q := Subgroup.eq_of_le_of_card_ge inf_le_left (by rw [hQc, hjZ])
    exact hcZ (hZQ ▸ hQ (mem_zpowers c))
  have hDZe : D = Z := Subgroup.eq_of_le_of_card_ge hDZ (by
    rw [hD, hjZ]
    exact Nat.pow_le_pow_right (by norm_num) (by omega))
  intro n hn
  rw [hDZe]
  exact ⟨hNQ hn, mem_centralizer_iff.2 fun d hd => (hNc n hn d hd).symm⟩

theorem comm_mem_of_gens {Z : Subgroup H} {Y : Set H}
    (hZ : ∀ z ∈ Z, ∀ g ∈ closure Y, z * g = g * z)
    (hY : ∀ a ∈ Y, ∀ b ∈ Y, a * b * a⁻¹ * b⁻¹ ∈ Z) :
    ∀ a ∈ closure Y, ∀ b ∈ closure Y, a * b * a⁻¹ * b⁻¹ ∈ Z := by
  have key : ∀ b : H, (∀ a ∈ Y, a * b * a⁻¹ * b⁻¹ ∈ Z) →
      ∀ a ∈ closure Y, a * b * a⁻¹ * b⁻¹ ∈ Z := by
    intro b hX a ha
    induction ha using Subgroup.closure_induction with
    | mem a ha => exact hX a ha
    | one => simp
    | mul a c ha' _ ha hc =>
      have e : a * c * b * (a * c)⁻¹ * b⁻¹ =
          a * (c * b * c⁻¹ * b⁻¹) * a⁻¹ * (a * b * a⁻¹ * b⁻¹) := by group
      have hc' : a * (c * b * c⁻¹ * b⁻¹) * a⁻¹ = c * b * c⁻¹ * b⁻¹ := by
        rw [← hZ _ hc a ha', mul_inv_cancel_right]
      rw [e, hc']
      exact Z.mul_mem hc ha
    | inv a ha' ha =>
      have e : a⁻¹ * b * a⁻¹⁻¹ * b⁻¹ = a⁻¹ * (a * b * a⁻¹ * b⁻¹)⁻¹ * a := by group
      rw [e, ← hZ _ (Z.inv_mem ha) a⁻¹ (inv_mem ha'), inv_mul_cancel_right]
      exact Z.inv_mem ha
  intro a ha b hb
  have hYb : ∀ y ∈ Y, y * b * y⁻¹ * b⁻¹ ∈ Z := by
    intro y hy
    have h2 : ∀ c ∈ closure Y, c * y * c⁻¹ * y⁻¹ ∈ Z := key y fun c hc => hY c hc y hy
    have h3 := Z.inv_mem (h2 b hb)
    have e : y * b * y⁻¹ * b⁻¹ = (b * y * b⁻¹ * y⁻¹)⁻¹ := by group
    rw [e]
    exact h3
  exact key b hYb a ha

theorem pow_mod3 {x : H} (h : x ^ 3 = 1) (n : ℕ) : x ^ n = x ^ (n % 3) := by
  conv_lhs => rw [← Nat.div_add_mod n 3, pow_add, pow_mul, h, one_pow, one_mul]

theorem card_two_gen (R : Subgroup H) [R.Normal] {u v : H} (huv : u * v * u⁻¹ * v⁻¹ ∈ R)
    (hu : u ^ 3 ∈ R) (hv : v ^ 3 ∈ R)
    (hS : ∀ a < 3, ∀ b < 3, u ^ a * v ^ b ∈ R → a = 0 ∧ b = 0) :
    ∃ M : Subgroup H, R ≤ M ∧ Nat.card M = 9 * Nat.card R ∧
      ∀ t ∈ M, ∃ r ∈ R, ∃ a < 3, ∃ b < 3, t = r * (u ^ a * v ^ b) := by
  set f := QuotientGroup.mk' R
  set q := f u
  set p := f v
  have hq3 : q ^ 3 = 1 := by
    rw [← map_pow]
    exact (QuotientGroup.eq_one_iff _).2 hu
  have hp3 : p ^ 3 = 1 := by
    rw [← map_pow]
    exact (QuotientGroup.eq_one_iff _).2 hv
  have hqp : Commute q p := by
    have h1 : f (u * v * u⁻¹ * v⁻¹) = 1 := (QuotientGroup.eq_one_iff _).2 huv
    simp only [map_mul, map_inv] at h1
    have : q * p = p * q := by
      calc q * p = q * p * q⁻¹ * p⁻¹ * (p * q) := by group
        _ = p * q := by rw [h1, one_mul]
    exact this
  have hpow : ∀ a b c d : ℕ, q ^ a * p ^ b * (q ^ c * p ^ d) = q ^ ((a + c) % 3) * p ^ ((b + d) % 3) := by
    intro a b c d
    rw [← pow_mod3 hq3, ← pow_mod3 hp3, pow_add, pow_add]
    have := (hqp.symm.pow_pow b c).eq
    calc q ^ a * p ^ b * (q ^ c * p ^ d) = q ^ a * (p ^ b * q ^ c) * p ^ d := by group
      _ = q ^ a * (q ^ c * p ^ b) * p ^ d := by rw [this]
      _ = q ^ a * q ^ c * (p ^ b * p ^ d) := by group
  set A : Subgroup (H ⧸ R) :=
    { carrier := {x | ∃ a < 3, ∃ b < 3, x = q ^ a * p ^ b}
      one_mem' := ⟨0, by norm_num, 0, by norm_num, by simp⟩
      mul_mem' := by
        rintro _ _ ⟨a, -, b, -, rfl⟩ ⟨c, -, d, -, rfl⟩
        exact ⟨(a + c) % 3, Nat.mod_lt _ (by norm_num), (b + d) % 3, Nat.mod_lt _ (by norm_num),
          hpow a b c d⟩
      inv_mem' := by
        rintro _ ⟨a, ha, b, hb, rfl⟩
        refine ⟨(3 - a) % 3, Nat.mod_lt _ (by norm_num), (3 - b) % 3, Nat.mod_lt _ (by norm_num), ?_⟩
        rw [eq_comm, eq_inv_iff_mul_eq_one, hpow]
        have e1 : (3 - a) % 3 + a = 3 * ((3 - a) % 3 + a) / 3 := by omega
        rw [← pow_mod3 hq3, ← pow_mod3 hp3, show (3 - a) % 3 + a = 3 * (((3 - a) % 3 + a) / 3) by
          omega, show (3 - b) % 3 + b = 3 * (((3 - b) % 3 + b) / 3) by omega, pow_mul, pow_mul, hq3,
          hp3, one_pow, one_pow, one_mul] }
  have hdec : ∀ t ∈ A.comap f, ∃ r ∈ R, ∃ a < 3, ∃ b < 3, t = r * (u ^ a * v ^ b) := by
    rintro t ⟨a, ha, b, hb, hab⟩
    refine ⟨t * (u ^ a * v ^ b)⁻¹, ?_, a, ha, b, hb, by group⟩
    have h1 : f t = f (u ^ a * v ^ b) := by rw [map_mul, map_pow, map_pow]; exact hab
    have h2 := (QuotientGroup.eq (s := R)).1 h1
    have h3 := ‹R.Normal›.conj_mem _ h2 t
    have e : t * (t⁻¹ * (u ^ a * v ^ b)) * t⁻¹ = (t * (u ^ a * v ^ b)⁻¹)⁻¹ := by group
    rw [e] at h3
    simpa using R.inv_mem h3
  have hinv : ∀ c < 3, ∀ d < 3, (q ^ c * p ^ d)⁻¹ = q ^ ((3 - c) % 3) * p ^ ((3 - d) % 3) := by
    intro c hc d hd
    rw [eq_comm, eq_inv_iff_mul_eq_one, hpow, ← pow_mod3 hq3, ← pow_mod3 hp3,
      show (3 - c) % 3 + c = 3 * (((3 - c) % 3 + c) / 3) by omega,
      show (3 - d) % 3 + d = 3 * (((3 - d) % 3 + d) / 3) by omega, pow_mul, pow_mul, hq3, hp3,
      one_pow, one_pow, one_mul]
  have key : ∀ a < 3, ∀ b < 3, ∀ c < 3, ∀ d < 3, q ^ a * p ^ b = q ^ c * p ^ d → a = c ∧ b = d := by
    intro a ha b hb c hc d hd h
    have h1 : q ^ a * p ^ b * (q ^ c * p ^ d)⁻¹ = 1 := by rw [h, mul_inv_cancel]
    rw [hinv c hc d hd, hpow] at h1
    have h1' : f (u ^ ((a + (3 - c) % 3) % 3) * v ^ ((b + (3 - d) % 3) % 3)) = 1 := by
      rw [map_mul, map_pow, map_pow]
      exact h1
    obtain ⟨e1, e2⟩ := hS _ (Nat.mod_lt _ (by norm_num)) _ (Nat.mod_lt _ (by norm_num))
      ((QuotientGroup.eq_one_iff _).1 h1')
    omega
  have hfR : ∀ r ∈ R, f r = 1 := fun r hr => (QuotientGroup.eq_one_iff _).2 hr
  have hmem : ∀ (r : R) (a b : Fin 3), (r : H) * (u ^ a.val * v ^ b.val) ∈ A.comap f := by
    intro r a b
    refine ⟨a.val, a.2, b.val, b.2, ?_⟩
    change f ((r : H) * (u ^ a.val * v ^ b.val)) = q ^ a.val * p ^ b.val
    rw [map_mul, hfR _ r.2, one_mul, map_mul, map_pow, map_pow]
  let F : R × Fin 3 × Fin 3 → A.comap f := fun x =>
    ⟨(x.1 : H) * (u ^ x.2.1.val * v ^ x.2.2.val), hmem x.1 x.2.1 x.2.2⟩
  have hbij : Function.Bijective F := by
    constructor
    · rintro ⟨r, a, b⟩ ⟨r', c, d⟩ he
      have h := congrArg Subtype.val he
      change (r : H) * (u ^ a.val * v ^ b.val) = (r' : H) * (u ^ c.val * v ^ d.val) at h
      have hf := congrArg f h
      simp only [map_mul, map_pow, hfR _ r.2, hfR _ r'.2, one_mul] at hf
      obtain ⟨hac, hbd⟩ := key _ a.2 _ b.2 _ c.2 _ d.2 hf
      have ha : a = c := Fin.ext hac
      have hb : b = d := Fin.ext hbd
      subst ha
      subst hb
      have hr : r = r' := Subtype.ext (mul_right_cancel h)
      rw [hr]
    · rintro ⟨t, ht⟩
      obtain ⟨r, hr, a, ha, b, hb, rfl⟩ := hdec t ht
      exact ⟨(⟨r, hr⟩, ⟨a, ha⟩, ⟨b, hb⟩), rfl⟩
  refine ⟨A.comap f, fun r hr => ⟨0, by norm_num, 0, by norm_num, ?_⟩, ?_, hdec⟩
  · simp only [pow_zero, mul_one]
    exact (QuotientGroup.eq_one_iff _).2 hr
  · rw [← Nat.card_eq_of_bijective F hbij, Nat.card_prod, Nat.card_prod, Nat.card_eq_fintype_card
      (α := Fin 3), Fintype.card_fin]
    ring

theorem eq_one_of_cosets {R Z T : Subgroup H} {S : Set H}
    (hRT : ∀ t ∈ T, ∃ r ∈ R, ∃ s ∈ S, t = r * s)
    (hcomm : ∀ a ∈ R, ∀ b ∈ R, a * b * a⁻¹ * b⁻¹ ∈ Z)
    (hS : ∀ s ∈ S, s ≠ 1 → ∃ r ∈ R, s * r * s⁻¹ * r⁻¹ ∉ Z) :
    ∀ t ∈ T, (∀ r ∈ R, t * r = r * t) → t ∈ R := by
  intro t ht htc
  obtain ⟨r, hr, s, hs, rfl⟩ := hRT t ht
  by_cases h1 : s = 1
  · rw [h1, mul_one]
    exact hr
  · exfalso
    obtain ⟨q, hq, hqZ⟩ := hS s hs h1
    have hc := htc q hq
    have e : s * q * s⁻¹ * q⁻¹ = r⁻¹ * q * r⁻¹⁻¹ * q⁻¹ := by
      have : s = r⁻¹ * (r * s) := by group
      rw [this]
      calc r⁻¹ * (r * s) * q * (r⁻¹ * (r * s))⁻¹ * q⁻¹
          = r⁻¹ * ((r * s) * q) * (r * s)⁻¹ * r * q⁻¹ := by group
        _ = r⁻¹ * (q * (r * s)) * (r * s)⁻¹ * r * q⁻¹ := by rw [hc]
        _ = r⁻¹ * q * r⁻¹⁻¹ * q⁻¹ := by group
    exact hqZ (e ▸ hcomm _ (R.inv_mem hr) q hq)

end CFSG.KC.Co3Cent

end

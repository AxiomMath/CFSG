module

public import CFSG.LocalAnalysis.ComponentClassification.CatFactsSp4Gauss

public noncomputable section

namespace CFSG.ComponentClassification.GSThmB

open CFSG Subgroup CatFactsSp4
open scoped QuadraticAlgebra

namespace Cat7E6

variable {K : Type} [Field K]

@[expose] def starU : (Gauss K)ˣ →* (Gauss K)ˣ :=
  Units.map (starRingEnd (Gauss K)).toMonoidHom

@[simp] theorem coe_starU (u : (Gauss K)ˣ) :
    ((starU u : (Gauss K)ˣ) : Gauss K) = star (u : Gauss K) := rfl

@[expose] def rho (u : (Gauss K)ˣ) : (Gauss K)ˣ := u * (starU u)⁻¹

theorem star_eq_self_iff (h2 : (2 : K) ≠ 0) (z : Gauss K) : star z = z ↔ z.im = 0 := by
  constructor
  · intro h
    have h1 := congrArg QuadraticAlgebra.im h
    rw [QuadraticAlgebra.im_star] at h1
    have h3 : (2 : K) * z.im = 0 := by linear_combination -h1
    exact (mul_eq_zero.mp h3).resolve_left h2
  · intro h
    ext <;> simp [h]

theorem rho_pow_eq_one_iff (u : (Gauss K)ˣ) (n : ℕ) :
    rho u ^ n = 1 ↔ star ((u ^ n : (Gauss K)ˣ) : Gauss K) = ((u ^ n : (Gauss K)ˣ) : Gauss K) := by
  rw [rho, mul_pow, inv_pow, mul_inv_eq_one, ← map_pow, Units.ext_iff, coe_starU]
  exact eq_comm

theorem norm_ne_zero_of_unit (u : (Gauss K)ˣ) : QuadraticAlgebra.norm (u : Gauss K) ≠ 0 := by
  intro h
  have := (QuadraticAlgebra.isUnit_iff_norm_isUnit (R := K)).mp u.isUnit
  rw [h] at this
  exact not_isUnit_zero this

theorem mul_star_eq_norm (z : Gauss K) :
    z * star z = algebraMap K (Gauss K) (QuadraticAlgebra.norm z) :=
  (QuadraticAlgebra.algebraMap_norm_eq_mul_star z).symm

theorem norm_eq (z : Gauss K) : QuadraticAlgebra.norm z = z.re ^ 2 + z.im ^ 2 := by
  rw [QuadraticAlgebra.norm_def]
  ring

theorem two_pow_parts_one {q : ℕ} (hq : q % 4 = 1) (hq1' : 1 < q) :
    ∃ a t t₂ : ℕ, 2 ≤ a ∧ Odd t ∧ Odd t₂ ∧ q - 1 = 2 ^ a * t ∧ q + 1 = 2 * t₂ := by
  have hq1 : q - 1 ≠ 0 := by omega
  obtain ⟨a, t, ⟨r, hr⟩, he⟩ := Nat.exists_eq_two_pow_mul_odd hq1
  obtain ⟨a', rfl⟩ : ∃ a', a = a' + 2 := by
    rcases a with _ | _ | a'
    · exfalso
      rw [pow_zero, one_mul] at he
      omega
    · exfalso
      rw [zero_add, pow_one] at he
      omega
    · exact ⟨a', rfl⟩
  have ha : 2 ≤ a' + 2 := by omega
  refine ⟨a' + 2, t, 2 ^ (a' + 1) * t + 1, ha, ⟨r, hr⟩, ⟨2 ^ a' * t, by ring⟩, he, ?_⟩
  have e : 2 ^ (a' + 2) * t = 2 * (2 ^ (a' + 1) * t) := by ring
  rw [e] at he
  omega

theorem two_pow_parts_three {q : ℕ} (hq : q % 4 = 3) :
    ∃ b t t₂ : ℕ, 2 ≤ b ∧ Odd t ∧ Odd t₂ ∧ q - 1 = 2 * t ∧ q + 1 = 2 ^ b * t₂ := by
  have hq1 : q + 1 ≠ 0 := by omega
  obtain ⟨b, t₂, ⟨r, hr⟩, he⟩ := Nat.exists_eq_two_pow_mul_odd hq1
  have hb : 2 ≤ b := by
    rcases b with _ | _ | b'
    · rw [pow_zero, one_mul] at he
      omega
    · rw [zero_add, pow_one] at he
      omega
    · omega
  exact ⟨b, (q - 1) / 2, t₂, hb, ⟨(q - 3) / 4, by omega⟩, ⟨r, hr⟩, by omega, he⟩

section Split

variable {s : K} (hs : s * s = -1)

@[expose] def phiS (hs : s * s = -1) : Gauss K →ₐ[K] K :=
  QuadraticAlgebra.lift ⟨s, by rw [hs]; simp⟩

theorem phiS_apply (z : Gauss K) : phiS hs z = z.re + z.im * s := by
  simp [phiS, QuadraticAlgebra.lift, mul_comm]

include hs in
theorem neg_mul_neg_s : -s * -s = -1 := by rw [neg_mul_neg, hs]

include hs in
theorem eq_star_of_phiS (h2 : (2 : K) ≠ 0) {z : Gauss K}
    (h : phiS hs z = phiS (neg_mul_neg_s hs) z) : star z = z := by
  rw [phiS_apply, phiS_apply] at h
  have hs0 : s ≠ 0 := by
    rintro rfl
    simp at hs
  rw [star_eq_self_iff h2]
  have h3 : (2 : K) * s * z.im = 0 := by linear_combination h
  exact (mul_eq_zero.mp h3).resolve_left (mul_ne_zero h2 hs0)

theorem phiS_star (z : Gauss K) : phiS hs (star z) = phiS (neg_mul_neg_s hs) z := by
  rw [phiS_apply, phiS_apply, QuadraticAlgebra.re_star, QuadraticAlgebra.im_star]
  ring

end Split

theorem omega_sq : (QuadraticAlgebra.omega : Gauss K) * QuadraticAlgebra.omega = -1 := by
  rw [QuadraticAlgebra.omega_mul_omega_eq_mk]
  ext <;> simp

theorem star_eq_pow_card [Fintype K] {p : ℕ} [Fact p.Prime] [CharP K p] {f : ℕ}
    (hq : Fintype.card K = p ^ f) (h3 : Fintype.card K % 4 = 3) (z : Gauss K) :
    star z = z ^ Fintype.card K := by
  have : CharP (Gauss K) p :=
    charP_of_injective_algebraMap (algebraMap K (Gauss K)).injective p
  have hz : z = algebraMap K (Gauss K) z.re +
      algebraMap K (Gauss K) z.im * QuadraticAlgebra.omega := by
    ext <;> simp [QuadraticAlgebra.omega]
  have hω : (QuadraticAlgebra.omega : Gauss K) ^ Fintype.card K = -QuadraticAlgebra.omega := by
    obtain ⟨k, hk⟩ : ∃ k, Fintype.card K = 2 * (2 * k + 1) + 1 := ⟨Fintype.card K / 4, by omega⟩
    rw [hk, pow_succ, pow_mul, sq, omega_sq, pow_succ, pow_mul, neg_one_sq, one_pow, one_mul]
    simp
  conv_rhs => rw [hz]
  rw [hq, add_pow_char_pow, mul_pow, ← map_pow, ← map_pow, ← hq, FiniteField.pow_card,
    FiniteField.pow_card, hω]
  ext <;> simp [QuadraticAlgebra.omega]

theorem exists_orderOf_eq_two_pow {G : Type*} [Group G] [Finite G] [IsCyclic G] {k t : ℕ}
    (hG : Nat.card G = 2 ^ k * t) (ht : t ≠ 0) : ∃ g : G, orderOf g = 2 ^ k := by
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := G)
  have hog : orderOf g = 2 ^ k * t := by rw [orderOf_eq_card_of_forall_mem_zpowers hg, hG]
  exact ⟨g ^ (orderOf g / 2 ^ k), orderOf_pow_orderOf_div (by rw [hog]; positivity)
    (by rw [hog]; exact dvd_mul_right _ _)⟩

theorem two_ne_zero_of_odd' [Finite K] (hodd : Odd (Nat.card K)) : (2 : K) ≠ 0 := by
  intro h
  obtain ⟨p, hp⟩ := CharP.exists K
  have := (CharP.cast_eq_zero_iff K p 2).mp (by exact_mod_cast h)
  let _ := Fintype.ofFinite K
  obtain ⟨n, hpn, hcard⟩ := FiniteField.card K p
  have hp2 : p = 2 := (Nat.prime_dvd_prime_iff_eq hpn Nat.prime_two).mp this
  rw [Nat.card_eq_fintype_card, hcard, hp2] at hodd
  exact (Nat.not_even_iff_odd.mpr hodd) (Nat.even_pow.mpr ⟨even_two, n.ne_zero⟩)

theorem exists_uv_split [Fintype K] (h2 : (2 : K) ≠ 0) (hodd : Odd (Fintype.card K)) {s : K}
    (hs' : s * s = -1) :
    ∃ (m c : ℕ) (u v : (Gauss K)ˣ), 3 ≤ m ∧ Odd c ∧ Fintype.card K ^ 2 - 1 = 2 ^ m * c ∧
      orderOf (rho u) = 2 ^ (m - 1) ∧ QuadraticAlgebra.norm (v : Gauss K) = -1 ∧
      v ^ 2 ∈ zpowers (rho u) := by
  classical
  set q := Fintype.card K with hqdef
  have hq1 : q % 4 = 1 := by
    have := (FiniteField.isSquare_neg_one_iff (F := K)).mp ⟨s, hs'.symm⟩
    have hq2 : q % 2 = 1 := Nat.odd_iff.mp hodd
    omega
  have hq1' : 1 < q := Fintype.one_lt_card
  obtain ⟨a, t, t₂, ha, ht, ht₂, hqm, hqp⟩ := two_pow_parts_one hq1 hq1'
  have hs2 : s ^ 2 = -1 := by rw [sq]; exact hs'
  obtain ⟨ζ, hoζ⟩ := exists_orderOf_eq_two_pow (G := Kˣ) (k := a) (t := t)
    (by rw [Nat.card_eq_fintype_card, Fintype.card_units, ← hqdef, hqm]) ht.pos.ne'
  set u0 : Gauss K := ⟨((ζ : K) + 1) / 2, (1 - (ζ : K)) * s / 2⟩ with hu0
  have hNu : QuadraticAlgebra.norm u0 = ζ := by
    rw [norm_eq]
    simp only [hu0]
    rw [div_pow, div_pow, mul_pow, hs2]
    field_simp
    ring
  have hu0unit : IsUnit u0 := by
    rw [QuadraticAlgebra.isUnit_iff_norm_isUnit, hNu]
    exact ζ.isUnit
  set u : (Gauss K)ˣ := hu0unit.unit with hu
  have hφ1 : phiS hs' (u : Gauss K) = ζ := by
    rw [hu, IsUnit.unit_spec, phiS_apply]
    show ((ζ : K) + 1) / 2 + (1 - (ζ : K)) * s / 2 * s = ζ
    rw [show ((ζ : K) + 1) / 2 + (1 - (ζ : K)) * s / 2 * s =
      ((ζ : K) + 1 + (1 - (ζ : K)) * (s * s)) / 2 by ring, hs']
    field_simp
    ring
  have hφ2 : phiS (neg_mul_neg_s hs') (u : Gauss K) = 1 := by
    rw [hu, IsUnit.unit_spec, phiS_apply]
    show ((ζ : K) + 1) / 2 + (1 - (ζ : K)) * s / 2 * -s = 1
    rw [show ((ζ : K) + 1) / 2 + (1 - (ζ : K)) * s / 2 * -s =
      ((ζ : K) + 1 - (1 - (ζ : K)) * (s * s)) / 2 by ring, hs']
    field_simp
    ring
  set v0 : Gauss K := ⟨0, s⟩ with hv0
  have hNv : QuadraticAlgebra.norm v0 = -1 := by
    rw [norm_eq]
    simp [hv0, hs2]
  have hv0unit : IsUnit v0 := by
    rw [QuadraticAlgebra.isUnit_iff_norm_isUnit, hNv]
    exact isUnit_one.neg
  set v : (Gauss K)ˣ := hv0unit.unit with hv
  have hv2 : v ^ 2 = 1 := by
    apply Units.ext
    rw [Units.val_pow_eq_pow_val, hv, IsUnit.unit_spec, Units.val_one, sq]
    ext <;> simp [hv0, hs']
  refine ⟨a + 1, t * t₂, u, v, by omega, ht.mul ht₂, ?_, ?_, ?_, ?_⟩
  · have e : q ^ 2 - 1 = (q - 1) * (q + 1) := by
      have : 1 ≤ q := by omega
      zify [this, Nat.one_le_pow 2 q (by omega)]
      ring
    rw [e, hqm, hqp]
    ring
  · rw [Nat.add_sub_cancel, ← hoζ, orderOf_eq_orderOf_iff]
    intro n
    rw [rho_pow_eq_one_iff, ← Units.val_eq_one, Units.val_pow_eq_pow_val]
    constructor
    · intro h
      have h1 := congrArg (phiS hs') h
      rw [phiS_star, map_pow, map_pow, hφ1, hφ2, one_pow] at h1
      exact h1.symm
    · intro h
      apply eq_star_of_phiS hs' h2
      rw [map_pow, map_pow, hφ1, hφ2, one_pow]
      exact h
  · rw [hv, IsUnit.unit_spec]
    exact hNv
  · rw [hv2]
    exact one_mem _

theorem exists_uv_nonsplit [Fintype K] (hsq : ¬ IsSquare (-1 : K)) :
    ∃ (m c : ℕ) (u v : (Gauss K)ˣ), 3 ≤ m ∧ Odd c ∧ Fintype.card K ^ 2 - 1 = 2 ^ m * c ∧
      orderOf (rho u) = 2 ^ (m - 1) ∧ QuadraticAlgebra.norm (v : Gauss K) = -1 ∧
      v ^ 2 ∈ zpowers (rho u) := by
  classical
  set q := Fintype.card K with hqdef
  have hq3 : q % 4 = 3 := by
    by_contra h
    exact hsq ((FiniteField.isSquare_neg_one_iff (F := K)).mpr h)
  obtain ⟨b, t, t₂, hb, ht, ht₂, hqm, hqp⟩ := two_pow_parts_three hq3
  have : Fact (¬ IsSquare (-1 : K)) := ⟨hsq⟩
  let _ : Fintype (Gauss K) := Fintype.ofEquiv (K × K) (QuadraticAlgebra.equivProd _ _).symm
  have hcardE : Fintype.card (Gauss K) = q ^ 2 := by
    rw [Fintype.card_congr (QuadraticAlgebra.equivProd (-1 : K) 0), Fintype.card_prod, sq]
  have hq2 : q ^ 2 - 1 = 2 ^ (b + 1) * (t * t₂) := by
    have e : q ^ 2 - 1 = (q - 1) * (q + 1) := by
      have : 1 ≤ q := by omega
      zify [this, Nat.one_le_pow 2 q (by omega)]
      ring
    rw [e, hqm, hqp]
    ring
  obtain ⟨ω₀, hoω⟩ := exists_orderOf_eq_two_pow (G := (Gauss K)ˣ) (k := b + 1) (t := t * t₂)
    (by rw [Nat.card_eq_fintype_card, Fintype.card_units, hcardE, hq2])
    (ht.mul ht₂).pos.ne'
  obtain ⟨p, hchar⟩ := CharP.exists K
  have : Fact p.Prime := ⟨CharP.char_is_prime K p⟩
  obtain ⟨f, -, hpf⟩ := FiniteField.card K p
  have hstar : ∀ z : (Gauss K)ˣ, starU z = z ^ q := fun z => by
    apply Units.ext
    rw [coe_starU, Units.val_pow_eq_pow_val]
    exact star_eq_pow_card hpf hq3 _
  have hq0 : q - 1 ≠ 0 := by omega
  have hrho : rho ω₀ = (ω₀ ^ (q - 1))⁻¹ := by
    rw [rho, hstar, show q = (q - 1) + 1 by omega, pow_succ, mul_inv_rev, mul_inv_cancel_left,
      Nat.add_sub_cancel]
  have hgcd1 : Nat.gcd (2 ^ (b + 1)) (q - 1) = 2 := by
    rw [hqm, pow_succ, mul_comm (2 ^ b) 2, Nat.gcd_mul_left,
      Nat.Coprime.pow_left b (Nat.coprime_two_left.mpr ht), mul_one]
  have hgcd2 : Nat.gcd (2 ^ (b + 1)) (q + 1) = 2 ^ b := by
    rw [hqp, pow_succ, Nat.gcd_mul_left, Nat.Coprime.gcd_eq_one, mul_one]
    exact Nat.coprime_two_left.mpr ht₂
  have horho : orderOf (rho ω₀) = 2 ^ b := by
    rw [hrho, orderOf_inv, orderOf_pow' _ hq0, hoω, hgcd1, pow_succ, Nat.mul_div_cancel _ two_pos]
  refine ⟨b + 1, t * t₂, ω₀, ω₀, by omega, ht.mul ht₂, hq2, by rw [Nat.add_sub_cancel]; exact horho,
    ?_, ?_⟩
  ·
    have hN : algebraMap K (Gauss K) (QuadraticAlgebra.norm (ω₀ : Gauss K)) =
        ((ω₀ ^ (q + 1) : (Gauss K)ˣ) : Gauss K) := by
      rw [← mul_star_eq_norm, ← coe_starU, hstar, ← Units.val_mul, ← pow_succ']
    have ho : orderOf (ω₀ ^ (q + 1)) = 2 := by
      rw [orderOf_pow' _ (by omega), hoω, hgcd2, pow_succ,
        Nat.mul_div_cancel_left _ (by positivity)]
    have hsq1 : ((ω₀ ^ (q + 1) : (Gauss K)ˣ) : Gauss K) ^ 2 = 1 := by
      rw [← Units.val_pow_eq_pow_val, ← ho, pow_orderOf_eq_one, Units.val_one]
    have hne1 : ((ω₀ ^ (q + 1) : (Gauss K)ˣ) : Gauss K) ≠ 1 := by
      intro h
      have : ω₀ ^ (q + 1) = 1 := Units.ext h
      rw [this, orderOf_one] at ho
      exact absurd ho (by norm_num)
    have hm1 : ((ω₀ ^ (q + 1) : (Gauss K)ˣ) : Gauss K) = -1 := by
      rw [sq] at hsq1
      exact (mul_self_eq_one_iff.mp hsq1).resolve_left hne1
    rw [hm1] at hN
    apply (algebraMap K (Gauss K)).injective
    rw [hN, map_neg, map_one]
  ·
    have hle : zpowers (rho ω₀) ≤ zpowers (ω₀ ^ 2) := by
      rw [zpowers_le, hrho, hqm, pow_mul]
      exact inv_mem (pow_mem (mem_zpowers _) t)
    have ho2 : orderOf (ω₀ ^ 2) = 2 ^ b := by
      rw [orderOf_pow' _ two_ne_zero, hoω, pow_succ,
        Nat.gcd_eq_right (dvd_mul_left 2 _), Nat.mul_div_cancel _ two_pos]
    have heq : zpowers (rho ω₀) = zpowers (ω₀ ^ 2) := by
      apply Subgroup.eq_of_le_of_card_ge hle
      rw [Nat.card_zpowers, Nat.card_zpowers, horho, ho2]
    rw [heq]
    exact mem_zpowers _

theorem exists_uv [Finite K] (hodd : Odd (Nat.card K)) :
    ∃ (m c : ℕ) (u v : (Gauss K)ˣ), 3 ≤ m ∧ Odd c ∧ Nat.card K ^ 2 - 1 = 2 ^ m * c ∧
      orderOf (rho u) = 2 ^ (m - 1) ∧ QuadraticAlgebra.norm (v : Gauss K) = -1 ∧
      v ^ 2 ∈ zpowers (rho u) := by
  let _ := Fintype.ofFinite K
  have h2 := two_ne_zero_of_odd' hodd
  rw [Nat.card_eq_fintype_card]
  by_cases hsq : IsSquare (-1 : K)
  · obtain ⟨s, hs⟩ := hsq
    exact exists_uv_split h2 (Nat.card_eq_fintype_card (α := K) ▸ hodd) hs.symm
  · exact exists_uv_nonsplit hsq

end Cat7E6

end CFSG.ComponentClassification.GSThmB

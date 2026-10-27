module

public import CFSG.CharacterTheory.Semidihedral.UnitaryDValueLocal
public import CFSG.CharacterTheory.CyclicBlocks.AbelianInertialIndexTwo
public import CFSG.CharacterTheory.Wreathed.BrauerWreathedOrderDegree
public import CFSG.CharacterTheory.Wreathed.ConditionalGeneralBaseCharacters

public section

open scoped BigOperators Classical

namespace CFSG.Semidihedral.UnitaryDValue

open CFSG.TwoRankLowerBound.Helpers

namespace DValueData

variable {G : Type} [Group G] [Fintype G] (D : DValueData G)

theorem card_G_eq : Nat.card G =
    D.m * Nat.card D.A * D.q ^ 3 * (D.q - 1) * ((D.q + 1) * (D.q ^ 2 - D.q + 1)) := by
  rw [← D.cube_add_one_eq]
  exact D.card_G

theorem coprime_card_G {n : ℕ}
    (h : ∀ r : ℕ, r.Prime → r ∣ n → r ≠ 2 ∧ ¬ r ∣ D.q ∧ ¬ r ∣ D.q - 1 ∧ ¬ r ∣ D.q + 1 ∧
      ¬ r ∣ D.q ^ 2 - D.q + 1) : Nat.Coprime n (Nat.card G) := by
  apply Nat.coprime_of_dvd
  intro r hr hrn hrG
  obtain ⟨h2, hq, hq1, hqp, hQ⟩ := h r hr hrn
  rw [D.card_G_eq] at hrG
  rcases (Nat.Prime.dvd_mul hr).mp hrG with h1 | h1
  · rcases (Nat.Prime.dvd_mul hr).mp h1 with h3 | h3
    · rcases (Nat.Prime.dvd_mul hr).mp h3 with h4 | h4
      · rcases (Nat.Prime.dvd_mul hr).mp h4 with h5 | h5
        · obtain ⟨k, hk⟩ := D.m_pow
          rw [hk] at h5
          exact h2 ((Nat.prime_dvd_prime_iff_eq hr Nat.prime_two).mp (hr.dvd_of_dvd_pow h5))
        · exact hqp (h5.trans D.card_A_dvd)
      · exact hq (hr.dvd_of_dvd_pow h4)
    · exact hq1 h3
  · rcases (Nat.Prime.dvd_mul hr).mp h1 with h3 | h3
    · exact hqp h3
    · exact hQ h3

theorem not_cube_sub_one_dvd_card_G : ¬ D.q ^ 3 - 1 ∣ Nat.card G := by
  intro hdvd
  have hq7 := D.seven_le_q
  set q := D.q with hq
  have hsplit : q ^ 3 - 1 = (q - 1) * (q ^ 2 + q + 1) := by
    have : 1 ≤ q ^ 3 := Nat.one_le_pow _ _ (by omega)
    zify [this, show 1 ≤ q by omega]
    ring
  have hdvd' : q ^ 2 + q + 1 ∣ Nat.card G := (Dvd.intro_left _ hsplit.symm).trans hdvd
  have hcop : Nat.Coprime (q ^ 2 + q + 1)
      (D.m * Nat.card D.A * q ^ 3 * ((q + 1) * (q ^ 2 - q + 1))) := by
    apply Nat.coprime_of_dvd
    intro r hr hr1 hr2
    have hrq : ¬ r ∣ q := by
      intro h
      have : r ∣ q ^ 2 + q := dvd_add (dvd_pow h (by norm_num)) h
      exact hr.one_lt.ne' (Nat.dvd_one.mp ((Nat.dvd_add_right this).mp hr1))
    have hrq1 : ¬ r ∣ q + 1 := by
      intro h
      have : r ∣ q * (q + 1) := dvd_mul_of_dvd_right h q
      rw [show q ^ 2 + q + 1 = q * (q + 1) + 1 by ring] at hr1
      exact hr.one_lt.ne' (Nat.dvd_one.mp ((Nat.dvd_add_right this).mp hr1))
    have hrQ : ¬ r ∣ q ^ 2 - q + 1 := by
      intro h
      have hle : q ≤ q ^ 2 := Nat.le_self_pow (by norm_num) _
      have h2q : r ∣ 2 * q := by
        have : q ^ 2 + q + 1 - (q ^ 2 - q + 1) = 2 * q := by omega
        rw [← this]
        exact Nat.dvd_sub hr1 h
      rcases (Nat.Prime.dvd_mul hr).mp h2q with h' | h'
      · have hr2' : r = 2 := (Nat.prime_dvd_prime_iff_eq hr Nat.prime_two).mp h'
        subst hr2'
        have hodd : Odd (q ^ 2 + q + 1) := by
          obtain ⟨k, hk⟩ := D.q_odd
          rw [← hq] at hk
          rw [hk]
          exact ⟨2 * k ^ 2 + 3 * k + 1, by ring⟩
        exact (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr hr1)
      · exact hrq h'
    rcases (Nat.Prime.dvd_mul hr).mp hr2 with h1 | h1
    · rcases (Nat.Prime.dvd_mul hr).mp h1 with h3 | h3
      · rcases (Nat.Prime.dvd_mul hr).mp h3 with h4 | h4
        · obtain ⟨k, hk⟩ := D.m_pow
          rw [hk] at h4
          have hr2' := (Nat.prime_dvd_prime_iff_eq hr Nat.prime_two).mp (hr.dvd_of_dvd_pow h4)
          subst hr2'
          have hodd : Odd (q ^ 2 + q + 1) := by
            obtain ⟨k, hk⟩ := D.q_odd
            rw [← hq] at hk
            rw [hk]
            exact ⟨2 * k ^ 2 + 3 * k + 1, by ring⟩
          exact (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr hr1)
        · exact hrq1 (h4.trans D.card_A_dvd)
      · exact hrq (hr.dvd_of_dvd_pow h3)
    · rcases (Nat.Prime.dvd_mul hr).mp h1 with h3 | h3
      · exact hrq1 h3
      · exact hrQ h3
  rw [D.card_G_eq,
    show D.m * Nat.card D.A * q ^ 3 * (q - 1) * ((q + 1) * (q ^ 2 - q + 1)) =
      D.m * Nat.card D.A * q ^ 3 * ((q + 1) * (q ^ 2 - q + 1)) * (q - 1) by ring] at hdvd'
  have h := hcop.dvd_of_dvd_mul_left hdvd'
  have := Nat.le_of_dvd (by omega) h
  omega


theorem not_dvd_card_G_sq_add_one : ¬ (D.q - 1) * (D.q ^ 2 + 1) ∣ Nat.card G := by
  intro hdvd
  have hq7 := D.seven_le_q
  obtain ⟨k, hk⟩ := D.q_odd
  set q := D.q with hq
  have hsq : q ^ 2 + 1 = 2 * (2 * k ^ 2 + 2 * k + 1) := by rw [hk]; ring
  set o := 2 * k ^ 2 + 2 * k + 1 with ho
  have hodd : Odd o := ⟨k ^ 2 + k, by ring⟩
  have hodvd : o ∣ Nat.card G :=
    (Dvd.intro_left _ hsq.symm).trans ((Dvd.intro_left _ rfl).trans hdvd)
  have hcop : Nat.Coprime o (Nat.card G) := by
    apply D.coprime_card_G
    intro r hr hro
    have hr2 : r ≠ 2 := by
      rintro rfl
      exact (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr hro)
    have hrs : r ∣ q ^ 2 + 1 := hro.trans ⟨2, by rw [hsq]; ring⟩
    have h2 : ¬ r ∣ 2 := fun h => hr2 ((Nat.prime_dvd_prime_iff_eq hr Nat.prime_two).mp h)
    have hid : q ^ 2 + 1 = (q - 1) * (q + 1) + 2 := by
      zify [show 1 ≤ q by omega]
      ring
    refine ⟨hr2, fun h => ?_, fun h => ?_, fun h => ?_, fun h => ?_⟩
    · have : r ∣ q ^ 2 := dvd_pow h (by norm_num)
      exact hr.one_lt.ne' (Nat.dvd_one.mp ((Nat.dvd_add_right this).mp hrs))
    · rw [hid] at hrs
      exact h2 ((Nat.dvd_add_right (dvd_mul_of_dvd_left h _)).mp hrs)
    · rw [hid] at hrs
      exact h2 ((Nat.dvd_add_right (dvd_mul_of_dvd_right h _)).mp hrs)
    · have hle : q ≤ q ^ 2 := Nat.le_self_pow (by norm_num) _
      have hq' : r ∣ q := by
        have : q ^ 2 + 1 - (q ^ 2 - q + 1) = q := by omega
        rw [← this]
        exact Nat.dvd_sub hrs h
      have : r ∣ q ^ 2 := dvd_pow hq' (by norm_num)
      exact hr.one_lt.ne' (Nat.dvd_one.mp ((Nat.dvd_add_right this).mp hrs))
  have ho1 : o = 1 := Nat.Coprime.eq_one_of_dvd hcop hodvd
  have : q ^ 2 + 1 = 2 := by rw [hsq, ho1]
  nlinarith

theorem factorization_two_q_add_one : (D.q + 1).factorization 2 = D.m.factorization 2 := by
  have hm := D.m_dvd
  obtain ⟨c, hc⟩ := hm
  have hc' : (D.q + 1) / D.m = c := by
    rw [hc, Nat.mul_div_cancel_left _ D.m_pos]
  have hodd := D.odd_quot
  rw [hc'] at hodd
  have hc0 : c ≠ 0 := by rintro rfl; exact (Nat.not_odd_zero hodd)
  have hc2 : c.factorization 2 = 0 := Nat.factorization_eq_zero_of_not_dvd (by
    intro h
    exact (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr h))
  change (D.p ^ D.f + 1).factorization 2 = _
  rw [hc, fact_mul D.m_pos.ne' hc0, hc2, add_zero]

theorem not_dvd_card_G_Q_add_one (h5 : 5 ∣ D.q + 1) : ¬ D.q ^ 2 - D.q + 2 ∣ Nat.card G := by
  intro hdvd
  have hq7 := D.seven_le_q
  set q := D.q with hq
  have hle : q ≤ q ^ 2 := Nat.le_self_pow (by norm_num) _
  have hne : q ^ 2 - q + 2 ≠ 0 := by omega
  obtain ⟨j, o, hodd, hjo⟩ := Nat.exists_eq_two_pow_mul_odd hne
  have hodvd : o ∣ Nat.card G := (Dvd.intro_left _ hjo.symm).trans hdvd
  have hcop : Nat.Coprime o (Nat.card G) := by
    apply D.coprime_card_G
    intro r hr hro
    have hr2 : r ≠ 2 := by
      rintro rfl
      exact (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr hro)
    have hrs : r ∣ q ^ 2 - q + 2 := hro.trans ⟨2 ^ j, by rw [hjo]; ring⟩
    have h2 : ¬ r ∣ 2 := fun h => hr2 ((Nat.prime_dvd_prime_iff_eq hr Nat.prime_two).mp h)
    have hid : q ^ 2 - q + 2 = q * (q - 1) + 2 := by
      zify [hle, show 1 ≤ q by omega]
      ring
    have hid' : q ^ 2 - q + 2 = (q + 1) * (q - 2) + 4 := by
      zify [hle, show 2 ≤ q by omega]
      ring
    refine ⟨hr2, fun h => ?_, fun h => ?_, fun h => ?_, fun h => ?_⟩
    · rw [hid] at hrs
      exact h2 ((Nat.dvd_add_right (dvd_mul_of_dvd_left h _)).mp hrs)
    · rw [hid] at hrs
      exact h2 ((Nat.dvd_add_right (dvd_mul_of_dvd_right h _)).mp hrs)
    · rw [hid'] at hrs
      have h4 : r ∣ 4 := (Nat.dvd_add_right (dvd_mul_of_dvd_left h _)).mp hrs
      have : r ∣ 2 ^ 2 := by simpa using h4
      exact h2 (hr.dvd_of_dvd_pow this)
    · have : r ∣ 1 := by
        have h' : q ^ 2 - q + 2 - (q ^ 2 - q + 1) = 1 := by omega
        rw [← h']
        exact Nat.dvd_sub hrs h
      exact hr.one_lt.ne' (Nat.dvd_one.mp this)
  have ho1 : o = 1 := Nat.Coprime.eq_one_of_dvd hcop hodvd
  rw [ho1, mul_one] at hjo
  have hpow : 2 ^ j ∣ Nat.card G := hjo ▸ hdvd
  have hj : j ≤ (Nat.card G).factorization 2 :=
    (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_two Nat.card_pos.ne').mp hpow
  obtain ⟨k, hk⟩ := D.m_pow
  have hmk : D.m.factorization 2 = k := by
    rw [hk, Nat.factorization_pow, Finsupp.smul_apply, Nat.Prime.factorization_self Nat.prime_two,
      smul_eq_mul, mul_one]
  have hA2 : (Nat.card D.A).factorization 2 = 0 :=
    Nat.factorization_eq_zero_of_not_dvd (by
      intro h; exact (Nat.not_even_iff_odd.mpr D.A_odd) (even_iff_two_dvd.mpr h))
  have hq2 : q.factorization 2 = 0 :=
    Nat.factorization_eq_zero_of_not_dvd (by
      intro h; exact (Nat.not_even_iff_odd.mpr D.q_odd) (even_iff_two_dvd.mpr h))
  have hQodd : Odd (q ^ 2 - q + 1) := by
    obtain ⟨a, ha⟩ := D.q_odd
    rw [← hq] at ha
    refine ⟨2 * a ^ 2 + a, ?_⟩
    rw [ha]
    zify [show 2 * a + 1 ≤ (2 * a + 1) ^ 2 by nlinarith]
    ring
  have hQ2 : (q ^ 2 - q + 1).factorization 2 = 0 :=
    Nat.factorization_eq_zero_of_not_dvd (by
      intro h; exact (Nat.not_even_iff_odd.mpr hQodd) (even_iff_two_dvd.mpr h))
  have hq3 : q ^ 3 ≠ 0 := pow_ne_zero 3 (by omega)
  have hG2 : (Nat.card G).factorization 2 = k + (q - 1).factorization 2 + k := by
    rw [D.card_G_eq,
      fact_mul (Nat.mul_ne_zero (Nat.mul_ne_zero (Nat.mul_ne_zero D.m_pos.ne' D.card_A_pos.ne')
        hq3) (by omega)) (Nat.mul_ne_zero (by omega) (by omega)),
      fact_mul (Nat.mul_ne_zero (Nat.mul_ne_zero D.m_pos.ne' D.card_A_pos.ne') hq3) (by omega),
      fact_mul (Nat.mul_ne_zero D.m_pos.ne' D.card_A_pos.ne') hq3,
      fact_mul D.m_pos.ne' D.card_A_pos.ne', fact_mul (by omega) (by omega),
      Nat.factorization_pow, Finsupp.smul_apply, hmk, hA2, hq2, hQ2,
      D.factorization_two_q_add_one, hmk]
    simp only [smul_eq_mul, mul_zero, add_zero]
    rfl
  rcases (show q % 4 = 1 ∨ q % 4 = 3 by have := D.q_odd; obtain ⟨a, ha⟩ := this; omega) with
    h4 | h4
  ·
    have hmod : (q ^ 2 - q + 2) % 4 = 2 := by
      obtain ⟨s, hs⟩ : ∃ s, q = 4 * s + 1 := ⟨q / 4, by omega⟩
      rw [hs]
      have : (4 * s + 1) ^ 2 - (4 * s + 1) + 2 = 4 * (4 * s ^ 2 + s) + 2 := by
        have h1 : 4 * s + 1 ≤ (4 * s + 1) ^ 2 := Nat.le_self_pow (by norm_num) _
        zify [h1]
        ring
      rw [this]
      omega
    have hqq : 7 * q ≤ q ^ 2 := by nlinarith
    rw [hjo] at hmod
    rcases j with _ | _ | j
    · simp at hmod
    · have : q ^ 2 - q + 2 = 2 := by rw [hjo]; norm_num
      omega
    · rw [pow_succ, pow_succ] at hmod
      omega
  ·
    have hq1 : (q - 1).factorization 2 = 1 := by
      obtain ⟨s, hs⟩ : ∃ s, q - 1 = 2 * (2 * s + 1) := ⟨q / 4, by omega⟩
      rw [hs, fact_mul (by norm_num) (by omega), Nat.Prime.factorization_self Nat.prime_two,
        Nat.factorization_eq_zero_of_not_dvd (by omega)]
    rw [hG2, hq1] at hj
    have h5m : 5 * D.m ∣ q + 1 := by
      apply Nat.Coprime.mul_dvd_of_dvd_of_dvd _ h5 D.m_dvd
      rw [hk]
      exact Nat.Coprime.pow_right _ (by norm_num)
    have h5m' : 5 * D.m ≤ q + 1 := Nat.le_of_dvd (by omega) h5m
    have hpowle : 2 ^ j ≤ 2 ^ (2 * k + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
    have hm2 : 2 ^ (2 * k + 1) = 2 * D.m ^ 2 := by rw [hk]; ring
    rw [hm2, ← hjo] at hpowle
    have h25 : 25 * D.m ^ 2 ≤ (q + 1) ^ 2 := by
      have := Nat.mul_le_mul h5m' h5m'
      nlinarith
    have hexp : (q + 1) ^ 2 = q ^ 2 + 2 * q + 1 := by ring
    have hqq : 7 * q ≤ q ^ 2 := by nlinarith
    omega

theorem finrank_dvd_card (basis : FiniteIrreducibleCharacterBasis G) (χ : basis.index) :
    Module.finrank ℂ (basis.representation χ).vector ∣ Nat.card G := by
  have : Representation.IsIrreducible (basis.representation χ).representation :=
    basis.irreducible χ
  exact Theory.Character.irreducible_dimension_dvd_group_order
    (basis.representation χ).representation

include D in
theorem eq_principal_of_real_linear (basis : FiniteIrreducibleCharacterBasis G)
    (principal : basis.index) (hprincipal : (basis.representation principal).character = 1)
    {χ : basis.index}
    (hreal : ∀ g, starRingEnd ℂ ((basis.representation χ).character g) =
      (basis.representation χ).character g)
    (hdeg : Module.finrank ℂ (basis.representation χ).vector = 1) : χ = principal := by
  set V := basis.representation χ
  have hmul := CFSG.Wreathed.BrauerWreathedOrder.character_mul_of_finrank_eq_one V hdeg
  have hone := CFSG.Wreathed.BrauerWreathedOrder.character_one_of_finrank_eq_one V hdeg
  have hsq : ∀ g, V.character g = 1 ∨ V.character g = -1 := by
    intro g
    have h1 : V.character g * V.character g⁻¹ = 1 := by rw [← hmul, mul_inv_cancel, hone]
    have h2 : V.character g⁻¹ = V.character g := by
      rw [← finite_character_conjugate_inverse V g, hreal g]
    rw [h2] at h1
    have : (V.character g - 1) * (V.character g + 1) = 0 := by ring_nf; rw [← h1]; ring
    rcases mul_eq_zero.mp this with h | h
    · left; linear_combination h
    · right; linear_combination h
  by_contra hne
  have hex : ∃ g, V.character g = -1 := by
    by_contra hall
    push Not at hall
    apply hne
    apply basis.distinct
    change V.character = (basis.representation principal).character
    rw [hprincipal]
    funext g
    rcases hsq g with h | h
    · rw [h]; rfl
    · exact absurd h (hall g)
  obtain ⟨a, ha⟩ := hex
  let H : Subgroup G :=
    { carrier := {g | V.character g = 1}
      one_mem' := hone
      mul_mem' := fun {g h} hg hh => by
        change V.character (g * h) = 1
        rw [hmul, show V.character g = 1 from hg, show V.character h = 1 from hh, one_mul]
      inv_mem' := fun {g} hg => by
        change V.character g⁻¹ = 1
        have h1 : V.character g * V.character g⁻¹ = 1 := by rw [← hmul, mul_inv_cancel, hone]
        rw [show V.character g = 1 from hg, one_mul] at h1
        exact h1 }
  apply D.index_ne_two H
  rw [Subgroup.index_eq_two_iff]
  refine ⟨a, fun b => ?_⟩
  change Xor (V.character (b * a) = 1) (V.character b = 1)
  rw [hmul, ha]
  rcases hsq b with h | h
  · rw [h]
    exact Or.inr ⟨rfl, by norm_num⟩
  · rw [h]
    exact Or.inl ⟨by norm_num, by norm_num⟩

theorem dvd_finrank_sub {r : ℕ} [Fact r.Prime] (basis : FiniteIrreducibleCharacterBasis G)
    (P : Sylow r G) (χ : basis.index) (δ : ℤ)
    (hval : ∀ g : G, r ∣ orderOf g → (basis.representation χ).character g = δ) :
    (Nat.card P : ℤ) ∣ (Module.finrank ℂ (basis.representation χ).vector : ℤ) - δ := by
  have hr : r.Prime := Fact.out
  obtain ⟨k, hk⟩ := CFSG.Wreathed.ConditionalGeneralBase.restriction_linear_pairing_nat basis
    (P : Subgroup G) (1 : (P : Subgroup G) →* ℂ) χ
  simp only [MonoidHom.one_apply, map_one, mul_one] at hk
  have hsum : ∑ u : (P : Subgroup G), (basis.representation χ).character u =
      (Module.finrank ℂ (basis.representation χ).vector : ℂ) + ((Nat.card P : ℂ) - 1) * δ := by
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ (1 : (P : Subgroup G)))]
    congr 1
    · rw [Subgroup.coe_one, FiniteComplexRepresentation.character, Representation.char_one]
    · rw [Finset.sum_congr rfl (g := fun _ => (δ : ℂ)) (fun u hu => ?_), Finset.sum_const,
        Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, nsmul_eq_mul,
        Nat.card_eq_fintype_card]
      · rw [Nat.cast_sub Fintype.card_pos, Nat.cast_one]
      · have hu1 : u ≠ 1 := (Finset.mem_erase.mp hu).1
        apply hval
        obtain ⟨n, hn⟩ := (IsPGroup.iff_orderOf.mp P.isPGroup') u
        rw [Subgroup.orderOf_coe, hn]
        rcases n with _ | n
        · exfalso
          rw [pow_zero] at hn
          exact hu1 (orderOf_eq_one_iff.mp hn)
        · exact dvd_pow_self r (Nat.succ_ne_zero n)
  rw [hsum] at hk
  have hP0 : (Nat.card P : ℂ) ≠ 0 := by exact_mod_cast Nat.card_pos.ne'
  have hk' : (Module.finrank ℂ (basis.representation χ).vector : ℂ) +
      ((Nat.card P : ℂ) - 1) * δ = k * Nat.card P := by
    field_simp at hk
    linear_combination hk
  have hkZ : (Module.finrank ℂ (basis.representation χ).vector : ℤ) +
      ((Nat.card P : ℤ) - 1) * δ = k * Nat.card P := by exact_mod_cast hk'
  exact ⟨k - δ, by linear_combination hkZ⟩

theorem false_of_inverted_sylow {r : ℕ} [Fact r.Prime] (hr2 : r ≠ 2) (P : Sylow r G)
    (hcomm : ∀ x ∈ (P : Subgroup G), ∀ y ∈ (P : Subgroup G), x * y = y * x)
    (hN : (Subgroup.centralizer (P : Set G)).relIndex (Subgroup.normalizer (P : Set G)) = 2)
    (τ : G) (hτN : τ ∈ Subgroup.normalizer (P : Set G))
    (hτ : ∀ x ∈ (P : Subgroup G), τ * x * τ⁻¹ = x⁻¹)
    (hP5 : 5 ≤ Nat.card P)
    (hcube : (Nat.card P : ℤ) ∣ (D.q : ℤ) ^ 3 + 1)
    (hQ : (Nat.card P : ℤ) ∣ (D.q : ℤ) ^ 2 - D.q + 1 - 3)
    (h3q : (Nat.card P : ℤ) ∣ 3 * ((D.q : ℤ) + 1))
    (h5 : Nat.card P = 5 → 5 ∣ D.q + 1) : False := by
  classical
  have hr : r.Prime := Fact.out
  obtain ⟨basis⟩ := finiteIrreducibleCharacterBasis_exists (G := G)
  obtain ⟨principal, hprincipal⟩ := finiteIrreducibleCharacterBasis_contains_irreducible basis
    (principalFiniteComplexRepresentation _) (principalFiniteComplexRepresentation_isIrreducible _)
  rw [principalFiniteComplexRepresentation_character] at hprincipal
  obtain ⟨⟨ideal, hmax, hmem⟩, hchar⟩ := CFSG.BlockBasics.residue_prime_existence r hr
  have : ideal.IsMaximal := hmax
  have : CharP (ComplexAlgebraicIntegers ⧸ ideal) r := hchar ideal hmax hmem
  obtain ⟨ψ₁, ψ, δ, hδ, hψ₁ne, -, -, hψ₁val, hψdeg, hψ₁real, hψreal, -⟩ :=
    CFSG.CyclicBlocks.principal_block_abelian_sylow_inverting_index_two basis ideal r hr2
      principal hprincipal P hcomm hN τ hτN hτ
  set M : ℤ := (Nat.card P : ℤ) with hM
  have hM5 : (5 : ℤ) ≤ M := by rw [hM]; exact_mod_cast hP5
  have hsmall : ∀ x : ℤ, M ∣ x → x ≠ 0 → -5 < x → x < 5 → False := by
    intro x hx hx0 hlo hhi
    exact hx0 (Int.eq_zero_of_abs_lt_dvd hx (by rw [abs_lt]; constructor <;> omega))
  have hfive : M ∣ 5 → Nat.card P = 5 := by
    intro h
    have := Int.le_of_dvd (by norm_num) h
    have h' : M = 5 := by omega
    rw [hM] at h'
    exact_mod_cast h'
  have hcong := dvd_finrank_sub basis P ψ₁ δ hψ₁val
  set d₁ : ℕ := Module.finrank ℂ (basis.representation ψ₁).vector with hd₁
  have h1mem : (1 : ℕ) ∈ Finset.Icc 1 ((Nat.card P - 1) / 2) := by
    simp only [Finset.mem_Icc, le_refl, true_and]
    omega
  set d : ℕ := Module.finrank ℂ (basis.representation (ψ 1)).vector with hd
  have hdd : (d : ℤ) = d₁ + δ := hψdeg 1 h1mem
  have hq7 := D.seven_le_q
  have hle : D.q ≤ D.q ^ 2 := D.q_le_sq
  have hQZ : ((D.q ^ 2 - D.q + 1 : ℕ) : ℤ) = (D.q : ℤ) ^ 2 - D.q + 1 := D.Q_cast
  have hqQZ : ((D.q * (D.q ^ 2 - D.q + 1) : ℕ) : ℤ) = D.q * ((D.q : ℤ) ^ 2 - D.q + 1) := by
    rw [Nat.cast_mul, hQZ]
  have hqQ3 : M ∣ (D.q : ℤ) * ((D.q : ℤ) ^ 2 - D.q + 1) + 3 := by
    have : (D.q : ℤ) * ((D.q : ℤ) ^ 2 - D.q + 1) + 3 =
        (D.q : ℤ) * ((D.q : ℤ) ^ 2 - D.q + 1 - 3) + 3 * ((D.q : ℤ) + 1) := by ring
    rw [this]
    exact dvd_add (dvd_mul_of_dvd_right hQ _) h3q
  have hc : ∀ x c : ℤ, M ∣ x → x = c → M ∣ c := fun x c h e => e ▸ h
  rcases Nat.even_or_odd d₁ with heven | hodd
  ·
    have hdodd : Odd d := by
      obtain ⟨a, ha⟩ := heven
      rcases hδ with rfl | rfl
      · exact ⟨a, by omega⟩
      · refine ⟨a - 1, ?_⟩
        have : a ≥ 1 := by omega
        omega
    have hcong' : M ∣ (d : ℤ) - 2 * δ := by
      rw [show (d : ℤ) - 2 * δ = (d₁ : ℤ) - δ by rw [hdd]; ring]
      exact hcong
    rcases D.real_odd_degree basis (ψ 1) (hψreal 1 h1mem) hdodd with h | h | h | h
    · rw [← hd] at h
      rw [h] at hcong'
      rcases hδ with rfl | rfl
      · exact hsmall _ (hc _ (-1) hcong' (by norm_num)) (by norm_num) (by norm_num)
          (by norm_num)
      · exact hsmall _ (hc _ 3 hcong' (by norm_num)) (by norm_num) (by norm_num)
          (by norm_num)
    · rw [← hd] at h
      rw [h] at hcong'
      have h2 := dvd_sub hcube hcong'
      rcases hδ with rfl | rfl
      · exact hsmall _ (hc _ 3 h2 (by push_cast; ring)) (by norm_num) (by norm_num) (by norm_num)
      · exact hsmall _ (hc _ (-1) h2 (by push_cast; ring)) (by norm_num) (by norm_num)
          (by norm_num)
    · rw [← hd] at h
      rw [h, hQZ] at hcong'
      have h2 := dvd_sub hcong' hQ
      rcases hδ with rfl | rfl
      · exact hsmall _ (hc _ 1 h2 (by ring)) (by norm_num) (by norm_num) (by norm_num)
      ·
        have hP : Nat.card P = 5 := hfive (hc _ 5 h2 (by ring))
        have hd₁ : d₁ = D.q ^ 2 - D.q + 2 := by
          have : (d₁ : ℤ) = (D.q : ℤ) ^ 2 - D.q + 2 := by
            rw [h, hQZ] at hdd
            linear_combination -hdd
          have h' : ((D.q ^ 2 - D.q + 2 : ℕ) : ℤ) = (D.q : ℤ) ^ 2 - D.q + 2 := by
            rw [Nat.cast_add, Nat.cast_sub hle, Nat.cast_pow]
            norm_num
          exact_mod_cast this.trans h'.symm
        exact D.not_dvd_card_G_Q_add_one (h5 hP) (hd₁ ▸ finrank_dvd_card basis ψ₁)
    · rw [← hd] at h
      rw [h, hqQZ] at hcong'
      have h2 := dvd_sub hqQ3 hcong'
      rcases hδ with rfl | rfl
      ·
        have hP : Nat.card P = 5 := hfive (hc _ 5 h2 (by ring))
        have hd₁ : d₁ = (D.q - 1) * (D.q ^ 2 + 1) := by
          have : (d₁ : ℤ) = ((D.q : ℤ) - 1) * ((D.q : ℤ) ^ 2 + 1) := by
            rw [h, hqQZ] at hdd
            linear_combination -hdd
          have h' : (((D.q - 1) * (D.q ^ 2 + 1) : ℕ) : ℤ) =
              ((D.q : ℤ) - 1) * ((D.q : ℤ) ^ 2 + 1) := by
            rw [Nat.cast_mul, Nat.cast_sub (by omega), Nat.cast_add, Nat.cast_pow]
            norm_num
          exact_mod_cast this.trans h'.symm
        exact D.not_dvd_card_G_sq_add_one (hd₁ ▸ finrank_dvd_card basis ψ₁)
      · exact hsmall _ (hc _ 1 h2 (by ring)) (by norm_num) (by norm_num) (by norm_num)
  ·
    rcases D.real_odd_degree basis ψ₁ hψ₁real hodd with h | h | h | h
    · exact hψ₁ne (D.eq_principal_of_real_linear basis principal hprincipal hψ₁real h)
    · rw [← hd₁] at h
      rw [h] at hcong
      have h2 := dvd_sub hcube hcong
      rcases hδ with rfl | rfl
      · exact hsmall _ (hc _ 2 h2 (by push_cast; ring)) (by norm_num) (by norm_num) (by norm_num)
      ·
        have hdq : d = D.q ^ 3 - 1 := by
          have : (d : ℤ) = (D.q : ℤ) ^ 3 - 1 := by
            rw [hdd, h]
            push_cast
            ring
          have h' : ((D.q ^ 3 - 1 : ℕ) : ℤ) = (D.q : ℤ) ^ 3 - 1 := by
            rw [Nat.cast_sub (Nat.one_le_pow _ _ D.q_pos), Nat.cast_pow, Nat.cast_one]
          exact_mod_cast this.trans h'.symm
        exact D.not_cube_sub_one_dvd_card_G (hdq ▸ finrank_dvd_card basis (ψ 1))
    · rw [← hd₁] at h
      rw [h, hQZ] at hcong
      have h2 := dvd_sub hcong hQ
      rcases hδ with rfl | rfl
      · exact hsmall _ (hc _ 2 h2 (by ring)) (by norm_num) (by norm_num) (by norm_num)
      · exact hsmall _ (hc _ 4 h2 (by ring)) (by norm_num) (by norm_num) (by norm_num)
    · rw [← hd₁] at h
      rw [h, hqQZ] at hcong
      have h2 := dvd_sub hqQ3 hcong
      rcases hδ with rfl | rfl
      · exact hsmall _ (hc _ 4 h2 (by ring)) (by norm_num) (by norm_num) (by norm_num)
      · exact hsmall _ (hc _ 2 h2 (by ring)) (by norm_num) (by norm_num) (by norm_num)

theorem ordProj_dvd_facts {r : ℕ} :
    ((r ^ (D.q + 1).factorization r : ℕ) : ℤ) ∣ (D.q : ℤ) ^ 3 + 1 ∧
      ((r ^ (D.q + 1).factorization r : ℕ) : ℤ) ∣ (D.q : ℤ) ^ 2 - D.q + 1 - 3 ∧
      ((r ^ (D.q + 1).factorization r : ℕ) : ℤ) ∣ 3 * ((D.q : ℤ) + 1) := by
  have h : ((r ^ (D.q + 1).factorization r : ℕ) : ℤ) ∣ (D.q : ℤ) + 1 := by
    have := Nat.ordProj_dvd (D.q + 1) r
    exact_mod_cast this
  refine ⟨h.trans ⟨(D.q : ℤ) ^ 2 - D.q + 1, by ring⟩, h.trans ⟨(D.q : ℤ) - 2, by ring⟩,
    dvd_mul_of_dvd_right h 3⟩

theorem prime_dvd_card_A {r : ℕ} (hr : r.Prime) (hr2 : r ≠ 2) (hr3 : r ≠ 3)
    (hdvd : r ∣ D.q + 1) : r ∣ Nat.card D.A := by
  by_contra hrA
  have : Fact r.Prime := ⟨hr⟩
  obtain ⟨P, hPeq, -, hPidx, hPcard⟩ := D.exists_sylow_index_two hr2 hr3 hdvd hrA
  have hPW : (P : Subgroup G) ≤ D.W := hPeq ▸ D.primaryPart_le_W_of_not_dvd hr2 hrA
  have hτ : ∀ x ∈ (P : Subgroup G), D.y * x * D.y⁻¹ = x⁻¹ := fun x hx => D.y_W x (hPW hx)
  have hτN : D.y ∈ Subgroup.normalizer (P : Set G) := by
    apply mem_normalizer_of_conj_mem_of_finite
    intro u hu
    rw [hτ u hu]
    exact (P : Subgroup G).inv_mem hu
  have hr5 : 5 ≤ r := by
    have := hr.two_le
    rcases hr.eq_two_or_odd' with h | h
    · exact absurd h hr2
    · obtain ⟨k, hk⟩ := h
      omega
  have hpos : 1 ≤ (D.q + 1).factorization r :=
    (hr.dvd_iff_one_le_factorization (by omega)).mp hdvd
  have hP5 : 5 ≤ Nat.card P := by
    rw [hPcard]
    exact hr5.trans (Nat.le_self_pow (by omega) r)
  obtain ⟨h1, h2, h3⟩ := D.ordProj_dvd_facts (r := r)
  rw [← hPcard] at h1 h2 h3
  refine D.false_of_inverted_sylow hr2 P (fun x hx y hy => D.W_comm x (hPW hx) y (hPW hy))
    hPidx D.y hτN hτ hP5 h1 h2 h3 fun h5 => ?_
  rw [h5] at h3
  have : (5 : ℤ) ∣ (D.q : ℤ) + 1 := by
    rw [hPcard] at h5
    have h' := Nat.ordProj_dvd (D.q + 1) r
    rw [h5] at h'
    exact_mod_cast h'
  exact_mod_cast this

end DValueData

end CFSG.Semidihedral.UnitaryDValue

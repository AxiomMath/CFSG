module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbL34Eb2
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbL34Ec
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbL34Ed
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbL34S5a
public import CFSG.GF2Type.Smith1980Orth.W4SigmaGL

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33.L34E

private lemma card_GL6 : 20158709760 = 2 ^ 15 * 3 ^ 4 * 5 * 7 ^ 2 * 31 := by norm_num

private lemma prime_dvd_GL6_six (p : ℕ) (hp : p.Prime) (hdvd : p ∣ 20158709760) :
    p = 2 ∨ p = 3 ∨ p = 5 ∨ p = 7 ∨ p = 31 := by
  rw [card_GL6] at hdvd
  rcases hp.dvd_mul.mp hdvd with h | h
  · rcases hp.dvd_mul.mp h with h | h
    · rcases hp.dvd_mul.mp h with h | h
      · rcases hp.dvd_mul.mp h with h | h
        · left
          exact (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp (hp.dvd_of_dvd_pow h)
        · right; left
          exact (Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).mp (hp.dvd_of_dvd_pow h)
      · right; right; left
        exact (Nat.prime_dvd_prime_iff_eq hp (by norm_num : Nat.Prime 5)).mp h
    · right; right; right; left
      exact (Nat.prime_dvd_prime_iff_eq hp (by norm_num : Nat.Prime 7)).mp (hp.dvd_of_dvd_pow h)
  · right; right; right; right
    exact (Nat.prime_dvd_prime_iff_eq hp (by norm_num : Nat.Prime 31)).mp h

private lemma pow_eq_49_of_dvd (p n : ℕ) (hp : p.Prime) (hp2 : p ≠ 2) (hn : 2 ≤ n)
    (hdvd : p ^ n ∣ 20158709760) (hmod : p ^ n % 3 = 1) : p ^ n = 49 := by
  have hpN : p ∣ 20158709760 := (dvd_pow_self p (by omega : n ≠ 0)).trans hdvd
  rcases prime_dvd_GL6_six p hp hpN with rfl | rfl | rfl | rfl | rfl
  · exact absurd rfl hp2
  · have h0 : 3 ^ n % 3 = 0 :=
      Nat.dvd_iff_mod_eq_zero.mp (dvd_pow_self 3 (by omega : n ≠ 0))
    exact absurd (h0.symm.trans hmod) (by norm_num)
  · have h25 : 25 ∣ 20158709760 := (pow_dvd_pow 5 hn).trans hdvd
    exact absurd h25 (by norm_num)
  · have hn_le : n ≤ 2 := by
      by_contra hcon
      have h3 : 3 ≤ n := by omega
      have h343 : 7 ^ 3 ∣ 20158709760 := (pow_dvd_pow 7 h3).trans hdvd
      exact absurd h343 (by norm_num)
    have hn_eq : n = 2 := by omega
    rw [hn_eq]; norm_num
  · have h961 : 31 ^ 2 ∣ 20158709760 := (pow_dvd_pow 31 hn).trans hdvd
    exact absurd h961 (by norm_num)

variable {Λ : Type} [Group Λ] [Finite Λ] {E : Type*} [AddCommGroup E] [Module (ZMod 2) E]
  [Module.Finite (ZMod 2) E] {ι : Λ →* (E ≃ₗ[ZMod 2] E)} {P W : Subgroup Λ} {r s : Λ}

theorem eq_bot_of_odd_normal_pgroup {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) (h : Crit ι P W r s)
    (R : Subgroup Λ) (hRP : R ≤ P) [R.Normal] (hRp : IsPGroup p R) {a : Λ} (ha2 : a * a = 1)
    (ha1 : a ≠ 1) (hcomm : ∀ x ∈ R, a * x = x * a) : R = ⊥ := by
  have hp : p.Prime := Fact.out
  have hr3 : r * r * r = 1 := by rw [← h.r_cube, pow_succ, pow_two]
  have hfixR : ∀ x ∈ R, r * x * r⁻¹ = x → x = 1 := fun x hx => h.fpf x (hRP hx)
  have hmodR : Nat.card R ≡ 1 [MOD 3] :=
    CFSG.OddStandard.SmallF3.HarrisU33.L34Z.card_modEq_one_of_conj_fpf R r hr3
      (fun b hb => (inferInstance : R.Normal).conj_mem b hb r)
      (fun b hb hbc => h.fpf b (hRP hb) (by rw [hbc, mul_assoc, mul_inv_cancel, mul_one]))
  by_cases hcyc : IsCyclic R
  ·
    haveI : IsCyclic R := hcyc
    exact eq_bot_of_normal_cyclic R r s h.r_cube h.s_conj hfixR
  ·
    obtain ⟨n, hn_card⟩ := (IsPGroup.iff_card (p := p) (G := ↥R)).mp hRp
    have hn2 : 2 ≤ n := by
      rcases Nat.lt_or_ge n 2 with hn | hn
      · interval_cases n
        · have hdiv : Nat.card ↥R ∣ p := by rw [hn_card, pow_zero]; exact one_dvd p
          exfalso; exact hcyc (isCyclic_of_card_dvd_prime hdiv)
        · have hp1 : Nat.card ↥R = p := by rw [hn_card, pow_one]
          exfalso; exact hcyc (isCyclic_of_prime_card hp1)
      · exact hn
    have hdvd_GL : Nat.card ↥R ∣ 20158709760 := by
      have hmap : Nat.card ↥(R.map ι) ∣ Nat.card (E ≃ₗ[ZMod 2] E) :=
        Subgroup.card_subgroup_dvd_card (R.map ι)
      rwa [Subgroup.card_map_of_injective (K := R) (f := ι) h.inj,
        CFSG.GF2Type.Smith1980Orth.W4Sigma.card_linearEquiv_of_finrank_eq_six h.dim] at hmap
    have hdvd_pn : p ^ n ∣ 20158709760 := by rwa [hn_card] at hdvd_GL
    have hmodR' : Nat.card ↥R % 3 = 1 := by
      have hh := hmodR
      change Nat.card ↥R % 3 = 1 % 3 at hh
      norm_num at hh
      exact hh
    have hmod_pn : p ^ n % 3 = 1 := by rwa [hn_card] at hmodR'
    have hp49 : p ^ n = 49 := pow_eq_49_of_dvd p n hp hp2 hn2 hdvd_pn hmod_pn
    have hm : Nat.card ↥R = 49 := by rw [hn_card, hp49]
    have hord_sub : ∀ g : ↥R, g ≠ 1 → orderOf g = 7 := by
      intro g hg1
      have hdvd : orderOf g ∣ 49 := by rw [← hm]; exact orderOf_dvd_natCard g
      obtain ⟨k, hk_le, hk_eq⟩ :=
        (Nat.dvd_prime_pow (p := 7) (m := 2) Nat.prime_seven).mp hdvd
      interval_cases k
      · have h1 : orderOf g = 1 := by rw [hk_eq]; norm_num
        exact absurd (orderOf_eq_one_iff.mp h1) hg1
      · exact by rw [hk_eq]; norm_num
      · have h49 : orderOf g = 49 := by rw [hk_eq]; norm_num
        exfalso; exact hcyc (isCyclic_of_orderOf_eq_card g (by rw [hm]; exact h49))
    exfalso
    refine false_of_involution_commutes_seven_sq (a := ι a) h.dim (R.map ι) ?_ ?_ ?_ ?_ ?_
    · rw [Subgroup.card_map_of_injective (K := R) (f := ι) h.inj, hm]
    · intro g hg hg1
      rcases hg with ⟨x, hx, rfl⟩
      have hx1 : (⟨x, hx⟩ : ↥R) ≠ 1 := by
        intro hh
        have hxeq : x = 1 := congrArg Subtype.val hh
        exact hg1 (by rw [hxeq, map_one])
      calc orderOf (ι x) = orderOf (⟨x, hx⟩ : ↥R) := by
            rw [orderOf_injective ι h.inj x]
            exact orderOf_injective R.subtype R.subtype_injective ⟨x, hx⟩
        _ = 7 := hord_sub ⟨x, hx⟩ hx1
    · simpa only [map_mul, map_one] using congrArg ι ha2
    · intro hh
      exact ha1 (h.inj (by rw [hh, map_one]))
    · intro g hg
      rcases hg with ⟨x, hx, rfl⟩
      simpa only [map_mul] using congrArg ι (hcomm x hx)

end CFSG.OddStandard.SmallF3.HarrisU33.L34E

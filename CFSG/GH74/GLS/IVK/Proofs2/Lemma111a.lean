module

public import CFSG.RankThree.FFModules.RepMulAut
public import CFSG.LinearAlgebra.SL2MinimalFaithful
public import CFSG.LinearAlgebra.SL2MinimalFaithfulMatrix
public import CFSG.GH74.GLS.IVK.Defs

public section

namespace CFSG.GH74.GLS.IVK.Proofs2

open Subgroup CFSG CFSG.GH74.GLS CFSG.GH74.GLS.IVK CFSG.Assembly.LowTwoRank

namespace Lemma111a

section Weak

variable {J V : Type*} [Group J] [Group V]

theorem two_mul_le_of_injective_weak [Finite J] [Finite V] {p f d : ℕ} (hp : p.Prime) (hf : 1 ≤ f)
    (hJ1 : f = 1 → p ∣ Nat.card J)
    (hZ : 2 ≤ f → ∃ ℓ : ℕ, ℓ.Prime ∧ ℓ ∣ Nat.card J ∧ ℓ ∣ p ^ (2 * f) - 1 ∧
      ∀ k : ℕ, 0 < k → k < 2 * f → ¬ ℓ ∣ p ^ k - 1)
    (ρ : J →* MulAut V) (hρ : Function.Injective ρ) (hV : Nat.card V = p ^ d) :
    2 * f ≤ d := by
  by_contra hd
  push Not at hd
  have hne : ∀ {h : J}, orderOf h ≠ 1 → ρ h ≠ 1 := by
    intro h hh h1
    apply hh
    rw [show h = 1 from hρ (by rw [h1, map_one]), orderOf_one]
  rcases Nat.lt_or_ge f 2 with hf1 | hf2
  · obtain rfl : f = 1 := by omega
    have : Fact p.Prime := ⟨hp⟩
    obtain ⟨h, hh⟩ := exists_prime_orderOf_dvd_card' p (hJ1 rfl)
    obtain ⟨e, hed, hdvd⟩ := CFSG.SL2MinimalFaithful.exists_dvd_pow_sub_pow hp hp ρ hh
      (hne (by rw [hh]; exact hp.one_lt.ne')) hV
    obtain rfl : d = 1 := by omega
    obtain rfl : e = 0 := by omega
    rw [pow_one, pow_zero] at hdvd
    have h2 := hp.two_le
    have := Nat.le_of_dvd (by omega) hdvd
    omega
  · obtain ⟨ℓ, hℓ, hℓJ, hℓdvd, hprim⟩ := hZ hf2
    have : Fact ℓ.Prime := ⟨hℓ⟩
    obtain ⟨h, hh⟩ := exists_prime_orderOf_dvd_card' ℓ hℓJ
    obtain ⟨e, hed, hdvd⟩ := CFSG.SL2MinimalFaithful.exists_dvd_pow_sub_pow hp hℓ ρ hh
      (hne (by rw [hh]; exact hℓ.one_lt.ne')) hV
    have hfac : p ^ d - p ^ e = p ^ e * (p ^ (d - e) - 1) := by
      rw [Nat.mul_sub_one, ← pow_add, Nat.add_sub_cancel' hed.le]
    rw [hfac] at hdvd
    have hℓp : ¬ ℓ ∣ p ^ e := by
      intro h'
      have hℓp' : ℓ = p := (Nat.prime_dvd_prime_iff_eq hℓ hp).mp (hℓ.dvd_of_dvd_pow h')
      subst hℓp'
      have h1 : ℓ ∣ ℓ ^ (2 * f) := dvd_pow_self ℓ (by omega)
      have h2 : 1 ≤ ℓ ^ (2 * f) := Nat.one_le_pow _ _ hℓ.pos
      have h3 := Nat.dvd_sub h1 hℓdvd
      rw [Nat.sub_sub_self h2] at h3
      exact hℓ.one_lt.ne' (Nat.dvd_one.mp h3)
    exact hprim (d - e) (by omega) (by omega)
      ((Nat.Coprime.dvd_of_dvd_mul_left ((Nat.Prime.coprime_iff_not_dvd hℓ).mpr hℓp) hdvd))

end Weak

theorem exists_mulAut_hom {H : Type} [Group H] {V : Type} [AddCommGroup V] {k : Type} [CommRing k]
    [Module k V] (ρ : Representation k H V) (hρ : Function.Injective ρ) :
    ∃ φ : H →* MulAut (Multiplicative V), Function.Injective φ :=
  ⟨CFSG.RankThree.FFModules.repMulAut ρ, CFSG.RankThree.FFModules.repMulAut_injective hρ⟩

end Lemma111a

open Lemma111a in
theorem ivk_11_1a :
    ∀ (p n : ℕ), p.Prime → p ≠ 2 → ∀ (H : Type) [Group H] [Finite H] (K : Subgroup H) [K.Normal],
      (HasSL2Model ↥K (fun r => r = p ^ n) ∨ IsL2 ↥K (fun r => r = p ^ n)) →
        ∀ (V : Type) [AddCommGroup V] [Module (ZMod p) V] [Module.Finite (ZMod p) V]
          (ρ : Representation (ZMod p) H V), Function.Injective ρ →
            2 * n ≤ Module.finrank (ZMod p) V := by
  intro p n hp hp2 H _ _ K _ hK V _ _ _ ρ hρ
  have : Fact p.Prime := ⟨hp⟩
  have : NeZero p := ⟨hp.ne_zero⟩
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  obtain ⟨φ, hφ⟩ := exists_mulAut_hom ρ hρ
  have hφK : Function.Injective (φ.comp K.subtype) := hφ.comp K.subtype_injective
  have : Finite V := Module.finite_of_finite (ZMod p)
  have hV : Nat.card (Multiplicative V) = p ^ Module.finrank (ZMod p) V := by
    have : Fintype V := Fintype.ofFinite V
    have h1 := Module.card_eq_pow_finrank (K := ZMod p) (V := V)
    rw [ZMod.card] at h1
    rw [Nat.card_congr (Multiplicative.toAdd : Multiplicative V ≃ V), Nat.card_eq_fintype_card]
    exact h1
  have hp3 : 3 ≤ p := by
    have := hp.two_le
    omega
  have hpodd : Odd p := hp.odd_of_ne_two hp2
  have hKcard : ∃ c : ℕ, (c = 1 ∨ c = 2) ∧ Nat.card ↥K * c = p ^ n * ((p ^ n) ^ 2 - 1) := by
    rcases hK with ⟨F₀, _, _, hF, ⟨e⟩⟩ | ⟨F₀, _, _, hF, ⟨e⟩⟩
    · replace hF : Nat.card F₀ = p ^ n := hF
      refine ⟨1, Or.inl rfl, ?_⟩
      rw [mul_one, Nat.card_congr e.toEquiv,
        ← Nat.card_congr (specialLinearGroupEquivStatedSL 2 F₀).toEquiv,
        CFSG.SL2MinimalFaithful.card_specialLinearGroup_fin_two F₀, hF]
    · replace hF : Nat.card F₀ = p ^ n := hF
      refine ⟨2, Or.inr rfl, ?_⟩
      have hodd : CFSG.GorensteinWalter.IsOddPrimePower (Nat.card F₀) := ⟨p, n, hp, hpodd, hn, hF⟩
      have h1 := CFSG.GorensteinWalter.psl2_card_formula F₀ hodd
      rw [Nat.card_congr e.toEquiv,
        ← Nat.card_congr (projectiveSpecialLinearGroupEquivStatedProj 2 F₀).toEquiv, h1, hF]
      have h2 : 2 ∣ p ^ n * ((p ^ n) ^ 2 - 1) := by
        have hq : Odd (p ^ n) := hpodd.pow
        obtain ⟨m, hm⟩ := hq
        have h3 : (p ^ n) ^ 2 - 1 = 2 * (m * (m + 1) * 2) := by
          rw [hm]
          have : (2 * m + 1) ^ 2 = 4 * (m * (m + 1)) + 1 := by ring
          rw [this, Nat.add_sub_cancel]
          ring
        rw [h3]
        exact Dvd.dvd.mul_left (dvd_mul_right 2 _) _
      exact Nat.div_mul_cancel h2
  obtain ⟨c, hc, hKc⟩ := hKcard
  have hnotc : ∀ ℓ : ℕ, ℓ.Prime → ℓ ∣ c → ℓ = 2 := by
    intro ℓ hℓ hℓc
    rcases hc with rfl | rfl
    · exact absurd (Nat.dvd_one.mp hℓc) hℓ.ne_one
    · exact (Nat.prime_dvd_prime_iff_eq hℓ Nat.prime_two).mp hℓc
  have hdvdK : ∀ ℓ : ℕ, ℓ.Prime → ℓ ≠ 2 → ℓ ∣ p ^ n * ((p ^ n) ^ 2 - 1) → ℓ ∣ Nat.card ↥K := by
    intro ℓ hℓ hℓ2 hℓd
    rw [← hKc] at hℓd
    rcases (Nat.Prime.dvd_mul hℓ).mp hℓd with h | h
    · exact h
    · exact absurd (hnotc ℓ hℓ h) hℓ2
  have key := two_mul_le_of_injective_weak (J := ↥K) (V := Multiplicative V) hp hn
    (fun hn1 => by
      subst hn1
      exact hdvdK p hp hp2 (Dvd.dvd.mul_right (dvd_pow_self p one_ne_zero) _))
    (fun hn2 => by
      obtain ⟨ℓ, hℓ, hℓd, hprim⟩ := CFSG.SL2MinimalFaithful.exists_primitive_prime_dvd_pow_sub_one
        (a := p) (n := 2 * n) hp3 (by omega)
      have hℓ2 : ℓ ≠ 2 := by
        rintro rfl
        apply hprim 1 (by norm_num) (by omega)
        rw [pow_one]
        obtain ⟨m, hm⟩ := hpodd
        rw [hm, Nat.add_sub_cancel]
        exact dvd_mul_right 2 m
      refine ⟨ℓ, hℓ, hdvdK ℓ hℓ hℓ2 ?_, hℓd, hprim⟩
      refine Dvd.dvd.mul_left ?_ _
      rwa [pow_mul'] at hℓd)
    (φ.comp K.subtype) hφK hV
  exact key

end CFSG.GH74.GLS.IVK.Proofs2

module

public import CFSG.GH74.E2.Shapes
public import CFSG.GH74.KGroups.TwoM12Check
public import CFSG.LocalAnalysis.ComponentClassification.M12CoverExternalOuter

public section

namespace CFSG.GH74.KGroups.TwoM12

open Subgroup CFSG.Blueprint CFSG.ComponentClassification CFSG.ComponentClassification.M12Cover
open CFSG.ComponentClassification.OuterAutomorphisms
open CFSG.GH74.E2 (Shape2M12)

variable {K : Type} [Group K]

noncomputable def quotEquiv (h : Shape2M12 K) : K ⧸ center K ≃* NativeSporadic.M12 :=
  Classical.choice h.2.2

noncomputable def autEmb (h : Shape2M12 K) : MulAut K →* MulAut NativeSporadic.M12 :=
  (MulAut.congr (quotEquiv h)).toMonoidHom.comp (PerfectAutomorphisms.centerQuotientHom K)

theorem autEmb_injective (h : Shape2M12 K) : Function.Injective (autEmb h) := by
  have : Group.IsPerfect K := h.1.1
  exact (MulAut.congr (quotEquiv h)).injective.comp
    (PerfectAutomorphisms.centerQuotientHom_injective K)

theorem card_mulAut_dvd
    (h : Shape2M12 K) : Nat.card (MulAut K) ∣ 190080 := by
  have := Subgroup.card_dvd_of_injective (autEmb h) (autEmb_injective h)
  rwa [card_mulAut] at this

theorem autRank_ge5_of_shape2M12
    [Finite K] (h : Shape2M12 K) (p : ℕ) (hp : p.Prime) (h5 : 5 ≤ p)
    (B : Subgroup (MulAut K)) (hB : CFSG.GH74.E2.ElemAb p B) : Nat.card B ≤ p := by
  have : Fact p.Prime := ⟨hp⟩
  have hnd : ¬ p ^ (1 + 1) ∣ Nat.card (MulAut K) := by
    intro hd
    have hd' : p ^ 2 ∣ 190080 := (hd.trans (card_mulAut_dvd h))
    have hpd : p ∣ 190080 := (dvd_pow_self p two_ne_zero).trans hd'
    have h190 : (190080 : ℕ) = 2 ^ 7 * 3 ^ 3 * 5 * 11 := by norm_num
    rw [h190] at hpd
    have hp2 : ¬ p ∣ 2 := fun h2 => by
      have := Nat.le_of_dvd (by norm_num) h2
      omega
    have hp3 : ¬ p ∣ 3 := fun h3 => by
      have := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).1 h3
      omega
    rcases (Nat.Prime.dvd_mul hp).1 hpd with h1 | h11
    · rcases (Nat.Prime.dvd_mul hp).1 h1 with h2 | h5
      · rcases (Nat.Prime.dvd_mul hp).1 h2 with h2 | h3
        · exact hp2 (hp.dvd_of_dvd_pow h2)
        · exact hp3 (hp.dvd_of_dvd_pow h3)
      · have := (Nat.prime_dvd_prime_iff_eq hp (by norm_num : Nat.Prime 5)).1 h5
        subst this
        exact absurd hd' (by norm_num)
    · have := (Nat.prime_dvd_prime_iff_eq hp (by norm_num : Nat.Prime 11)).1 h11
      subst this
      exact absurd hd' (by norm_num)
  have := elemAb_card_le p B hB 1 hnd
  simpa using this

theorem not_nine_dvd_card_centralizer
    (τ : MulAut NativeSporadic.M12) (h2 : τ ^ 2 = 1)
    (h1 : τ ≠ 1) : ¬ 9 ∣ Nat.card (centralizer ({τ} : Set (MulAut NativeSporadic.M12))) := by
  have hord : orderOf τ = 2 := orderOf_eq_prime h2 h1
  by_cases hin : τ ∈ inner NativeSporadic.M12
  · obtain ⟨g, rfl⟩ := hin
    have hg2 : g ^ 2 = 1 := by
      apply M12Cover.conj_injective
      rw [map_pow, h2, map_one]
    have hg1 : g ≠ 1 := fun h => h1 (by rw [h, map_one])
    have hgord : orderOf g = 2 := orderOf_eq_prime hg2 hg1
    obtain ⟨c, hc | hc⟩ := m12_involution_conj_a0_a1 g hgord
    · rw [hc, map_mul, map_mul, map_inv, card_centralizer_conj_eq, card_centralizer_conj_elemA0]
      decide
    · rw [hc, map_mul, map_mul, map_inv, card_centralizer_conj_eq, card_centralizer_conj_elemA1]
      decide
  · obtain ⟨g, hg⟩ := exists_conj_beta_of_outer hord hin
    rw [hg, card_centralizer_conj_eq, card_centralizer_beta]
    decide

theorem autCentralizer_of_shape2M12
    (h : Shape2M12 K) (R : Subgroup (MulAut K))
    (hcard : Nat.card R = 9) (ψ : MulAut K) (hψ : ψ ^ 2 = 1)
    (hc : ∀ r ∈ R, ψ * r = r * ψ) : ψ = 1 := by
  by_contra hne
  have hΘ := autEmb_injective h
  have hτ2 : autEmb h ψ ^ 2 = 1 := by rw [← map_pow, hψ, map_one]
  have hτ1 : autEmb h ψ ≠ 1 := fun h1 => hne (hΘ (by rw [h1, map_one]))
  have hle : R.map (autEmb h) ≤ centralizer ({autEmb h ψ} : Set (MulAut NativeSporadic.M12)) := by
    rintro _ ⟨r, hr, rfl⟩
    rw [Subgroup.mem_centralizer_singleton_iff, ← map_mul, ← map_mul, hc r hr]
  have h9 : 9 ∣ Nat.card (centralizer ({autEmb h ψ} : Set (MulAut NativeSporadic.M12))) := by
    have := Subgroup.card_dvd_of_le hle
    rwa [Subgroup.card_map_of_injective hΘ, hcard] at this
  exact not_nine_dvd_card_centralizer _ hτ2 hτ1 h9

end CFSG.GH74.KGroups.TwoM12

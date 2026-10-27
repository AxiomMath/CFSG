module

public import CFSG.LargeExtraspecial.AS35WList
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87FL5Block
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87FU5
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87FU3Card

public section

namespace CFSG.LargeExtraspecial

open Subgroup CFSG.Blueprint

namespace AS35W

theorem not_cube_dvd {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hf : 1 ≤ f) :
    ¬ (p ^ f) ^ 3 ∣ 2 ^ 8 * 3 ^ 2 * 5 := by
  intro h
  have h1 : p ^ 3 ∣ 2 ^ 8 * 3 ^ 2 * 5 := by
    refine (pow_dvd_pow_of_dvd ?_ 3).trans h
    exact dvd_pow_self p (by omega)
  have h2 : p ^ 3 ≤ 2 ^ 8 * 3 ^ 2 * 5 := Nat.le_of_dvd (by norm_num) h1
  have h3 : p ≤ 22 := by
    by_contra hc
    push Not at hc
    have : 23 ^ 3 ≤ p ^ 3 := Nat.pow_le_pow_left hc 3
    omega
  interval_cases p <;> revert hp hp2 h1 <;> decide

theorem eq_three_of_sq_dvd {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hf : 1 ≤ f)
    (h : (p ^ f) ^ 2 ∣ 2 ^ 8 * 3 ^ 2 * 5) : p ^ f = 3 := by
  have h1 : p ^ 2 ∣ 2 ^ 8 * 3 ^ 2 * 5 :=
    (pow_dvd_pow_of_dvd (dvd_pow_self p (by omega)) 2).trans h
  have hp3 : p = 3 := by
    have h2 : p ∣ 2 ^ 8 * 3 ^ 2 * 5 := (dvd_pow_self p two_ne_zero).trans h1
    have h3 : p ∣ 2 ∨ p ∣ 3 ∨ p ∣ 5 := by
      rcases (Nat.Prime.dvd_mul hp).1 h2 with h4 | h4
      · rcases (Nat.Prime.dvd_mul hp).1 h4 with h5 | h5
        · exact Or.inl (hp.dvd_of_dvd_pow h5)
        · exact Or.inr (Or.inl (hp.dvd_of_dvd_pow h5))
      · exact Or.inr (Or.inr h4)
    rcases h3 with h3 | h3 | h3
    · exact absurd ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 h3) hp2
    · exact (Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).1 h3
    · have := (Nat.prime_dvd_prime_iff_eq hp (by norm_num : Nat.Prime 5)).1 h3
      subst this
      exact absurd h1 (by norm_num)
  subst hp3
  rcases Nat.lt_or_ge f 2 with hf2 | hf2
  · obtain rfl : f = 1 := by omega
    rfl
  · exfalso
    have : 3 ^ 4 ∣ (3 ^ f) ^ 2 := by
      rw [← pow_mul]
      exact pow_dvd_pow 3 (by omega)
    have := this.trans h
    norm_num at this

theorem W2Data.card_dvd_of_le {X : Type} [Group X] {z : X} (hz : W2Data X z) {H : Subgroup X}
    (hH : H ≤ centralizer ({z} : Set X)) : Nat.card H ∣ 2 ^ 8 * 3 ^ 2 * 5 :=
  (Subgroup.card_dvd_of_le hH).trans hz.card_dvd

theorem ne_two_of_mod_four {p f : ℕ} (hf : 1 ≤ f) (h : p ^ f % 4 = 3 ∨ p ^ f % 4 = 1) :
    p ≠ 2 := by
  rintro rfl
  obtain ⟨g, rfl⟩ : ∃ g, f = g + 1 := ⟨f - 1, by omega⟩
  rcases g with _ | g
  · simp at h
  · have : 2 ^ (g + 1 + 1) = 4 * 2 ^ g := by ring
    rw [this] at h
    omega

open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
  CFSG.GH74.GLS.Stage2.Signalizer in
theorem l5W2Input : L5W2Input := by
  intro X _ _ p f hp hf hq h z hz
  exfalso
  have hp2 : p ≠ 2 := ne_two_of_mod_four hf (Or.inl hq)
  obtain ⟨K, _, _, hK, ⟨e⟩⟩ := LinearCover.exists_mulEquiv_projectiveSL_of_lieModel h
  have hz' := hz.map e
  obtain ⟨g, hg⟩ := proj_surjective 5 K (e z)
  rw [← hg] at hz'
  have : Fintype K := Fintype.ofFinite K
  have hchar : ringChar K ≠ 2 := by
    rw [Ne, FiniteField.even_card_iff_char_two, ← Nat.card_eq_fintype_card, hK]
    have : Odd (p ^ f) := (hp.odd_of_ne_two hp2).pow
    obtain ⟨k, hk⟩ := this
    omega
  have hz2 : proj 5 K g ^ 2 = 1 := by rw [← hz'.orderOf_eq, pow_orderOf_eq_one]
  have hB : conjAut (3 + 2) K (Matrix.SpecialLinearGroup.toGL g) ^ 2 = 1 := by
    change conjAut 5 K (Matrix.SpecialLinearGroup.toGL g) ^ 2 = 1
    rw [conjAut_toGL, ← map_pow, hz2, map_one]
  obtain ⟨ρ, hρ, hfix⟩ := Odd87.exists_fixed_sl3_block hchar _ hB
  have hle : ρ.range ≤ centralizer ({proj 5 K g} : Set (projectiveSL 5 K)) := by
    rintro _ ⟨s, rfl⟩
    rw [mem_centralizer_singleton_iff]
    have h1 := hfix s
    change conjAut 5 K (Matrix.SpecialLinearGroup.toGL g) (ρ s) = ρ s at h1
    rw [conjAut_toGL, MulAut.conj_apply] at h1
    calc ρ s * proj 5 K g = proj 5 K g * ρ s * (proj 5 K g)⁻¹ * proj 5 K g := by rw [h1]
      _ = proj 5 K g * ρ s := by group
  have hdvd := hz'.card_dvd_of_le hle
  rw [← Nat.card_congr (MonoidHom.ofInjective hρ).toEquiv] at hdvd
  have h3 : (p ^ f) ^ 3 ∣ Nat.card (Matrix.SpecialLinearGroup (Fin 3) K) := by
    rw [card_SL_eq (by norm_num), hK]
    exact Dvd.intro _ rfl
  exact not_cube_dvd hp hp2 hf (h3.trans hdvd)

open CFSG.GH74.GLS.Stage2.Signalizer CFSG.ClassicalGroups.UnitaryFlag in
theorem u5W2Input : U5W2Input := by
  intro X _ _ p f hp hf hq h z hz
  exfalso
  have hp2 : p ≠ 2 := ne_two_of_mod_four hf (Or.inr hq)
  obtain ⟨K, _, _, hdat, -, ⟨e⟩⟩ := Odd87.exists_unitaryData_equiv hp hf h
  have hz' := hz.map e
  have hz2 : e z ^ 2 = 1 := by
    have := pow_orderOf_eq_one (e z)
    rwa [hz'.orderOf_eq] at this
  have hα : (MulAut.conj (e z)) ^ 2 = 1 := by rw [← map_pow, hz2, map_one]
  rcases Odd87.unitary5_involution_cases hdat hp2 _ hα with ⟨ψ, hψ, hfix⟩ | ⟨hni, -⟩
  · have hle : ((hypProj hdat 2 1).comp ψ).range ≤
        centralizer ({e z} : Set _) := by
      intro s hs
      rw [mem_centralizer_singleton_iff]
      have h1 := hfix s hs
      rw [MulAut.conj_apply] at h1
      calc s * e z = e z * s * (e z)⁻¹ * e z := by rw [h1]
        _ = e z * s := by group
    have hdvd := hz'.card_dvd_of_le hle
    rw [← Nat.card_congr (MonoidHom.ofInjective hψ).toEquiv] at hdvd
    have h3 : (p ^ f) ^ 3 ∣ Nat.card ↥(unitarySU p f K 3) := by
      rw [Odd87.card_unitarySU_three hdat, mul_assoc]
      exact Dvd.intro _ rfl
    exact not_cube_dvd hp hp2 hf (h3.trans hdvd)
  · exact hni (e z) rfl

end AS35W

end CFSG.LargeExtraspecial

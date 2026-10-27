module

public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87CF67SBasic
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87L34Cls3
public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67RedAut
public import CFSG.LocalAnalysis.ComponentClassification.PSL3FourL34Check
public import Certificates.Certificate5185

public section

namespace CFSG.GH74.GLS.Stage2.Bender.Thm1.CF67S

open Subgroup CFSG CFSG.ComponentClassification.PSL3Four CFSG.PSL3Four.Native
  CFSG.ComponentClassification.OuterAutomorphisms

theorem l34_ord_check
    {x : Equiv.Perm (Fin 42)} (hx : x ∈ S) :
    (x ^ 15 = 1 → x ^ 3 = 1 ∨ x ^ 5 = 1) ∧ (x ^ 21 = 1 → x ^ 3 = 1 ∨ x ^ 7 = 1) := by
  have h : l34OrdCheck enumS.tabs = true := Certificates.certificate5185
  unfold l34OrdCheck at h
  rw [allBelow_eq_true] at h
  obtain ⟨k, hk, hrep⟩ := enumerates_S.exists_pos hx
  have hc := h k hk
  simp only [Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true'] at hc
  obtain ⟨c1, c2⟩ := hc
  have hpow : ∀ n : ℕ, ∀ y : Equiv.Perm (Fin 42), (powTab 42 enumS.tabs[k]! n == idTab 42) = true ↔ x ^ n = 1 := by
    intro n y
    exact (TabRep.pow hrep n).beq_iff TabRep.idTab
  refine ⟨fun h15 => ?_, fun h21 => ?_⟩
  · rcases c1 with (c | c) | c
    · exact absurd ((hpow 15 x).mpr h15) (by simpa using c)
    · exact Or.inl ((hpow 3 x).mp c)
    · exact Or.inr ((hpow 5 x).mp c)
  · rcases c2 with (c | c) | c
    · exact absurd ((hpow 21 x).mpr h21) (by simpa using c)
    · exact Or.inl ((hpow 3 x).mp c)
    · exact Or.inr ((hpow 7 x).mp c)

theorem S_no_comm
    {g h : Equiv.Perm (Fin 42)} (hg : g ∈ S) (hh : h ∈ S) (hgh : g * h = h * g) {s : ℕ}
    (hs : s = 5 ∨ s = 7) (hg3 : g ^ 3 = 1) (hg1 : g ≠ 1) (hhs : h ^ s = 1) (hh1 : h ≠ 1) :
    False := by
  have hcomm : Commute g h := hgh
  have hx : g * h ∈ S := S.mul_mem hg hh
  obtain ⟨c15, c21⟩ := l34_ord_check hx
  have hgp : ∀ n : ℕ, g ^ (3 * n) = 1 := fun n => by rw [pow_mul, hg3, one_pow]
  have hhp : ∀ n : ℕ, h ^ (s * n) = 1 := fun n => by rw [pow_mul, hhs, one_pow]
  rcases hs with rfl | rfl
  · have h15 : (g * h) ^ 15 = 1 := by
      rw [hcomm.mul_pow, show (15 : ℕ) = 3 * 5 by norm_num, hgp 5, show 3 * 5 = 5 * 3 by norm_num, hhp 3, one_mul]
    rcases c15 h15 with h3 | h5
    · rw [hcomm.mul_pow, hg3, one_mul] at h3
      have := pow_gcd_eq_one.mpr (⟨h3, hhs⟩ : h ^ 3 = 1 ∧ h ^ 5 = 1)
      exact hh1 (by simpa using this)
    · rw [hcomm.mul_pow, hhs, mul_one] at h5
      have h5' : g ^ 5 = g ^ 2 := by
        rw [show (5 : ℕ) = 3 + 2 by norm_num, pow_add, hg3, one_mul]
      have := pow_gcd_eq_one.mpr (⟨h5' ▸ h5, hg3⟩ : g ^ 2 = 1 ∧ g ^ 3 = 1)
      exact hg1 (by simpa using this)
  · have h21 : (g * h) ^ 21 = 1 := by
      rw [hcomm.mul_pow, show (21 : ℕ) = 3 * 7 by norm_num, hgp 7, show 3 * 7 = 7 * 3 by norm_num, hhp 3, one_mul]
    rcases c21 h21 with h3 | h7
    · rw [hcomm.mul_pow, hg3, one_mul] at h3
      have := pow_gcd_eq_one.mpr (⟨h3, hhs⟩ : h ^ 3 = 1 ∧ h ^ 7 = 1)
      exact hh1 (by simpa using this)
    · rw [hcomm.mul_pow, hhs, mul_one] at h7
      have h7' : g ^ 7 = g := by
        rw [show (7 : ℕ) = 3 * 2 + 1 by norm_num, pow_succ, pow_mul, hg3, one_pow, one_mul]
      exact hg1 (h7' ▸ h7)

theorem center_S_eq_bot : Subgroup.center ↥S = ⊥ := by
  rw [eq_bot_iff]
  intro z hz
  have h1 : conjAutS (⟨(z : Equiv.Perm (Fin 42)), S_le_R z.2⟩ : ↥R) = 1 := by
    refine MulEquiv.ext fun t => Subtype.ext ?_
    rw [conjAutS_apply]
    have := Subgroup.mem_center_iff.mp hz t
    have h2 : (t : Equiv.Perm (Fin 42)) * z = z * t := congrArg Subtype.val this
    show _ = (t : Equiv.Perm (Fin 42))
    calc (z : Equiv.Perm (Fin 42)) * t * (z : Equiv.Perm (Fin 42))⁻¹
        = ((z : Equiv.Perm (Fin 42)) * t) * (z : Equiv.Perm (Fin 42))⁻¹ := rfl
      _ = (t * z) * (z : Equiv.Perm (Fin 42))⁻¹ := by rw [h2]
      _ = t := by group
  have h2 : (⟨(z : Equiv.Perm (Fin 42)), S_le_R z.2⟩ : ↥R) = 1 := conjAutS_injective (by rw [h1, map_one])
  have h3 : (z : Equiv.Perm (Fin 42)) = 1 := congrArg Subtype.val h2
  exact Subgroup.mem_bot.mpr (Subtype.ext h3)

theorem noN2_model : NoN2 ↥S := by
  classical
  intro r V Z h
  have hc := center_S_eq_bot
  have hinj := conj_injective_of_center_bot hc
  have hA : Nat.card (MulAut ↥S) = 241920 := by
    rw [← Nat.card_congr (CFSG.GH74.GLS.Stage2.Signalizer.Odd87.Cls3.conjIso).toEquiv, card_R]
  have hO : Nat.card (Outer ↥S) = 12 := by
    have := card_mulAut_eq_outer_mul hc
    rw [hA, card_S] at this
    omega
  have hsq := n2_sq_dvd h
  rw [hA] at hsq
  obtain ⟨s, y, hs, hsodd, hsr, hys, hy1, -, hVy⟩ := n2_exists_prime_elt h
  obtain ⟨hr, hr2, hVe, hVc, -⟩ := h
  have : Fact s.Prime := ⟨hs⟩
  have hfac : (241920 : ℕ) = 2 ^ 8 * 3 ^ 3 * 5 * 7 := by norm_num
  have hr3 : r = 3 := by
    have h1 : r ∣ 2 ^ 8 * 3 ^ 3 * 5 * 7 := by
      have : r ∣ r ^ 2 := dvd_pow_self r two_ne_zero
      exact hfac ▸ this.trans hsq
    rcases (Nat.Prime.dvd_mul hr).mp h1 with h2 | h2
    · rcases (Nat.Prime.dvd_mul hr).mp h2 with h3 | h3
      · rcases (Nat.Prime.dvd_mul hr).mp h3 with h4 | h4
        · have := (Nat.prime_dvd_prime_iff_eq hr Nat.prime_two).mp (hr.dvd_of_dvd_pow h4)
          subst this
          exact absurd hr2 (by decide)
        · exact (Nat.prime_dvd_prime_iff_eq hr Nat.prime_three).mp (hr.dvd_of_dvd_pow h4)
      · have := (Nat.prime_dvd_prime_iff_eq hr Nat.prime_five).mp h3
        subst this
        omega
    · have := (Nat.prime_dvd_prime_iff_eq hr (by norm_num)).mp h2
      subst this
      omega
  subst hr3
  have hs57 : s = 5 ∨ s = 7 := by
    have hord : orderOf y = s := orderOf_eq_prime hys hy1
    have hdvd : s ∣ 241920 := by
      rw [← hA, ← hord]
      exact orderOf_dvd_natCard y
    have h1 : s ∣ 2 ^ 8 * 3 ^ 3 * 5 * 7 := hfac ▸ hdvd
    rcases (Nat.Prime.dvd_mul hs).mp h1 with h2 | h2
    · rcases (Nat.Prime.dvd_mul hs).mp h2 with h3 | h3
      · rcases (Nat.Prime.dvd_mul hs).mp h3 with h4 | h4
        · have := (Nat.prime_dvd_prime_iff_eq hs Nat.prime_two).mp (hs.dvd_of_dvd_pow h4)
          subst this
          exact absurd hsodd (by decide)
        · exact absurd ((Nat.prime_dvd_prime_iff_eq hs Nat.prime_three).mp (hs.dvd_of_dvd_pow h4)) hsr
      · exact Or.inl ((Nat.prime_dvd_prime_iff_eq hs Nat.prime_five).mp h3)
    · exact Or.inr ((Nat.prime_dvd_prime_iff_eq hs (by norm_num)).mp h2)
  obtain ⟨v, hvV, hv1, hvin⟩ := exists_inner_ne_one V hVc (by rw [hO]; norm_num)
  have hv3 : v ^ 3 = 1 := elemPow_eq_one_of_isElementaryAbelian v hvV
  have hyin : y ∈ CFSG.ComponentClassification.OuterAutomorphisms.inner ↥S := mem_inner_of_pow_eq_one hys (by
    rw [hO]; rcases hs57 with rfl | rfl <;> norm_num)
  obtain ⟨g, rfl⟩ : ∃ g : ↥S, MulAut.conj g = v := hvin
  obtain ⟨k, rfl⟩ : ∃ k : ↥S, MulAut.conj k = y := hyin
  have hcomm := hVy _ hvV
  have hg3 : g ^ 3 = 1 := by apply hinj; rw [map_pow, hv3, map_one]
  have hg1 : g ≠ 1 := by rintro rfl; exact hv1 (map_one _)
  have hks : k ^ s = 1 := by apply hinj; rw [map_pow, hys, map_one]
  have hk1 : k ≠ 1 := by rintro rfl; exact hy1 (map_one _)
  have hgk : g * k = k * g := by apply hinj; rw [map_mul, map_mul, hcomm]
  refine S_no_comm g.2 k.2 (congrArg Subtype.val hgk) hs57 ?_ ?_ ?_ ?_
  · simpa using congrArg Subtype.val hg3
  · exact fun h => hg1 (Subtype.ext h)
  · simpa using congrArg Subtype.val hks
  · exact fun h => hk1 (Subtype.ext h)

end CFSG.GH74.GLS.Stage2.Bender.Thm1.CF67S

namespace CFSG.GH74.GLS.Stage2.Bender.Thm1

open CFSG.Blueprint CFSG.Assembly.LowTwoRank

theorem noN2_L34 (Y : Type) [Group Y]
    (h : LieModel Y .PSL 3 2 2) : NoN2 Y := by
  obtain ⟨e⟩ := CFSG.ComponentClassification.CatFactsSmall.nonempty_equiv_psl34_of_lieModel h
  exact NoN2.of_mulEquiv e CF67S.noN2_model

end CFSG.GH74.GLS.Stage2.Bender.Thm1

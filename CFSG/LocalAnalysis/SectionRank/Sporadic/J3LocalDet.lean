module

public import CFSG.LocalAnalysis.SectionRank.Sporadic.LocalDetWitness
public import CFSG.LocalAnalysis.SectionRank.Sporadic.OpsF2
public import Certificates.Data.CFSGNative.SectionRank.J3LocalDet
public meta import Certificates.Data.CFSGNative.SectionRank.J3LocalDet
import CFSG.Blueprint.NativeSporadic
public import Certificates.Certificate8022
public import CFSG.Open.Defs

public section

namespace CFSG.SectionRank

open CFSG.Open CFSG.SectionRank.Native

theorem not_sq_dvd_360 {r : ℕ} (hr : r.Prime) (h2 : r ≠ 2) (h3 : r ≠ 3) : ¬ r ^ 2 ∣ 360 := by
  intro h
  have hle : r ^ 2 ≤ 360 := Nat.le_of_dvd (by norm_num) h
  have : r ≤ 18 := by nlinarith
  interval_cases r <;> simp_all (config := {decide := true})

theorem isCyclic_sylow_of_card_eq_360 {K : Type*} [Group K] [Finite K]
    (hK : Nat.card K = 360) (r : ℕ) (hr : r.Prime) (h2 : r ≠ 2) (h3 : r ≠ 3) (R : Sylow r K) :
    IsCyclic (R : Subgroup K) := by
  have : Fact r.Prime := ⟨hr⟩
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.1 R.isPGroup'
  have hdvd : r ^ k ∣ 360 := hk ▸ hK ▸ Subgroup.card_subgroup_dvd_card _
  rcases Nat.lt_or_ge k 2 with hk2 | hk2
  · interval_cases k
    · rw [pow_zero] at hk
      have : Subsingleton (R : Subgroup K) := (Nat.card_eq_one_iff_unique.1 hk).1
      exact isCyclic_of_subsingleton
    · rw [pow_one] at hk
      exact isCyclic_of_prime_card hk
  · exact absurd (dvd_trans (pow_dvd_pow r hk2) hdvd) (not_sq_dvd_360 hr h2 h3)

theorem J3_perfect_local_det_witness :
    ∃ (K : Subgroup CFSG.Blueprint.NativeSporadic.J3) (_ : Group.IsPerfect K) (Q : Sylow 3 K)
      (x y : K) (h cc : CFSG.Blueprint.NativeSporadic.J3) (a b c d : ℕ),
      Nat.card K = 360 ∧ IsElemAbelian 3 (Q : Subgroup K) ∧
      Nat.card (Q : Subgroup K) = 3 ^ 2 ∧
      (∀ r : ℕ, r.Prime → r ≠ 2 → r ≠ 3 → ∀ R : Sylow r K, IsCyclic (R : Subgroup K)) ∧
      h ∈ Subgroup.normalizer (K : Set CFSG.Blueprint.NativeSporadic.J3) ∧
      Subgroup.closure ({x, y} : Set K) = Q ∧
      h * x * h⁻¹ =
        (x : CFSG.Blueprint.NativeSporadic.J3) ^ a * (y : CFSG.Blueprint.NativeSporadic.J3) ^ c ∧
      h * y * h⁻¹ =
        (x : CFSG.Blueprint.NativeSporadic.J3) ^ b * (y : CFSG.Blueprint.NativeSporadic.J3) ^ d ∧
      ((a * d - b * c : ℤ) : ZMod 3) ≠ 1 ∧
      (∀ k ∈ K, Commute cc k) ∧ orderOf cc = 3 ∧ Subgroup.zpowers cc ⊓ K = ⊥ := by
  obtain ⟨K, hP, Q, x, y, h, cc, hK, hQ, hQc, hn, hgen, hx, hy, hcK, hcc, hcK1⟩ :=
    Certificates.certificate8022
  have hK' : Nat.card K = 360 := hK
  have : Finite K := Nat.finite_of_card_ne_zero (by rw [hK']; decide)
  exact ⟨K, hP, Q, x, y, h, cc, 2, 1, 1, 0, hK', hQ, hQc,
    isCyclic_sylow_of_card_eq_360 (K := K) hK', hn, hgen, hx, hy, by decide, hcK, hcc, hcK1⟩

end CFSG.SectionRank

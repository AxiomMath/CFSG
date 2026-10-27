module

public import CFSG.ClassicalGroups.UnitaryFlag.SU3L2Centralizer
import CFSG.ClassicalGroups.UnitaryFlag.HomologyEigen
import CFSG.GH74.GLS.Stage2.Signalizer.Odd87FU3Card
import CFSG.GH74.KGroups.PSLN
import CFSG.Timmesfeld.Orders.Distinct
import CFSG.Walter.PSL2Facts.Even

public section

namespace CFSG.ClassicalGroups.UnitaryFlag

open CFSG.LocalAnalysis.ComponentInitial CFSG.LinearGroups
open CFSG.LocalAnalysis.UniquenessCase.UC22

variable {m : ℕ} {K : Type} [Field K]

theorem mulVec_eq_of_mem_normalizer_of_pow_eq_one (h : UnitaryFieldData 2 m K) {v : Fin 3 → K}
    (hv : stdHermForm h 3 v v ≠ 0) {L : Subgroup (unitarySU 2 m K 3)}
    (hL : ∀ g, g ∈ L ↔ ((g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K).mulVec v = v)
    {y : unitarySU 2 m K 3} (hy : y ∈ Subgroup.normalizer (L : Set (unitarySU 2 m K 3)))
    {k : ℕ} (hyk : y ^ 2 ^ k = 1) :
    ((y : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K).mulVec v = v := by
  have hfix : ∀ g ∈ L, g • (y • v) = y • v := by
    intro g hg
    have hconj : y⁻¹ * g * y ∈ L := (Subgroup.mem_normalizer_iff''.mp hy g).mp hg
    calc
      g • (y • v) = (g * y) • v := (mul_smul g y v).symm
      _ = (y * (y⁻¹ * g * y)) • v := by
        rw [show y * (y⁻¹ * g * y) = g * y by group]
      _ = y • ((y⁻¹ * g * y) • v) := mul_smul y (y⁻¹ * g * y) v
      _ = y • v := by
        rw [unitarySU_smul_def h (y⁻¹ * g * y) v, Matrix.mulVecLin_apply,
          (hL (y⁻¹ * g * y)).mp hconj]
  obtain ⟨c, hc⟩ := exists_eq_smul_of_forall_mem_mulVec_eq h hv hL (w := y • v) (fun g hg => by
    rw [← Matrix.mulVecLin_apply, ← unitarySU_smul_def h]
    exact hfix g hg)
  have hv0 : v ≠ 0 := fun h0 => hv (by rw [h0]; simp)
  have hcv : c ^ 2 ^ k • v = v := by
    have h := pow_smul_eq_smul_pow (a := y) (e := v) (c := c) hc (2 ^ k)
    rw [hyk, one_smul] at h
    rw [← h]
  have hc1pow : c ^ 2 ^ k = 1 := by
    have h : (c ^ 2 ^ k - 1) • v = 0 := by
      rw [sub_smul, hcv, one_smul, sub_self]
    rcases smul_eq_zero.mp h with h' | h'
    · exact sub_eq_zero.mp h'
    · exact absurd h' hv0
  have hc1 : c = 1 := by
    have : CharP K 2 := h.charP
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have h2 : (c - 1) ^ 2 ^ k = 0 := by
      rw [sub_pow_char_pow, hc1pow, one_pow, sub_self]
    exact sub_eq_zero.mp ((pow_eq_zero_iff (pow_ne_zero k two_ne_zero)).mp h2)
  rw [← Matrix.mulVecLin_apply, ← unitarySU_smul_def h, hc, hc1, one_smul]

theorem not_le_normalizer_of_nonisotropic (h : UnitaryFieldData 2 m K) (hm : 2 ≤ m)
    {v : Fin 3 → K} (hv : stdHermForm h 3 v v ≠ 0) {L : Subgroup (unitarySU 2 m K 3)}
    (hL : ∀ g, g ∈ L ↔ ((g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K).mulVec v = v)
    (T : Sylow 2 (unitarySU 2 m K 3)) :
    ¬ (T : Subgroup (unitarySU 2 m K 3)) ≤ Subgroup.normalizer (L : Set (unitarySU 2 m K 3)) := by
  intro hTN
  have hfin : Finite K := h.finite
  obtain ⟨e, f, he, hf, hef, hev, hfv⟩ := exists_hyperbolic_pair_of_nonisotropic h hv
  have hL2 : IsL2 L m :=
    isL2_of_forall_mem_iff_mulVec_eq h hm hv he hf hef hev hfv hL
  obtain ⟨eL⟩ := CFSG.GH74.KGroups.PSLN.psl_equiv_of_lieModel (K := L) 2 2 m
    (F := GaloisField 2 m) (by omega)
    (GaloisField.card (p := 2) (n := m) (by omega)) hL2
  have hcardL : Nat.card L = 2 ^ m * ((2 ^ m) ^ 2 - 1) := by
    rw [Nat.card_congr eL.toEquiv]
    exact CFSG.Walter.psl2_even_card (f := m) (by omega)
  have hTL : (T : Subgroup (unitarySU 2 m K 3)) ≤ L := by
    intro t ht
    obtain ⟨j, hj⟩ := IsPGroup.iff_orderOf.mp T.isPGroup' ⟨t, ht⟩
    have hpow : t ^ 2 ^ j = 1 := by
      have h := pow_orderOf_eq_one (⟨t, ht⟩ : (T : Subgroup (unitarySU 2 m K 3)))
      rw [hj] at h
      simpa using h
    exact (hL t).mpr (mulVec_eq_of_mem_normalizer_of_pow_eq_one h hv hL (hTN ht) hpow)
  have hoddA : Odd ((2 ^ m) ^ 2 - 1) :=
    CFSG.Timmesfeld.Orders.odd_pow_sub_one (f := m) (a := 2) (by omega) (by norm_num)
  have hoddB : Odd ((2 ^ m) ^ 3 + 1) :=
    CFSG.Timmesfeld.Orders.odd_pow_add_one (f := m) (a := 3) (by omega) (by norm_num)
  have hfacA : ((2 ^ m) ^ 2 - 1).factorization 2 = 0 :=
    Nat.factorization_eq_zero_of_not_dvd hoddA.not_two_dvd_nat
  have hfacB : ((2 ^ m) ^ 3 + 1).factorization 2 = 0 :=
    Nat.factorization_eq_zero_of_not_dvd hoddB.not_two_dvd_nat
  have hA0 : (2 ^ m) ^ 2 - 1 ≠ 0 := hoddA.pos.ne'
  have hfac : (Nat.card (unitarySU 2 m K 3)).factorization 2 = 3 * m := by
    rw [CFSG.GH74.GLS.Stage2.Signalizer.Odd87.card_unitarySU_three h]
    rw [Nat.factorization_mul (mul_ne_zero (pow_ne_zero 3 (by norm_num)) hA0)
      (by positivity : (2 ^ m) ^ 3 + 1 ≠ 0)]
    rw [Nat.factorization_mul (pow_ne_zero 3 (by norm_num)) hA0]
    simp [hfacA, hfacB, Nat.Prime.factorization_self Nat.prime_two]
  have hcardT : Nat.card (T : Subgroup (unitarySU 2 m K 3)) = 2 ^ (3 * m) := by
    rw [Sylow.card_eq_multiplicity T, hfac]
  have hdiv : 2 ^ (3 * m) ∣ Nat.card L := by
    rw [← hcardT]
    exact Subgroup.card_dvd_of_le hTL
  rw [hcardL] at hdiv
  have hcop : Nat.Coprime (2 ^ (3 * m)) ((2 ^ m) ^ 2 - 1) := by
    rw [Nat.coprime_pow_left_iff (by omega : 0 < 3 * m)]
    exact Nat.coprime_two_left.mpr hoddA
  have hdvd : 2 ^ (3 * m) ∣ 2 ^ m := hcop.dvd_of_dvd_mul_right hdiv
  have hle : 2 ^ (3 * m) ≤ 2 ^ m := Nat.le_of_dvd (by positivity) hdvd
  have hlt : 2 ^ m < 2 ^ (3 * m) :=
    Nat.pow_lt_pow_right (by norm_num : 1 < 2) (by omega)
  omega

end CFSG.ClassicalGroups.UnitaryFlag

end

module

public import CFSG.LocalAnalysis.ComponentClassification.GS82PumpOddCharCof
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofLieOrder
public import CFSG.LocalAnalysis.ComponentClassification.GS82PumpP1Defs

public section

namespace CFSG.ComponentClassification.GS82PumpInputs

open CFSG.Assembly.LowTwoRank CFSG.ComponentClassification.CatLeaf
  CFSG.ComponentClassification.CatLeafProof

namespace OddChar

theorem lieSylowExponent_pos {t : StatedLieTag} {n p f : ℕ}
    (hadm : StatedLieAdmissible t n p f) : 0 < lieSylowExponent t n := by
  have tri : ∀ {m : ℕ}, 2 ≤ m → 0 < m * (m - 1) / 2 := fun {m} hm =>
    Nat.div_pos (by simpa using Nat.mul_le_mul hm (show 1 ≤ m - 1 by omega)) two_pos
  cases t
  case PSL => exact tri hadm.2.2.1
  case PSU => exact tri (by have := hadm.2.2.1; omega)
  case PSp => exact pow_pos (by have := hadm.2.2.1; omega) 2
  case POmegaOdd => exact pow_pos (by have := hadm.2.2.1; omega) 2
  case POmegaPlus => exact Nat.mul_pos (by have := hadm.2.2; omega) (by have := hadm.2.2; omega)
  case POmegaMinus => exact Nat.mul_pos (by have := hadm.2.2; omega) (by have := hadm.2.2; omega)
  all_goals simp only [lieSylowExponent]; norm_num

theorem ordProj_le_of_mul_eq {t : StatedLieTag} {n p f M : ℕ}
    (hadm : StatedLieAdmissible t n p f) (hp2 : p ≠ 2)
    (hM : M * lieOrderDivisor t n (p ^ f) = lieOrderNumerator t n (p ^ f)) {s : ℕ}
    (hs : s.Prime) (hs2 : s ≠ 2) (hsp : s ≠ p) :
    ordProj[s] M ≤ (p ^ f) ^ lieSylowExponent t n := by
  have hp := hadm.1
  have hq0 : (p ^ f) ^ lieSylowExponent t n ≠ 0 := pow_ne_zero _ (pow_ne_zero _ hp.ne_zero)
  have hC0 := lieOrderCofactor_ne_zero hadm
  have hnum : lieOrderNumerator t n (p ^ f) ≠ 0 := by
    rw [lieOrderNumerator_eq hadm]
    exact mul_ne_zero hq0 hC0
  have h1 : ordProj[s] M ≤ ordProj[s] (lieOrderNumerator t n (p ^ f)) :=
    Nat.le_of_dvd (Nat.ordProj_pos _ _) (Nat.ordProj_dvd_ordProj_of_dvd hnum ⟨_, hM.symm⟩ s)
  have hsq : ¬ s ∣ (p ^ f) ^ lieSylowExponent t n := fun hd =>
    hsp ((Nat.prime_dvd_prime_iff_eq hs hp).mp (hs.dvd_of_dvd_pow (hs.dvd_of_dvd_pow hd)))
  rw [lieOrderNumerator_eq hadm, Nat.ordProj_mul s hq0 hC0,
    Nat.factorization_eq_zero_of_not_dvd hsq, pow_zero, one_mul] at h1
  exact h1.trans (ordProj_lieOrderCofactor_le hadm hp2 hs hs2 hsp)

end OddChar

theorem oddLieCharUnique_holds :
    OddLieCharUnique := by
  intro X _ t n p f t' n' r f' hp2 hr2 h h'
  by_contra hpr
  have hadm := h.admissible
  have hadm' := h'.admissible
  obtain ⟨-, hmul, hfac⟩ := lieOrderFormulasInput X t n p f hadm h
  obtain ⟨-, hmul', hfac'⟩ := lieOrderFormulasInput X t' n' r f' hadm' h'
  have h1 := OddChar.ordProj_le_of_mul_eq hadm hp2 hmul hadm'.1 hr2 (Ne.symm hpr)
  have h2 := OddChar.ordProj_le_of_mul_eq hadm' hr2 hmul' hadm.1 hp2 hpr
  rw [← pow_mul, mul_comm f, ← hfac] at h1
  rw [← pow_mul, mul_comm f', ← hfac'] at h2
  have hvp : 0 < (Nat.card X).factorization p := by
    rw [hfac]
    exact Nat.mul_pos (OddChar.lieSylowExponent_pos hadm) hadm.2.1
  have hpdvd : p ∣ ordProj[r] (Nat.card X) := by
    rw [← le_antisymm h2 h1]
    exact dvd_pow_self p hvp.ne'
  exact hpr ((Nat.prime_dvd_prime_iff_eq hadm.1 hadm'.1).mp (hadm.1.dvd_of_dvd_pow hpdvd))

end CFSG.ComponentClassification.GS82PumpInputs

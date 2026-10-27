module

public import CFSG.HardMathSupport.Dickson.Sec6.I1431LieAux.Low
public import CFSG.HardMathSupport.Solomon.Coordinator.InndiagLink
public import CFSG.RankThree.PartTwo.KFacts.AutPSUInner

public section

namespace CFSG.HardMathSupport.Dickson.Sec6.I1431

open CFSG CFSG.Open CFSG.Blueprint CFSG.Assembly.LowTwoRank CFSG.HardMathSupport.Solomon.Coordinator
  CFSG.RankThree.PartTwo.KFacts CFSG.RankThree.PartOne.Sec66T CFSG.LocalAnalysis.ComponentInitial
  CFSG.ClassicalGroups.UnitaryFlag CFSG.HardMathSupport.Solomon.LocalBalance.Lemma514CoverNs

section Core

variable {p f : ℕ} {K : Type} [Field K] {h : UnitaryFieldData p f K}

theorem t6outpsu_pow_mem_range_conj (A : unitaryIsom3 h) :
    (psuConj h A) ^ (p ^ f + 1) ∈
      (MulAut.conj : unitaryPSU h 3 →* MulAut (unitaryPSU h 3)).range := by
  rw [← map_pow]
  refine psuConj_mem_range_conj_of_det_eq_pow (u := 1) ?_ ?_
  · rw [Units.val_one]
    rw [UnitaryFieldData.norm, map_one, mul_one]
  · rw [one_pow, Subgroup.coe_pow, map_pow]
    apply Units.ext
    have hn := norm_det_of_mem_unitaryIsom3 A.2
    rw [UnitaryFieldData.norm, UnitaryFieldData.bar_apply] at hn
    rw [Units.val_pow_eq_pow_val, pow_succ, Units.val_one, Matrix.GeneralLinearGroup.val_det_apply]
    rw [mul_comm]
    exact hn

theorem t6outpsu_mem_range_conj_of_not_dvd {β : MulAut (unitaryPSU h 3)}
    (hβ : β ∈ (psuConj h).range) (hq : ¬ 3 ∣ p ^ f + 1) :
    β ∈ (MulAut.conj : unitaryPSU h 3 →* MulAut (unitaryPSU h 3)).range := by
  set S := (MulAut.conj : unitaryPSU h 3 →* MulAut (unitaryPSU h 3)).range
  have h3 : β ^ 3 ∈ S := cube_mem_range_conj_of_mem_psuConj_range hβ
  obtain ⟨A, rfl⟩ := hβ
  have hm : (psuConj h A) ^ (p ^ f + 1) ∈ S := t6outpsu_pow_mem_range_conj A
  have hcop : Nat.Coprime (p ^ f + 1) 3 :=
    Nat.Coprime.symm ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).2 hq)
  have hab : (((p ^ f + 1 : ℕ) : ℤ) * Nat.gcdA (p ^ f + 1) 3 +
      ((3 : ℕ) : ℤ) * Nat.gcdB (p ^ f + 1) 3) = 1 := by
    rw [← Nat.gcd_eq_gcd_ab, hcop, Nat.cast_one]
  have hβ' : psuConj h A = ((psuConj h A) ^ (p ^ f + 1)) ^ Nat.gcdA (p ^ f + 1) 3 *
      ((psuConj h A) ^ 3) ^ Nat.gcdB (p ^ f + 1) 3 := by
    rw [← zpow_natCast (psuConj h A) (p ^ f + 1), ← zpow_natCast (psuConj h A) 3,
      ← _root_.zpow_mul, ← _root_.zpow_mul, ← _root_.zpow_add, hab, zpow_one]
  rw [hβ']
  exact S.mul_mem (S.zpow_mem hm _) (S.zpow_mem h3 _)

end Core

theorem outDerived3_psuGoodThree : OutDerived3At FamPsuGoodThree := by
  intro P _ _ t n p f hadm ht hF hm τ hτ hτ3
  obtain ⟨rfl, rfl, hnd, hp3⟩ := hF
  have hC : StatedClassicalModel P .PSU 3 p f := (lieModel_classical_iff (by decide)).mp hm
  obtain ⟨-, K, _, _, hK, ⟨e0⟩⟩ := hC
  have hp : p.Prime := hadm.1
  have hf : 1 ≤ f := hadm.2.1
  have hUF : UnitaryFieldData p f K :=
    ⟨hp, hf, by rw [hK, ← pow_mul, mul_comm]⟩
  have hq : 2 < p ^ f := by
    have h1 : 2 ≤ p ^ f := le_trans hp.two_le (Nat.le_self_pow (by omega) p)
    have h2 : p ^ f ≠ 2 := fun h2 => hadm.2.2.2 (by rw [h2])
    omega
  have hre : ¬ 3 ∣ p ^ f + 1 := fun h => hnd (by rw [Nat.gcd_eq_left h])
  have h1 : IsInnDiagPSU 3 (p ^ f) e0 τ :=
    (isInnDiagPSU_three_iff_mem_innAutDerived hUF hq e0 τ).2 hτ
  have h2 := (isInnDiagPSU_three_iff hUF e0 τ).1 h1
  rw [PinnedAut.mem_comap_inndiag] at h2
  have h3 : MulAut.congr (e0.trans (psuO hUF).symm) τ ∈ (psuConj hUF).range := h2
  exact (isInnerAut_congr (e0.trans (psuO hUF).symm) τ).1
    (t6outpsu_mem_range_conj_of_not_dvd h3 hre)

end CFSG.HardMathSupport.Dickson.Sec6.I1431

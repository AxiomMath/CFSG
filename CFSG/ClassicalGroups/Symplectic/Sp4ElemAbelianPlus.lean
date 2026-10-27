module

public import CFSG.Open.StatedDefs
public import CFSG.Open.LocalVocabulary
public import CFSG.GroupTheory.ElemAbelianClosure
public import CFSG.GroupTheory.TwoReflections
public import CFSG.CGT.Timmesfeld75.L2Sylow
public import CFSG.LocalAnalysis.ComponentInitial.SymplecticTorusInverters
public import CFSG.GroupTheory.CommutingProductFixedSubgroup

public section

namespace CFSG.ClassicalGroups.Symplectic.Sp4

open Matrix Subgroup CFSG.Open
open CFSG.LocalAnalysis.ComponentInitial.SymplecticTorusWeyl

theorem eq_one_of_lam_zero_eq_lam_one {K : Type} [Field K]
    {h h' : SpecialLinearGroup (Fin 2) K}
    (heq : lam (r := 2) (k := K) 0 h = lam (r := 2) (k := K) 1 h') :
    h = 1 := by
  have hm := congrArg (fun z : StatedSp 2 K =>
    ((z : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K)) heq
  simp only [coe_lam] at hm
  obtain ⟨a1, a2, a3, a4⟩ := pairMat_apply_pair
    (R := K) (Sum.inl_ne_inr : (Sum.inl (0 : Fin 2) : Fin 2 ⊕ Fin 2) ≠ Sum.inr 0)
    (h : Matrix (Fin 2) (Fin 2) K)
  rw [hm] at a1 a2 a3 a4
  have e00 : (h : Matrix (Fin 2) (Fin 2) K) 0 0 = 1 := by
    rw [pairMat_apply_of_ne (x := Sum.inl (0 : Fin 2)) (by simp) (by simp)] at a1
    simpa using a1.symm
  have e01 : (h : Matrix (Fin 2) (Fin 2) K) 0 1 = 0 := by
    rw [pairMat_apply_of_ne (x := Sum.inl (0 : Fin 2)) (y := Sum.inr (0 : Fin 2))
      (by simp) (by simp)] at a2
    simpa using a2.symm
  have e10 : (h : Matrix (Fin 2) (Fin 2) K) 1 0 = 0 := by
    rw [pairMat_apply_of_ne (x := Sum.inr (0 : Fin 2)) (y := Sum.inl (0 : Fin 2))
      (by simp) (by simp)] at a3
    simpa using a3.symm
  have e11 : (h : Matrix (Fin 2) (Fin 2) K) 1 1 = 1 := by
    rw [pairMat_apply_of_ne (x := Sum.inr (0 : Fin 2)) (by simp) (by simp)] at a4
    simpa using a4.symm
  ext j k
  fin_cases j <;> fin_cases k
  · simpa using e00
  · simpa using e01
  · simpa using e10
  · simpa using e11

theorem exists_isElemAbelian_card_sq_of_dvd_card_add_one {K : Type} [Field K] [Finite K]
    {p : ℕ} (hp : p.Prime) (hpd : p ∣ Nat.card K + 1) :
    ∃ E : Subgroup (StatedSp 2 K), IsElemAbelian p E ∧ Nat.card E = p ^ 2 := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hsq : p ∣ Nat.card K ^ 2 - 1 := by
    have hfac : Nat.card K ^ 2 - 1 = (Nat.card K + 1) * (Nat.card K - 1) := by
      obtain ⟨t, ht⟩ : ∃ t, Nat.card K = t + 1 :=
        ⟨Nat.card K - 1, by have := Nat.card_pos (α := K); omega⟩
      rw [ht]
      have h : (t + 1) ^ 2 = (t + 1 + 1) * t + 1 := by ring
      rw [h, Nat.add_sub_cancel, Nat.add_sub_cancel]
    rw [hfac]
    exact hpd.mul_right _
  have hdvd : p ∣ Nat.card (SpecialLinearGroup (Fin 2) K) := by
    rw [CFSG.CGT.Timmesfeld75.card_sl2]
    exact dvd_mul_of_dvd_right hsq _
  obtain ⟨g, hg⟩ := exists_prime_orderOf_dvd_card' p hdvd
  let x : StatedSp 2 K := lam (r := 2) (k := K) 0 g
  let y : StatedSp 2 K := lam (r := 2) (k := K) 1 g
  have hx : orderOf x = p := by
    dsimp only [x]
    rw [orderOf_lam, hg]
  have hy : orderOf y = p := by
    dsimp only [y]
    rw [orderOf_lam, hg]
  have hcomm : Commute x y := commute_lam_lam (i := (0 : Fin 2)) (j := (1 : Fin 2))
    (by decide) g g
  have hinf : Subgroup.zpowers x ⊓ Subgroup.zpowers y = ⊥ := by
    rw [eq_bot_iff]
    intro z hz
    rw [Subgroup.mem_bot]
    obtain ⟨hzx, hzy⟩ := Subgroup.mem_inf.mp hz
    obtain ⟨a, ha⟩ := Subgroup.mem_zpowers_iff.mp hzx
    obtain ⟨b, hb⟩ := Subgroup.mem_zpowers_iff.mp hzy
    have heq : lam (r := 2) (k := K) 0 (g ^ a) = lam (r := 2) (k := K) 1 (g ^ b) := by
      calc lam (r := 2) (k := K) 0 (g ^ a) = (lam (r := 2) (k := K) 0 g) ^ a := map_zpow _ _ _
        _ = x ^ a := rfl
        _ = z := ha
        _ = y ^ b := hb.symm
        _ = (lam (r := 2) (k := K) 1 g) ^ b := rfl
        _ = lam (r := 2) (k := K) 1 (g ^ b) := (map_zpow _ _ _).symm
    have hg1 : g ^ a = 1 := eq_one_of_lam_zero_eq_lam_one heq
    calc z = x ^ a := ha.symm
      _ = (lam (r := 2) (k := K) 0 g) ^ a := rfl
      _ = lam (r := 2) (k := K) 0 (g ^ a) := (map_zpow _ _ _).symm
      _ = 1 := by rw [hg1, map_one]
  refine ⟨Subgroup.zpowers x ⊔ Subgroup.zpowers y, ?_, ?_⟩
  · refine IsElemAbelian.sup_of_commute
      (isElemAbelian_zpowers (p := p) (x := x) ?_) (isElemAbelian_zpowers (p := p) (x := y) ?_) ?_
    · rw [← hx]; exact pow_orderOf_eq_one x
    · rw [← hy]; exact pow_orderOf_eq_one y
    · intro a ha b hb
      obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
      obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hb
      exact (hcomm.zpow_zpow m n).eq
  · exact (CFSG.GroupTheory.card_zpowers_sup_zpowers (r := p) hcomm hx hy hinf).1

end CFSG.ClassicalGroups.Symplectic.Sp4

end

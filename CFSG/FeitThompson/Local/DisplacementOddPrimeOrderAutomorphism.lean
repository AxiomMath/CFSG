module

public import Mathlib.Algebra.Module.Torsion.Basic
public import Mathlib.Data.Nat.Choose.Dvd

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

namespace CFSG.FeitThompson

open Finset

variable {A : Type*} [AddCommGroup A] {p : ℕ}

theorem pow_nsmul_eq_zero_of_le {k l : ℕ} {v : A} (h : p ^ k • v = 0) (hkl : k ≤ l) :
    p ^ l • v = 0 := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hkl
  rw [pow_add, mul_comm, ← smul_smul, h, smul_zero]

theorem pow_nsmul_pow_apply_eq_zero {D : AddMonoid.End A}
    (hD : ∀ v : A, p • v = 0 → D v = 0) (j : ℕ) :
    ∀ (k : ℕ) (v : A), p ^ (j + k) • v = 0 → p ^ k • (D ^ j) v = 0 := by
  induction j with
  | zero => intro k v h; simpa using h
  | succ j ih =>
    intro k v h
    have hDv : p ^ (j + k) • D v = 0 := by
      have h1 : p • (p ^ (j + k) • v) = 0 := by
        rw [smul_smul, ← pow_succ']
        exact pow_nsmul_eq_zero_of_le h (by omega)
      have h2 := hD _ h1
      rwa [map_nsmul] at h2
    have h3 : (D ^ (j + 1)) v = (D ^ j) (D v) := by
      rw [pow_succ]; simp [AddMonoid.End.coe_mul]
    rw [h3]
    exact ih k (D v) hDv

theorem add_one_pow_apply {D : AddMonoid.End A} (n : ℕ) (a : A) :
    ((D + 1) ^ n) a = ∑ m ∈ range (n + 1), n.choose m • (D ^ m) a := by
  rw [(Commute.one_right D).add_pow n]
  simp only [one_pow, mul_one]
  rw [show ((∑ m ∈ range (n + 1), D ^ m * (n.choose m : AddMonoid.End A)) : AddMonoid.End A) a
      = ∑ m ∈ range (n + 1), (D ^ m * (n.choose m : AddMonoid.End A)) a from
      AddMonoidHom.finsetSum_apply _ _ _]
  refine Finset.sum_congr rfl fun m _ => ?_
  simp [AddMonoid.End.coe_mul, AddMonoid.End.natCast_apply]

theorem pow_nsmul_apply_descent (hp : p.Prime) (hp3 : 3 ≤ p) {D : AddMonoid.End A}
    (hD1 : (D + 1) ^ p = 1) (hD : ∀ v : A, p • v = 0 → D v = 0) (s : ℕ) {v : A}
    (h : p ^ (s + 2) • D v = 0) : p ^ (s + 1) • D v = 0 := by
  have hsum := add_one_pow_apply (D := D) p v
  rw [hD1] at hsum
  simp only [AddMonoid.End.one_apply] at hsum
  rw [Finset.range_eq_Ico, Finset.sum_eq_sum_Ico_succ_bot (by omega),
    Finset.sum_eq_sum_Ico_succ_bot (a := 1) (b := p + 1) (by omega)] at hsum
  simp only [Nat.choose_zero_right, pow_zero, AddMonoid.End.one_apply, one_smul,
    Nat.choose_one_right, pow_one] at hsum
  have hkey : p • D v + ∑ m ∈ Finset.Ico 2 (p + 1), p.choose m • (D ^ m) v = 0 := by
    have h2 : (1 : ℕ) + 1 = 2 := rfl
    rw [h2] at hsum
    exact left_eq_add.mp hsum
  have hS : p ^ s • (∑ m ∈ Finset.Ico 2 (p + 1), p.choose m • (D ^ m) v) = 0 := by
    rw [Finset.smul_sum]
    refine Finset.sum_eq_zero fun m hm => ?_
    simp only [Finset.mem_Ico] at hm
    have hmv : (D ^ m) v = (D ^ (m - 1)) (D v) := by
      have hm1 : m = (m - 1) + 1 := by omega
      rw [hm1, pow_succ]; simp [AddMonoid.End.coe_mul]
    rcases eq_or_lt_of_le (show m ≤ p by omega) with hmp | hmp
    ·
      have hz : p ^ s • (D ^ m) v = 0 := by
        rw [hmv]
        exact pow_nsmul_pow_apply_eq_zero hD (m - 1) s (D v)
          (pow_nsmul_eq_zero_of_le h (by omega))
      rw [smul_comm, hz, smul_zero]
    ·
      obtain ⟨c, hc⟩ := hp.dvd_choose_self (k := m) (by omega) hmp
      have hz : p ^ (s + 1) • (D ^ m) v = 0 := by
        rw [hmv]
        exact pow_nsmul_pow_apply_eq_zero hD (m - 1) (s + 1) (D v)
          (pow_nsmul_eq_zero_of_le h (by omega))
      rw [hc, smul_smul, show p ^ s * (p * c) = c * p ^ (s + 1) by ring, ← smul_smul, hz,
        smul_zero]
  have hneg : p • D v = -∑ m ∈ Finset.Ico 2 (p + 1), p.choose m • (D ^ m) v := by
    rw [eq_neg_iff_add_eq_zero]; exact hkey
  rw [pow_succ, mul_smul, hneg, smul_neg, hS, neg_zero]

theorem nsmul_apply_sub_self_eq_zero_of_pow_nsmul_eq_zero (hp : p.Prime) (hodd : Odd p)
    (T : AddMonoid.End A) (hTp : T ^ p = 1) (hfix : ∀ a : A, p • a = 0 → T a = a) {N : ℕ}
    (hN : ∀ a : A, p ^ N • a = 0) (a : A) : p • (T a - a) = 0 := by
  have hp3 : 3 ≤ p := by
    obtain ⟨k, hk⟩ := hodd
    have := hp.two_le
    omega
  set D : AddMonoid.End A := T - 1 with hDdef
  have hDapply : ∀ b : A, D b = T b - b := fun _ => rfl
  have hD1 : (D + 1) ^ p = 1 := by
    rw [hDdef, sub_add_cancel]; exact hTp
  have hD : ∀ v : A, p • v = 0 → D v = 0 := by
    intro v hv
    rw [hDapply, hfix v hv, sub_self]
  have main : ∀ s : ℕ, (∀ b : A, p ^ (s + 1) • D b = 0) → ∀ b : A, p • D b = 0 := by
    intro s
    induction s with
    | zero => intro h b; simpa using h b
    | succ s ih => exact fun h b => ih (fun c => pow_nsmul_apply_descent hp hp3 hD1 hD s (h c)) b
  rw [← hDapply]
  exact main N (fun b => pow_nsmul_eq_zero_of_le (hN (D b)) (Nat.le_succ N)) a

theorem nsmul_apply_sub_self_eq_zero (hp : p.Prime) (hodd : Odd p) {n : ℕ}
    (hcard : Nat.card A = p ^ n) (t : A ≃+ A) (htp : (⇑t)^[p] = id)
    (hfix : ∀ a : A, p • a = 0 → t a = a) (a : A) : p • (t a - a) = 0 := by
  set T : AddMonoid.End A := t.toAddMonoidHom with hT
  have hTp : T ^ p = 1 := by
    ext b
    rw [AddMonoid.End.coe_pow]
    exact congrFun htp b
  have hfix' : ∀ b : A, p • b = 0 → T b = b := hfix
  have hN : ∀ b : A, p ^ n • b = 0 := by
    intro b
    rw [← hcard]
    exact card_nsmul_eq_zero'
  exact nsmul_apply_sub_self_eq_zero_of_pow_nsmul_eq_zero hp hodd T hTp hfix' hN a

theorem quotientAddGroup_mk_apply_eq_mk (hp : p.Prime) (hodd : Odd p) {n : ℕ}
    (hcard : Nat.card A = p ^ n) (t : A ≃+ A) (htp : (⇑t)^[p] = id)
    (hfix : ∀ a : A, p • a = 0 → t a = a) (a : A) :
    (QuotientAddGroup.mk (t a) : A ⧸ AddSubgroup.torsionBy A (p : ℤ)) =
      QuotientAddGroup.mk a := by
  rw [QuotientAddGroup.eq_iff_sub_mem]
  exact AddSubgroup.torsionBy.nsmul_iff.2 (nsmul_apply_sub_self_eq_zero hp hodd hcard t htp hfix a)

end CFSG.FeitThompson

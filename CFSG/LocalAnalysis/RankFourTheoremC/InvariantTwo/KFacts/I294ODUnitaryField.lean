module

public import Mathlib.NumberTheory.Multiplicity
public import Mathlib.FieldTheory.Finite.Basic
public import CFSG.LocalAnalysis.RankFourTheoremC.InvariantTwo.KFacts.I294ODEigen
public import Mathlib.Combinatorics.Matroid.Init

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC

namespace I294OD

open Polynomial

theorem od_pq_dvd {p q : ℕ} (hp : Odd p) (hpq : p ∣ q + 1) : p * (q + 1) ∣ q ^ p + 1 := by
  obtain ⟨u, hu⟩ := hpq
  obtain ⟨t, ht⟩ := sq_dvd_add_pow_sub_sub ((q : ℤ) + 1) (-1) p
  have h1 : (-1 + ((q : ℤ) + 1)) = q := by ring
  have h2 : ((-1 : ℤ) ^ (p - 1)) = 1 := by
    obtain ⟨k, rfl⟩ := hp
    exact Even.neg_one_pow ⟨k, by omega⟩
  have h3 : ((-1 : ℤ) ^ p) = -1 := Odd.neg_one_pow hp
  rw [h1, h2, h3] at ht
  refine Int.natCast_dvd_natCast.mp ?_
  push_cast
  have hu' : (q : ℤ) + 1 = p * u := by exact_mod_cast hu
  refine ⟨1 + u * t, ?_⟩
  have h4 : (q : ℤ) ^ p + 1 = (q + 1) * p + (q + 1) ^ 2 * t := by linear_combination ht
  rw [h4]
  have h5 : (q + 1 : ℤ) ^ 2 * t = (q + 1) * (p * u) * t := by rw [← hu']; ring
  rw [h5]
  ring

section Field

variable {K : Type} [Field K] [Finite K] {p : ℕ} [hpf : Fact p.Prime] {c : K}
  [hirr : Fact (Irreducible (X ^ p - C c : K[X]))]

theorem odA_root_pow : (AdjoinRoot.root (X ^ p - C c : K[X])) ^ p = algebraMap K _ c := by
  have := AdjoinRoot.eval₂_root (X ^ p - C c : K[X])
  simp only [eval₂_sub, eval₂_pow, eval₂_X, eval₂_C] at this
  rw [AdjoinRoot.algebraMap_eq]
  exact sub_eq_zero.1 this

theorem odA_finrank :
    Module.finrank K (AdjoinRoot (X ^ p - C c : K[X])) = p := by
  have hf0 : (X ^ p - C c : K[X]) ≠ 0 := (monic_X_pow_sub_C c hpf.out.ne_zero).ne_zero
  rw [(AdjoinRoot.powerBasis hf0).finrank]
  simp [AdjoinRoot.powerBasis, natDegree_X_pow_sub_C]

instance odA_finite : Finite (AdjoinRoot (X ^ p - C c : K[X])) := by
  have hf0 : (X ^ p - C c : K[X]) ≠ 0 := (monic_X_pow_sub_C c hpf.out.ne_zero).ne_zero
  haveI : Module.Finite K (AdjoinRoot (X ^ p - C c : K[X])) :=
    (AdjoinRoot.powerBasis hf0).finite
  exact Module.finite_of_finite K

theorem odA_card :
    Nat.card (AdjoinRoot (X ^ p - C c : K[X])) = Nat.card K ^ p := by
  haveI : Module.Finite K (AdjoinRoot (X ^ p - C c : K[X])) :=
    (AdjoinRoot.powerBasis ((monic_X_pow_sub_C c hpf.out.ne_zero).ne_zero)).finite
  rw [Module.natCard_eq_pow_finrank (K := K), odA_finrank]

end Field

section Iota

variable {K : Type} [Field K] [Finite K] {r e0 p : ℕ} [Fact r.Prime] [CharP K r]
  [hpf : Fact p.Prime] {c : K} [hirr : Fact (Irreducible (X ^ p - C c : K[X]))]

instance odA_charP : CharP (AdjoinRoot (X ^ p - C c : K[X])) r :=
  charP_of_injective_algebraMap (algebraMap K (AdjoinRoot (X ^ p - C c : K[X]))).injective r

variable (K r e0 p c) in
@[expose] noncomputable def odIota :
    AdjoinRoot (X ^ p - C c : K[X]) →+* AdjoinRoot (X ^ p - C c : K[X]) :=
  iterateFrobenius (AdjoinRoot (X ^ p - C c : K[X])) r (e0 * p)

theorem odIota_apply (x : AdjoinRoot (X ^ p - C c : K[X])) :
    odIota K r e0 p c x = x ^ ((r ^ e0) ^ p) := by
  rw [odIota, iterateFrobenius_def, pow_mul]

theorem odIota_algebraMap (hK : Nat.card K = (r ^ e0) ^ 2) (hp : Odd p) (a : K) :
    odIota K r e0 p c (algebraMap K _ a) = algebraMap K _ (a ^ (r ^ e0)) := by
  rw [odIota_apply, ← map_pow]
  congr 1
  haveI := Fintype.ofFinite K
  have hcard : Fintype.card K = (r ^ e0) ^ 2 := by rw [← Nat.card_eq_fintype_card]; exact hK
  obtain ⟨k, rfl⟩ := hp
  have h1 := FiniteField.pow_card_pow k a
  rw [hcard] at h1
  have h2 : (r ^ e0) ^ (2 * k + 1) = ((r ^ e0) ^ 2) ^ k * r ^ e0 := by rw [pow_succ, pow_mul]
  rw [h2, pow_mul, h1]

theorem odIota_root (hp : Odd p) (hpq : p ∣ r ^ e0 + 1) (hc : c ^ (r ^ e0 + 1) = 1) :
    odIota K r e0 p c (AdjoinRoot.root (X ^ p - C c : K[X])) =
      (AdjoinRoot.root (X ^ p - C c : K[X]))⁻¹ := by
  set β := AdjoinRoot.root (X ^ p - C c : K[X]) with hβ
  have h1 : β ^ ((r ^ e0) ^ p + 1) = 1 := by
    obtain ⟨v, hv⟩ := od_pq_dvd hp hpq
    rw [hv, mul_assoc, pow_mul, hβ, odA_root_pow, ← map_pow, pow_mul, hc, one_pow, map_one]
  rw [odIota_apply]
  exact eq_inv_of_mul_eq_one_left (by rw [← pow_succ]; exact h1)

theorem od_exists_norm_eq (hK : Nat.card K = (r ^ e0) ^ 2)
    {ν : AdjoinRoot (X ^ p - C c : K[X])} (hν0 : ν ≠ 0) (hν : odIota K r e0 p c ν = ν) :
    ∃ e, odIota K r e0 p c e * e * ν = 1 := by
  set Q := (r ^ e0) ^ p with hQ
  have hq2 : 2 ≤ r ^ e0 := by
    by_contra h
    have h1 : r ^ e0 ≤ 1 := by omega
    have h2 : Nat.card K ≤ 1 := by rw [hK]; exact Nat.pow_le_one_iff (by norm_num) |>.2 h1
    have : 1 < Nat.card K := Finite.one_lt_card
    omega
  have hQ2 : 2 ≤ Q := le_trans hq2 (Nat.le_self_pow hpf.out.ne_zero _)
  have hcardA : Nat.card (AdjoinRoot (X ^ p - C c : K[X])) = Q ^ 2 := by
    rw [odA_card, hK, hQ, ← pow_mul, mul_comm, pow_mul]
  have hQν : ν ^ Q = ν := by rw [← odIota_apply]; exact hν
  have hν1 : ν ^ (Q - 1) = 1 := by
    refine mul_right_cancel₀ hν0 ?_
    rw [← pow_succ, Nat.sub_add_cancel (by omega), one_mul, hQν]
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := (AdjoinRoot (X ^ p - C c : K[X]))ˣ)
  obtain ⟨a, ha⟩ := Subgroup.mem_zpowers_iff.1 (hg (Units.mk0 ν hν0))
  have hord : orderOf g = Q ^ 2 - 1 := by
    rw [orderOf_eq_card_of_forall_mem_zpowers hg, Nat.card_units, hcardA]
  have h1 : g ^ (a * ((Q - 1 : ℕ) : ℤ)) = 1 := by
    rw [zpow_mul, ha]
    simpa using Units.ext (by simpa using hν1)
  have h2 : ((Q ^ 2 - 1 : ℕ) : ℤ) ∣ a * ((Q - 1 : ℕ) : ℤ) := by
    rw [← hord]
    exact orderOf_dvd_iff_zpow_eq_one.2 h1
  have hQ1 : ((Q - 1 : ℕ) : ℤ) = (Q : ℤ) - 1 := by push_cast [Nat.cast_sub (by omega : 1 ≤ Q)]; ring
  have hQsq : ((Q ^ 2 - 1 : ℕ) : ℤ) = ((Q : ℤ) - 1) * ((Q : ℤ) + 1) := by
    have : 1 ≤ Q ^ 2 := Nat.one_le_pow _ _ (by omega)
    push_cast [Nat.cast_sub this]
    ring
  rw [hQsq, hQ1] at h2
  obtain ⟨m, hm⟩ := h2
  have hne : (Q : ℤ) - 1 ≠ 0 := by
    have : (2 : ℤ) ≤ Q := by exact_mod_cast hQ2
    omega
  have ham : a = ((Q : ℤ) + 1) * m := by
    refine mul_right_cancel₀ hne ?_
    rw [hm]
    ring
  refine ⟨((g ^ (-m) : (AdjoinRoot (X ^ p - C c : K[X]))ˣ) : AdjoinRoot (X ^ p - C c : K[X])), ?_⟩
  have h3 : (g ^ (-m)) ^ (Q + 1) * Units.mk0 ν hν0 = 1 := by
    rw [← ha, ← zpow_natCast, ← zpow_mul, ← zpow_add]
    have : -m * ((Q + 1 : ℕ) : ℤ) + a = 0 := by rw [ham]; push_cast; ring
    rw [this, zpow_zero]
  have h4 := congrArg Units.val h3
  rw [odIota_apply, ← hQ, ← pow_succ]
  simpa using h4

end Iota

end I294OD

end CFSG.LocalAnalysis.RankFourTheoremC

module

public import CFSG.LocalAnalysis.GLTheoremA.PartI.KDOut.Tower
public import CFSG.Quasithin.Background.PSL2TwoNilpotent

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Quasithin.H13.Ch838 (TwoNilpotent)
open CFSG.ComponentClassification.OuterAutomorphisms (inner inner_normal Outer)

theorem mem_of_pow_eq_one_of_twoPower_mem {G : Type*} [Group G] {M : Subgroup G} {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) {x : G} {k j : ℕ} (hk : x ^ (p ^ k) = 1)
    (hj : x ^ (2 ^ j) ∈ M) : x ∈ M := by
  have hcop : Nat.Coprime (2 ^ j) (p ^ k) :=
    Nat.Coprime.pow j k ((Nat.coprime_primes Nat.prime_two hp).2 (Ne.symm hp2))
  obtain ⟨u, v, huv⟩ : IsCoprime ((2 ^ j : ℕ) : ℤ) ((p ^ k : ℕ) : ℤ) :=
    Nat.isCoprime_iff_coprime.2 hcop
  have hx : x = (x ^ (2 ^ j)) ^ u := by
    have h1 : (x ^ (p ^ k)) ^ v = 1 := by rw [hk, one_zpow]
    calc x = x ^ (u * ((2 ^ j : ℕ) : ℤ) + v * ((p ^ k : ℕ) : ℤ)) := by rw [huv, zpow_one]
      _ = (x ^ (2 ^ j)) ^ u * (x ^ (p ^ k)) ^ v := by
        rw [zpow_add, mul_comm u, mul_comm v, zpow_mul, zpow_mul, zpow_natCast, zpow_natCast]
      _ = (x ^ (2 ^ j)) ^ u := by rw [h1, mul_one]
  rw [hx]
  exact M.zpow_mem hj u

theorem outTwoTowerAt_of_twoNilpotent_outer {K : Type*} [Group K] {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (h : TwoNilpotent (Outer K)) : OutTwoTowerAt K p := by
  obtain ⟨M, hM, hodd, h2⟩ := h
  haveI : (inner K).Normal := inner_normal K
  let π : MulAut K →* Outer K := QuotientGroup.mk' (inner K)
  refine ⟨M.comap π, fun γ α ⟨k, hk⟩ => ?_, fun α _ δ hδ ⟨m, hm⟩ => ?_⟩
  · have hk' : π α ^ (p ^ k) = 1 := by rw [← map_pow, hk, map_one]
    obtain ⟨j, hj⟩ := h2 (π α)
    have hα : π α ∈ M := mem_of_pow_eq_one_of_twoPower_mem hp hp2 hk' hj
    change π (γ * α * γ⁻¹ * α⁻¹) ∈ M
    simp only [map_mul, map_inv]
    exact M.mul_mem (hM.conj_mem _ hα (π γ)) (M.inv_mem hα)
  · have hδM : π δ ∈ M := hδ
    have hm' : π δ ^ (2 ^ m) = 1 := by
      rw [← map_pow]
      exact (QuotientGroup.eq_one_iff _).2 hm
    have hcop : Nat.Coprime (2 ^ m) (Nat.card M) :=
      Nat.Coprime.pow_left m (Nat.coprime_two_left.2 hodd)
    have hord : orderOf (π δ) = 1 :=
      Nat.eq_one_of_dvd_coprimes hcop (orderOf_dvd_of_pow_eq_one hm')
        (by
          have := orderOf_dvd_natCard (⟨π δ, hδM⟩ : M)
          rwa [Subgroup.orderOf_mk] at this)
    have hδi : δ ∈ (inner K : Subgroup (MulAut K)) :=
      (QuotientGroup.eq_one_iff _).1 (orderOf_eq_one_iff.1 hord)
    exact (inner K).mul_mem ((inner_normal K).conj_mem δ hδi α) ((inner K).inv_mem hδi)

end CFSG.LocalAnalysis.GLTheoremA

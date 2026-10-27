module

public import CFSG.FeitThompson.Definitions.RawNormalPrimeSetCore

namespace CFSG.FeitThompson

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

variable {G : Type*} [Group G]

theorem conj_eq_self_of_isPGroup_closure_conj {p : ℕ} {N : Subgroup G} [hN : N.Normal]
    (hcop : (Nat.card N).Coprime p) {x : G}
    (hx : ∀ n ∈ N, IsPGroup p (Subgroup.closure ({x, n⁻¹ * x * n} : Set G)))
    {n : G} (hn : n ∈ N) : n⁻¹ * x * n = x := by
  set y := x⁻¹ * (n⁻¹ * x * n) with hy
  have h1 : x⁻¹ * n⁻¹ * x ∈ N := by
    have := hN.conj_mem n⁻¹ (N.inv_mem hn) x⁻¹
    simpa using this
  have hyN : y ∈ N := by
    have h2 : y = (x⁻¹ * n⁻¹ * x) * n := by rw [hy]; group
    rw [h2]; exact N.mul_mem h1 hn
  have hxC : x ∈ Subgroup.closure ({x, n⁻¹ * x * n} : Set G) := Subgroup.subset_closure (by simp)
  have hcC : n⁻¹ * x * n ∈ Subgroup.closure ({x, n⁻¹ * x * n} : Set G) :=
    Subgroup.subset_closure (by simp)
  have hyC : y ∈ Subgroup.closure ({x, n⁻¹ * x * n} : Set G) := mul_mem (inv_mem hxC) hcC
  obtain ⟨k, hk⟩ := (hx n hn).exists_orderOf_dvd_pow ⟨y, hyC⟩
  rw [Subgroup.orderOf_mk] at hk
  have hdvd : orderOf y ∣ Nat.card N := by
    have := orderOf_dvd_natCard (⟨y, hyN⟩ : N)
    rwa [Subgroup.orderOf_mk] at this
  have hone : orderOf y = 1 :=
    Nat.Coprime.eq_one_of_dvd ((hcop.symm.pow_left k).coprime_dvd_left hk) hdvd
  exact (inv_mul_eq_one.mp (orderOf_eq_one_iff.mp hone)).symm

theorem mem_centralizer_of_isPGroup_closure_conj {p : ℕ} {N : Subgroup G} [N.Normal]
    (hcop : (Nat.card N).Coprime p) {x : G}
    (hx : ∀ n ∈ N, IsPGroup p (Subgroup.closure ({x, n⁻¹ * x * n} : Set G))) :
    x ∈ Subgroup.centralizer (N : Set G) := by
  rw [Subgroup.mem_centralizer_iff]
  intro n hn
  have h := conj_eq_self_of_isPGroup_closure_conj hcop hx hn
  calc n * x = n * (n⁻¹ * x * n) := by rw [h]
    _ = x * n := by group

theorem le_centralizer_singleton_of_isPGroup_closure_conj {p : ℕ} {N : Subgroup G} [N.Normal]
    (hcop : (Nat.card N).Coprime p) {x : G}
    (hx : ∀ n ∈ N, IsPGroup p (Subgroup.closure ({x, n⁻¹ * x * n} : Set G))) :
    N ≤ Subgroup.centralizer ({x} : Set G) := by
  intro n hn
  rw [Subgroup.mem_centralizer_iff]
  rintro g rfl
  exact (Subgroup.mem_centralizer_iff.mp
    (mem_centralizer_of_isPGroup_closure_conj hcop hx) n hn).symm

theorem coprime_natCard_of_isPiSubgroup_compl [Finite G] {p : ℕ} (hp : p.Prime) {N : Subgroup G}
    (hN : IsPiSubgroup {q : ℕ | q.Prime ∧ q ≠ p} N) : (Nat.card N).Coprime p := by
  rw [isPiSubgroup_iff] at hN
  refine Nat.Coprime.symm ((Nat.Prime.coprime_iff_not_dvd hp).2 fun hdvd => ?_)
  exact (hN p (Nat.mem_primeFactors.2 ⟨hp, hdvd, Nat.card_pos.ne'⟩)).2 rfl

theorem mem_centralizer_of_isPiSubgroup_compl_of_isPGroup_closure_conj [Finite G] {p : ℕ}
    (hp : p.Prime) {N : Subgroup G} [N.Normal]
    (hN : IsPiSubgroup {q : ℕ | q.Prime ∧ q ≠ p} N) {x : G}
    (hx : ∀ n ∈ N, IsPGroup p (Subgroup.closure ({x, n⁻¹ * x * n} : Set G))) :
    x ∈ Subgroup.centralizer (N : Set G) :=
  mem_centralizer_of_isPGroup_closure_conj (coprime_natCard_of_isPiSubgroup_compl hp hN) hx

end

end CFSG.FeitThompson

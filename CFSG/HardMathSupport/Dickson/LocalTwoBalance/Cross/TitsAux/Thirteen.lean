module

public import Mathlib.GroupTheory.Sylow

public section

namespace CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.TitsAux

theorem no_order_thirteen_centralizes_card_twentyfive {G : Type*} [Group G] [Finite G]
    (hcard : Nat.card G = 17971200)
    (h2 : ∀ u y : G, orderOf u = 2 → orderOf y = 13 → u * y ≠ y * u)
    (h3 : ∀ x y : G, orderOf x = 3 → orderOf y = 13 → x * y ≠ y * x)
    {y : G} (hy : orderOf y = 13) {P : Subgroup G} (hP : Nat.card P = 25)
    (hPy : ∀ x ∈ P, x * y = y * x) : False := by
  have h13 : Fact (Nat.Prime 13) := ⟨by decide⟩
  set C : Subgroup G := Subgroup.centralizer ({y} : Set G) with hC
  have hPC : P ≤ C := fun x hx => Subgroup.mem_centralizer_singleton_iff.2 (hPy x hx)
  have hyC : y ∈ C := Subgroup.mem_centralizer_singleton_iff.2 rfl
  have h25 : 25 ∣ Nat.card C := hP ▸ Subgroup.card_dvd_of_le hPC
  have h13C : 13 ∣ Nat.card C := by
    have := orderOf_dvd_natCard (⟨y, hyC⟩ : C)
    rwa [Subgroup.orderOf_mk, hy] at this
  have h325 : 325 ∣ Nat.card C := by
    have hco : Nat.Coprime 25 13 := by norm_num
    simpa using hco.mul_dvd_of_dvd_of_dvd h25 h13C
  have hdvd : Nat.card C ∣ 17971200 := hcard ▸ Subgroup.card_subgroup_dvd_card C
  have hn2 : ¬ 2 ∣ Nat.card C := by
    intro h
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    obtain ⟨u, hu⟩ := exists_prime_orderOf_dvd_card' 2 h
    exact h2 (u : G) y (by rw [Subgroup.orderOf_coe]; exact hu) hy
      (Subgroup.mem_centralizer_singleton_iff.1 u.2)
  have hn3 : ¬ 3 ∣ Nat.card C := by
    intro h
    haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    obtain ⟨u, hu⟩ := exists_prime_orderOf_dvd_card' 3 h
    exact h3 (u : G) y (by rw [Subgroup.orderOf_coe]; exact hu) hy
      (Subgroup.mem_centralizer_singleton_iff.1 u.2)
  have hC325 : Nat.card C = 325 := by
    obtain ⟨m, hm⟩ := h325
    have hm' : m ∣ 2 ^ 11 * 3 ^ 3 := by
      rw [hm, show (17971200 : ℕ) = 325 * (2 ^ 11 * 3 ^ 3) by norm_num] at hdvd
      exact Nat.dvd_of_mul_dvd_mul_left (by norm_num) hdvd
    have hm2 : ¬ 2 ∣ m := fun h => hn2 (hm ▸ h.mul_left 325)
    have hm3 : ¬ 3 ∣ m := fun h => hn3 (hm ▸ h.mul_left 325)
    have hc2 : Nat.Coprime m (2 ^ 11) :=
      Nat.Coprime.pow_right 11 ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).2 hm2).symm
    have hc3 : Nat.Coprime m (3 ^ 3) :=
      Nat.Coprime.pow_right 3 ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).2 hm3).symm
    have hm1 : m = 1 := (hc2.mul_right hc3).eq_one_of_dvd hm'
    rw [hm, hm1]
  set Q : Subgroup G := Subgroup.zpowers y with hQ
  have hQcard : Nat.card Q = 13 := by rw [hQ, Nat.card_zpowers, hy]
  have hQp : IsPGroup 13 Q := IsPGroup.of_card (n := 1) (by rw [hQcard, pow_one])
  have hQidx : ¬ 13 ∣ Q.index := by
    have h := Subgroup.card_mul_index Q
    rw [hQcard, hcard] at h
    have : Q.index = 1382400 := by omega
    rw [this]
    norm_num
  have hS : (hQp.toSylow hQidx : Subgroup G) = Q := IsPGroup.toSylow_coe _ _
  have hmod : Nat.card (Sylow 13 G) ≡ 1 [MOD 13] := card_sylow_modEq_one 13 G
  set N : Subgroup G := Subgroup.normalizer (Q : Set G) with hN
  have hindex : Nat.card (Sylow 13 G) = N.index := by
    rw [Sylow.card_eq_index_normalizer (hQp.toSylow hQidx)]
    exact congrArg (fun H : Subgroup G => (Subgroup.normalizer (H : Set G)).index) hS
  have hCQ : Subgroup.centralizer (Q : Set G) = C := by
    refine le_antisymm (fun x hx => ?_) (fun x hx => ?_)
    · exact Subgroup.mem_centralizer_iff.2 fun z hz => by
        rw [Set.mem_singleton_iff.1 hz]
        exact Subgroup.mem_centralizer_iff.1 hx y (Subgroup.mem_zpowers y)
    · refine Subgroup.mem_centralizer_iff.2 fun z hz => ?_
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hz
      have hxy : Commute y x := (Subgroup.mem_centralizer_singleton_iff.1 hx).symm
      exact (hxy.zpow_left k).eq
  have hCN : C ≤ N := by
    rw [← hCQ]
    exact Subgroup.centralizer_le_normalizer _
  have hrel : C.relIndex N ∣ 12 := by
    have key := Subgroup.card_dvd_of_injective _
      (QuotientGroup.kerLift_injective Q.normalizerMonoidHom)
    rw [Subgroup.normalizerMonoidHom_ker, ← Subgroup.index, ← Subgroup.relIndex, hCQ] at key
    have hcyc : Nat.card (MulAut Q) = 12 := by
      rw [IsCyclic.card_mulAut, hQcard, Nat.totient_prime h13.out]
    rwa [hcyc] at key
  have hNcard : Nat.card N = 325 * C.relIndex N := by
    have h := Subgroup.card_mul_index (C.subgroupOf N)
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hCN).toEquiv, hC325] at h
    exact h.symm
  have hGN := Subgroup.card_mul_index N
  rw [hNcard, hcard] at hGN
  have hn : N.index % 13 = 1 := by
    have := hindex ▸ hmod
    exact this
  have hr : C.relIndex N ≤ 12 := Nat.le_of_dvd (by norm_num) hrel
  generalize C.relIndex N = r at hr hGN
  interval_cases r <;> omega

end CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.TitsAux

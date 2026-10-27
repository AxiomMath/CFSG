module

public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesL630Setup

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L630.I2026

open CFSG.Open

variable {G : Type} [Group G] [Finite G]

theorem normal_subgroupOf_of_le_center {N X : Subgroup G} (hN : N ≤ Subgroup.center G) :
    (N.subgroupOf X).Normal :=
  ⟨fun n hn g => by
    have hn' : (n : G) ∈ N := hn
    show ((g * n * g⁻¹ : ↥X) : G) ∈ N
    have h1 := Subgroup.mem_center_iff.mp (hN hn') (g : G)
    have h2 : ((g * n * g⁻¹ : ↥X) : G) = (n : G) := by
      show (g : G) * (n : G) * (g : G)⁻¹ = (n : G)
      rw [h1]
      group
    rw [h2]
    exact hn'⟩

theorem conj_mem_of_normal_subgroupOf {N X : Subgroup G} (hNX : N ≤ X)
    (hN : (N.subgroupOf X).Normal) : ∀ x ∈ X, ∀ n ∈ N, x * n * x⁻¹ ∈ N := by
  intro x hx n hn
  exact Subgroup.mem_subgroupOf.mp
    (hN.conj_mem ⟨n, hNX hn⟩ (Subgroup.mem_subgroupOf.mpr hn) ⟨x, hx⟩)

theorem commute_core_pcore (X : Subgroup G) :
    ∀ n ∈ rankThreePrimeCore 2 X, ∀ t ∈ pCoreOf 2 X, n * t = t * n := by
  intro n hn t ht
  have hNX : rankThreePrimeCore 2 X ≤ X := rankThreePrimeCore_le_self 2 X
  have hTX : pCoreOf 2 X ≤ X := pCoreOf_le_self 2 X
  have hNc := conj_mem_of_normal_subgroupOf hNX
    (rankThreePrimeCore_subgroupOf_normal Nat.prime_two X)
  have hTc := conj_mem_of_normal_subgroupOf hTX (pCoreOf_subgroupOf_normal 2 X)
  have h1 : n * t * n⁻¹ * t⁻¹ ∈ pCoreOf 2 X :=
    (pCoreOf 2 X).mul_mem (hTc n (hNX hn) t ht) ((pCoreOf 2 X).inv_mem ht)
  have h2 : n * t * n⁻¹ * t⁻¹ ∈ rankThreePrimeCore 2 X := by
    have : n * t * n⁻¹ * t⁻¹ = n * (t * n⁻¹ * t⁻¹) := by group
    rw [this]
    exact (rankThreePrimeCore 2 X).mul_mem hn
      (hNc t (hTX ht) n⁻¹ ((rankThreePrimeCore 2 X).inv_mem hn))
  have hodd : Nat.Coprime 2 (Nat.card (rankThreePrimeCore 2 X)) :=
    CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimple.coprime_card_relPPrimeCore
      Nat.prime_two X
  have hd1 : orderOf (n * t * n⁻¹ * t⁻¹) ∣ Nat.card (rankThreePrimeCore 2 X) := by
    have := Subgroup.orderOf_dvd_natCard (rankThreePrimeCore 2 X) h2
    exact this
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hpg : ∀ g : ↥(pCoreOf 2 X), ∃ k : ℕ, orderOf g = 2 ^ k :=
    IsPGroup.iff_orderOf.mp (pCoreOf_isPGroup 2 X)
  obtain ⟨k, hk⟩ := hpg ⟨n * t * n⁻¹ * t⁻¹, h1⟩
  have hk' : orderOf (n * t * n⁻¹ * t⁻¹) = 2 ^ k := by
    rw [← hk]
    exact Subgroup.orderOf_coe (⟨n * t * n⁻¹ * t⁻¹, h1⟩ : ↥(pCoreOf 2 X))
  have hcop : Nat.Coprime (2 ^ k) (Nat.card (rankThreePrimeCore 2 X)) :=
    Nat.Coprime.pow_left k hodd
  have hone : orderOf (n * t * n⁻¹ * t⁻¹) = 1 := by
    rw [hk'] at hd1 ⊢
    exact Nat.Coprime.eq_one_of_dvd hcop hd1
  have h3 : n * t * n⁻¹ * t⁻¹ = 1 := orderOf_eq_one_iff.mp hone
  calc n * t = n * t * n⁻¹ * t⁻¹ * (t * n) := by group
    _ = t * n := by rw [h3, one_mul]

theorem center_le_core (X : Subgroup G) {c : G} (hc : c ∈ Subgroup.center G) (hcX : c ∈ X) :
    c ∈ rankThreePrimeCore 2 X ⊔ pCoreOf 2 X := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hc0 : orderOf c ≠ 0 := (orderOf_pos c).ne'
  obtain ⟨a, m, hm, hgam⟩ := Nat.exists_eq_two_pow_mul_odd hc0
  have hcop : Nat.Coprime (2 ^ a) m := Nat.Coprime.pow_left a (Nat.coprime_two_left.mpr hm)
  have hbez : (1 : ℤ) = (m : ℤ) * Nat.gcdA m (2 ^ a) + (2 ^ a : ℕ) * Nat.gcdB m (2 ^ a) := by
    have := Nat.gcd_eq_gcd_ab m (2 ^ a)
    rw [Nat.Coprime.symm hcop |>.gcd_eq_one] at this
    exact_mod_cast this
  have hcz : ∀ k : ℤ, c ^ k ∈ Subgroup.center G := fun k => Subgroup.zpow_mem _ hc k
  have hcz' : ∀ k : ℕ, c ^ k ∈ Subgroup.center G := fun k => Subgroup.pow_mem _ hc k
  have hT : Subgroup.zpowers (c ^ m) ≤ pCoreOf 2 X := by
    apply le_pCoreOf
    · rw [Subgroup.zpowers_le]
      exact Subgroup.pow_mem _ hcX m
    · exact normal_subgroupOf_of_le_center (by rw [Subgroup.zpowers_le]; exact hcz' m)
    · apply IsPGroup.of_card_dvd_pow (n := a)
      rw [Nat.card_zpowers]
      apply orderOf_dvd_of_pow_eq_one
      rw [← pow_mul, mul_comm, ← hgam]
      exact pow_orderOf_eq_one c
  have hN : Subgroup.zpowers (c ^ (2 ^ a)) ≤ rankThreePrimeCore 2 X := by
    apply le_sSup
    refine ⟨?_, normal_subgroupOf_of_le_center (by rw [Subgroup.zpowers_le]; exact hcz' _), ?_⟩
    · rw [Subgroup.zpowers_le]
      exact Subgroup.pow_mem _ hcX _
    · rw [Nat.card_zpowers]
      have hd : orderOf (c ^ (2 ^ a)) ∣ m := by
        apply orderOf_dvd_of_pow_eq_one
        rw [← pow_mul, ← hgam]
        exact pow_orderOf_eq_one c
      exact Nat.Coprime.coprime_dvd_right hd (Nat.coprime_two_left.mpr hm)
  have hcdec : c = (c ^ m) ^ (Nat.gcdA m (2 ^ a)) * (c ^ (2 ^ a)) ^ (Nat.gcdB m (2 ^ a)) := by
    rw [← zpow_natCast, ← zpow_natCast, ← zpow_mul, ← zpow_mul, ← zpow_add]
    have : (m : ℤ) * Nat.gcdA m (2 ^ a) + ((2 ^ a : ℕ) : ℤ) * Nat.gcdB m (2 ^ a) = 1 := hbez.symm
    rw [this, zpow_one]
  rw [hcdec, sup_comm]
  exact Subgroup.mul_mem_sup (hT (Subgroup.zpow_mem_zpowers _ _))
    (hN (Subgroup.zpow_mem_zpowers _ _))

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L630.I2026

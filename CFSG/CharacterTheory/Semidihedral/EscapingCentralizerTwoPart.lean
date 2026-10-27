module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PCore.PPrimeCore
public import CFSG.LinearAlgebra.LinearGroups.CyclicSylowIndexTwo

public section

namespace CFSG.Semidihedral.EscapingCentralizer

universe u

variable {K : Type u} [Group K]

theorem eq_one_or_eq_of_mem_zpowers_of_orderOf_eq_two {g x : K} (hg : orderOf g = 2)
    (hx : x ∈ Subgroup.zpowers g) : x = 1 ∨ x = g := by
  obtain ⟨m, rfl⟩ := hx
  change g ^ m = 1 ∨ g ^ m = g
  rw [← zpow_mod_orderOf, hg]
  rcases Int.emod_two_eq_zero_or_one m with h | h
  · left
    rw [Nat.cast_ofNat, h, zpow_zero]
  · right
    rw [Nat.cast_ofNat, h, zpow_one]

variable [Finite K]

theorem sylow_two_card_eq_two_of_no_centralizing_four (i : K) (hi : orderOf i = 2)
    (hC : ∀ Q : Subgroup K, Nat.card Q = 4 → ¬ Q ≤ Subgroup.centralizer ({i} : Set K)) :
    ∀ S : Sylow 2 K, Nat.card (S : Subgroup K) = 2 := by
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hZi : IsPGroup 2 (Subgroup.zpowers i) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hi, pow_one])
  obtain ⟨S, hiS⟩ := hZi.exists_le_sylow
  have hiS' : i ∈ (S : Subgroup K) := hiS (Subgroup.mem_zpowers i)
  let CS := (S : Subgroup K) ⊓ Subgroup.centralizer ({i} : Set K)
  have hCSp : IsPGroup 2 CS := S.isPGroup'.to_le inf_le_left
  have hiCS : i ∈ CS := ⟨hiS', Subgroup.mem_centralizer_singleton_iff.mpr rfl⟩
  have hi1 : i ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hi
    exact absurd hi (by decide)
  obtain ⟨k, hk⟩ := hCSp.exists_card_eq
  have hk1 : k ≤ 1 := by
    by_contra hk1
    have h4 : 2 ^ 2 ∣ Nat.card CS := hk ▸ pow_dvd_pow 2 (by omega)
    obtain ⟨Q, hQ⟩ := Sylow.exists_subgroup_card_pow_prime 2 h4
    apply hC (Q.map CS.subtype)
    · rw [Subgroup.card_map_of_injective CS.subtype_injective, hQ]
      norm_num
    · exact (Subgroup.map_subtype_le Q).trans inf_le_right
  have hZle : Subgroup.zpowers i ≤ CS := Subgroup.zpowers_le.mpr hiCS
  have h2 : 2 ∣ Nat.card CS := by
    have h := Subgroup.card_dvd_of_le hZle
    rwa [Nat.card_zpowers, hi] at h
  have hCScard : Nat.card CS = 2 := by
    interval_cases k
    · rw [hk, pow_zero] at h2
      exact absurd h2 (by decide)
    · rw [hk, pow_one]
  have hCSeq : Subgroup.zpowers i = CS :=
    Subgroup.eq_of_le_of_card_ge hZle (by rw [hCScard, Nat.card_zpowers, hi])
  let : Nontrivial (S : Subgroup K) :=
    ⟨⟨⟨i, hiS'⟩, 1, fun h => hi1 (congrArg Subtype.val h)⟩⟩
  have hcenter := S.isPGroup'.center_nontrivial
  obtain ⟨c, hc⟩ := exists_ne (1 : Subgroup.center (S : Subgroup K))
  have hcCS : ((c : (S : Subgroup K)) : K) ∈ CS := by
    refine ⟨(c : (S : Subgroup K)).property, ?_⟩
    apply Subgroup.mem_centralizer_singleton_iff.mpr
    have h := Subgroup.mem_center_iff.mp c.property ⟨i, hiS'⟩
    exact (congrArg Subtype.val h).symm
  rw [← hCSeq] at hcCS
  have hci : ((c : (S : Subgroup K)) : K) = i := by
    rcases eq_one_or_eq_of_mem_zpowers_of_orderOf_eq_two hi hcCS with h | h
    · exact absurd (Subtype.ext (Subtype.ext h)) hc
    · exact h
  have hSC : (S : Subgroup K) ≤ CS := by
    intro x hx
    refine ⟨hx, ?_⟩
    apply Subgroup.mem_centralizer_singleton_iff.mpr
    have h := Subgroup.mem_center_iff.mp c.property ⟨x, hx⟩
    have h' : x * ((c : (S : Subgroup K)) : K) = ((c : (S : Subgroup K)) : K) * x :=
      congrArg Subtype.val h
    rw [hci] at h'
    exact h'
  have hScard : Nat.card (S : Subgroup K) = 2 := by
    apply le_antisymm
    · exact (Nat.le_of_dvd Nat.card_pos (Subgroup.card_dvd_of_le hSC)).trans hCScard.le
    · have h := Subgroup.card_dvd_of_le (hiS.trans le_rfl)
      rw [Nat.card_zpowers, hi] at h
      exact Nat.le_of_dvd Nat.card_pos h
  intro S'
  rw [Sylow.card_eq_multiplicity S', ← Sylow.card_eq_multiplicity S, hScard]

theorem odd_core_index_two_of_sylow_two_card_two (S : Sylow 2 K)
    (hS : Nat.card (S : Subgroup K) = 2) :
    (Nat.card K).factorization 2 = 1 ∧
      ∃ M : Subgroup K, M.Normal ∧ Odd (Nat.card M) ∧ M.index = 2 ∧
        M = CFSG.pPrimeCore 2 K := by
  classical
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let : Fintype K := Fintype.ofFinite K
  have hfac : (Nat.card K).factorization 2 = 1 := by
    have h := Sylow.card_eq_multiplicity S
    rw [hS] at h
    exact Nat.pow_right_injective le_rfl (h.symm.trans (pow_one 2).symm)
  have hcardK : Nat.card K = 2 * (S : Subgroup K).index := by
    have h := Subgroup.card_mul_index (S : Subgroup K)
    rw [hS] at h
    exact h.symm
  have hindexodd : Odd (S : Subgroup K).index :=
    Nat.odd_iff.mpr (Nat.two_dvd_ne_zero.mp S.not_dvd_index)
  have heven : Even (Fintype.card K) := by
    rw [← Nat.card_eq_fintype_card, hcardK]
    exact even_two_mul _
  have hcyc : IsCyclic (S : Subgroup K) := isCyclic_of_prime_card (p := 2) hS
  obtain ⟨-, -, hnormal, hindex⟩ := CFSG.LinearGroups.cyclic_sylow_index_two heven S hcyc
  let M := (Equiv.Perm.sign.comp (MulAction.toPermHom K K)).ker
  have hMcard : Nat.card M = (S : Subgroup K).index := by
    have h := Subgroup.card_mul_index M
    rw [hindex, hcardK] at h
    omega
  have hModd : Odd (Nat.card M) := hMcard ▸ hindexodd
  have hMle : M ≤ CFSG.pPrimeCore 2 K := le_sSup ⟨hnormal, Nat.coprime_two_left.mpr hModd⟩
  have hOodd : Odd (Nat.card (CFSG.pPrimeCore 2 K)) :=
    Nat.coprime_two_left.mp (CFSG.pPrimeCore_coprime_card (p := 2) (G := K))
  have hOdvd : Nat.card (CFSG.pPrimeCore 2 K) ∣ Nat.card M := by
    have h := Subgroup.card_subgroup_dvd_card (CFSG.pPrimeCore 2 K)
    rw [hcardK, ← hMcard] at h
    exact (Nat.coprime_two_right.mpr hOodd).dvd_of_dvd_mul_left h
  have heq : M = CFSG.pPrimeCore 2 K :=
    Subgroup.eq_of_le_of_card_ge hMle (Nat.le_of_dvd Nat.card_pos hOdvd)
  exact ⟨hfac, M, hnormal, hModd, hindex, heq⟩

end CFSG.Semidihedral.EscapingCentralizer

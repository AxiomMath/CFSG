module

public import CFSG.GroupTheory.ABGLocalTools.Basic

public section

namespace CFSG.GroupTheory

open Subgroup

variable {G : Type*} [Group G] [Finite G]

theorem relIndex_eq_of_isSylow_two {B C T Q : Subgroup G} {k : ℕ}
    (hCB : C ≤ B) (hQC : Q ≤ C) (hTB : T ≤ B) (hQT : Q ≤ T)
    (hQp : IsPGroup 2 Q)
    (hk : C.relIndex B = 2 ^ k) (hodd : Odd (Q.relIndex C))
    (hTsyl : CFSG.ABGLocalTools.IsSylowOf 2 T B) :
    Q.relIndex T = 2 ^ k ∧ Q.relIndex C = T.relIndex B := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hB1 : Nat.card B = 2 ^ k * Nat.card C := by
    have h := Subgroup.relIndex_mul_card C B
    rw [inf_eq_left.mpr hCB, hk] at h
    exact h.symm
  have hC1 : Nat.card C = Q.relIndex C * Nat.card Q := by
    have h := Subgroup.relIndex_mul_card Q C
    rw [inf_eq_left.mpr hQC] at h
    exact h.symm
  have hT1 : Nat.card T = Q.relIndex T * Nat.card Q := by
    have h := Subgroup.relIndex_mul_card Q T
    rw [inf_eq_left.mpr hQT] at h
    exact h.symm
  have hQTne : Q.relIndex T ≠ 0 := by
    intro h0
    rw [h0, zero_mul] at hT1
    exact Nat.card_pos.ne' hT1
  have hB2 : Nat.card B = T.relIndex B * Nat.card T := by
    have h := Subgroup.relIndex_mul_card T B
    rw [inf_eq_left.mpr hTB] at h
    exact h.symm
  have hQne : Nat.card Q ≠ 0 := Nat.card_pos.ne'
  have hQCne : Q.relIndex C ≠ 0 := by
    intro h0
    rw [h0, zero_mul] at hC1
    exact Nat.card_pos.ne' hC1
  have hCne : Nat.card C ≠ 0 := Nat.card_pos.ne'
  have hnotdvd : ¬ 2 ∣ Q.relIndex C := by
    obtain ⟨m, hm⟩ := hodd
    rintro ⟨c, hc⟩
    omega
  have hfacB : (Nat.card B).factorization 2 = k + (Nat.card C).factorization 2 := by
    rw [hB1, Nat.factorization_mul (by positivity) hCne]
    show (2 ^ k).factorization 2 + (Nat.card C).factorization 2 =
      k + (Nat.card C).factorization 2
    rw [Nat.factorization_pow_self Nat.prime_two]
  have hfacC : (Nat.card C).factorization 2 = (Nat.card Q).factorization 2 := by
    rw [hC1, Nat.factorization_mul hQCne hQne]
    show (Q.relIndex C).factorization 2 + (Nat.card Q).factorization 2 =
      (Nat.card Q).factorization 2
    rw [Nat.factorization_eq_zero_of_not_dvd hnotdvd, zero_add]
  have hcardQ : Nat.card Q = 2 ^ (Nat.card Q).factorization 2 := by
    obtain ⟨n, hn⟩ := (IsPGroup.iff_card (p := 2) (G := ↥Q)).mp hQp
    rw [hn, Nat.factorization_pow_self Nat.prime_two]
  have hcardT : Nat.card T = 2 ^ (Nat.card B).factorization 2 := hTsyl.card_eq
  have hfacT : (Nat.card T).factorization 2 =
      (Q.relIndex T).factorization 2 + (Nat.card Q).factorization 2 := by
    rw [hT1, Nat.factorization_mul hQTne hQne]
    show (Q.relIndex T).factorization 2 + (Nat.card Q).factorization 2 =
      (Q.relIndex T).factorization 2 + (Nat.card Q).factorization 2
    rfl
  have hm : (Nat.card B).factorization 2 = (Nat.card T).factorization 2 := by
    rw [hcardT, Nat.factorization_pow_self Nat.prime_two]
  have hkfac : (Q.relIndex T).factorization 2 = k := by omega
  have hidx : (Q.subgroupOf T).index = Q.relIndex T := by
    rw [← Subgroup.relIndex_top_right (Q.subgroupOf T), ← Subgroup.subgroupOf_self T]
    exact Subgroup.relIndex_subgroupOf (le_refl T)
  have hTp : IsPGroup 2 ↥T := hTsyl.isPGroup
  obtain ⟨j, hj⟩ := hTp.index (Q.subgroupOf T)
  have hQidx : Q.relIndex T = 2 ^ j := by rw [← hidx, hj]
  have hjk : j = k := by
    rw [hQidx, Nat.factorization_pow_self Nat.prime_two] at hkfac
    omega
  refine ⟨by rw [hQidx, hjk], ?_⟩
  have hkey : 2 ^ k * Nat.card C = T.relIndex B * (2 ^ k * Nat.card Q) := by
    rw [← hB1, hB2, hT1, hQidx, hjk]
  have hkey' : 2 ^ k * Nat.card C = 2 ^ k * (T.relIndex B * Nat.card Q) := by
    rw [hkey]; ring
  have h2 : Nat.card C = T.relIndex B * Nat.card Q :=
    Nat.eq_of_mul_eq_mul_left (by positivity) hkey'
  have h3 : Q.relIndex C * Nat.card Q = T.relIndex B * Nat.card Q := by
    rw [← hC1, h2]
  exact Nat.eq_of_mul_eq_mul_right (Nat.card_pos) h3

end CFSG.GroupTheory

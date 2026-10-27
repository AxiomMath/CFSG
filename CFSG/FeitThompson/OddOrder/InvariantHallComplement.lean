module

public import Mathlib.GroupTheory.Complement
public import Mathlib.GroupTheory.Solvable
public import CFSG.FeitThompson.Foundations.HallContainsNormalPrimeSupport
import CFSG.FeitThompson.Foundations.PiSubgroupInHallSolvable
import CFSG.FeitThompson.OddOrder.FrobeniusKernelContainsRoots

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

open Pointwise

namespace CFSG.FeitThompson

variable {M : Type*} [Group M]

theorem isPiNumber_compl_primeFactors_iff_coprime {m n : ℕ} (hm : m ≠ 0) (hn : n ≠ 0) :
    IsPiNumber (↑m.primeFactors : Set ℕ)ᶜ n ↔ Nat.Coprime n m := by
  rw [← Nat.disjoint_primeFactors hn hm, Finset.disjoint_left, isPiNumber_compl_iff]
  simp

theorem exists_isComplement'_le_of_coprime [Finite M] [Group.IsSolvable M] {H K : Subgroup M}
    [H.Normal] (hH : Nat.Coprime (Nat.card H) H.index)
    (hK : Nat.Coprime (Nat.card H) (Nat.card K)) :
    ∃ L : Subgroup M, K ≤ L ∧ H.IsComplement' L := by
  have hcardH0 : Nat.card H ≠ 0 := Nat.card_pos.ne'
  set σ : Set ℕ := (↑(Nat.card H).primeFactors : Set ℕ)
  have hKπ : IsPiNumber σᶜ (Nat.card K) :=
    (isPiNumber_compl_primeFactors_iff_coprime hcardH0 Nat.card_pos.ne').2 hK.symm
  obtain ⟨L, hL, hKL⟩ := exists_isHallSubgroup_ge (π := σᶜ) hKπ
  refine ⟨L, hKL, ?_⟩
  have hcopHL : Nat.Coprime (Nat.card H) (Nat.card L) :=
    ((isPiNumber_compl_primeFactors_iff_coprime hcardH0 Nat.card_pos.ne').1 hL.natCard).symm
  have hHdvd : Nat.card H ∣ L.index := by
    refine hcopHL.dvd_of_dvd_mul_left ?_
    rw [Subgroup.card_mul_index L]
    exact Subgroup.card_subgroup_dvd_card H
  have hLindexdvd : L.index ∣ Nat.card H := by
    have hLσ : IsPiNumber σ L.index := by simpa using hL.index
    have hHiσ' : IsPiNumber σᶜ H.index :=
      (isPiNumber_compl_primeFactors_iff_coprime hcardH0 Subgroup.index_ne_zero_of_finite).2 hH.symm
    have hcop : Nat.Coprime L.index H.index :=
      hLσ.coprime_of_compl hHiσ' Subgroup.index_ne_zero_of_finite Subgroup.index_ne_zero_of_finite
    refine hcop.dvd_of_dvd_mul_right ?_
    rw [Subgroup.card_mul_index H]
    exact Subgroup.index_dvd_card L
  have hLindex : L.index = Nat.card H := Nat.dvd_antisymm hLindexdvd hHdvd
  have hdisjHL : Disjoint H L := by
    rw [disjoint_iff, ← Subgroup.card_eq_one]
    have hd : Nat.card (H ⊓ L : Subgroup M) ∣ Nat.gcd (Nat.card H) (Nat.card L) :=
      Nat.dvd_gcd (Subgroup.card_dvd_of_le inf_le_left) (Subgroup.card_dvd_of_le inf_le_right)
    exact Nat.eq_one_of_dvd_one (hcopHL ▸ hd)
  refine Subgroup.isComplement'_of_card_mul_and_disjoint ?_ hdisjHL
  have h := Subgroup.card_mul_index L
  rw [hLindex, mul_comm] at h
  exact h

theorem exists_invariant_complement_of_coprime
    [Finite M] [Group.IsSolvable M] {S K H : Subgroup M} [S.Normal] [H.Normal]
    (hSmul : (S : Set M) * (K : Set M) = Set.univ) (hSK : S ⊓ K = ⊥)
    (hS : Nat.Coprime (Nat.card S) S.index)
    (hHS : H ≤ S) (hH : Nat.Coprime (Nat.card H) (H.relIndex S)) :
    ∃ E : Subgroup M, E ≤ S ∧ (H : Set M) * (E : Set M) = (S : Set M) ∧ H ⊓ E = ⊥ ∧
      K ≤ Subgroup.normalizer (E : Set M) := by
  have hcompSK : S.IsComplement' K :=
    Subgroup.isComplement'_of_disjoint_and_mul_eq_univ (disjoint_iff.2 hSK) hSmul
  have hKindex : Nat.card K = S.index :=
    Nat.eq_of_mul_eq_mul_left Nat.card_pos
      (hcompSK.card_mul_card.trans (Subgroup.card_mul_index S).symm)
  have hcopHS : Nat.Coprime (Nat.card H) S.index :=
    Nat.Coprime.coprime_dvd_left (Subgroup.card_dvd_of_le hHS) hS
  have hcopHK : Nat.Coprime (Nat.card H) (Nat.card K) := by rw [hKindex]; exact hcopHS
  have hcopHindex : Nat.Coprime (Nat.card H) H.index := by
    rw [← Subgroup.relIndex_mul_index hHS]
    exact Nat.Coprime.mul_right hH hcopHS
  obtain ⟨L, hKL, hcompHL⟩ := exists_isComplement'_le_of_coprime hcopHindex hcopHK
  have hHLuniv : (H : Set M) * (L : Set M) = Set.univ := hcompHL.mul_eq
  refine ⟨S ⊓ L, inf_le_left, ?_, ?_, ?_⟩
  ·
    ext s
    refine ⟨fun ⟨h, hh, e, he, hs⟩ => hs ▸ S.mul_mem (hHS hh) he.1, fun hs => ?_⟩
    have hmem : s ∈ (H : Set M) * (L : Set M) := by rw [hHLuniv]; trivial
    obtain ⟨h, hh, l, hl, rfl⟩ := hmem
    refine ⟨h, hh, l, ⟨?_, hl⟩, rfl⟩
    simpa using S.mul_mem (S.inv_mem (hHS hh)) hs
  · rw [← inf_assoc, inf_eq_left.2 hHS, disjoint_iff.1 hcompHL.disjoint]
  ·
    intro k hk
    rw [Subgroup.mem_normalizer_iff]
    have hkL : k ∈ L := hKL hk
    intro x
    simp only [Subgroup.mem_inf]
    refine ⟨fun hx => ⟨‹S.Normal›.conj_mem x hx.1 k,
      L.mul_mem (L.mul_mem hkL hx.2) (L.inv_mem hkL)⟩, fun hx => ⟨?_, ?_⟩⟩
    · simpa [mul_assoc] using ‹S.Normal›.conj_mem _ hx.1 k⁻¹
    · simpa [mul_assoc] using L.mul_mem (L.mul_mem (L.inv_mem hkL) hx.2) hkL

theorem conj_smul_eq_self_of_mem_normalizer {E : Subgroup M} {k : M}
    (hk : k ∈ Subgroup.normalizer (E : Set M)) : MulAut.conj k • E = E := by
  ext x
  rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem]
  simp only [MulAut.smul_def, MulAut.conj_inv_apply]
  rw [Subgroup.mem_normalizer_iff.1 hk (k⁻¹ * x * k)]
  group

theorem exists_invariant_complement_sup_of_coprime
    [Finite M] [Group.IsSolvable M] {S K H : Subgroup M} [S.Normal] [H.Normal]
    (hSmul : (S : Set M) * (K : Set M) = Set.univ) (hSK : S ⊓ K = ⊥)
    (hS : Nat.Coprime (Nat.card S) S.index)
    (hHS : H ≤ S) (hH : Nat.Coprime (Nat.card H) (H.relIndex S)) :
    ∃ E : Subgroup M, E ≤ S ∧ H ⊔ E = S ∧ H ⊓ E = ⊥ ∧ ∀ k ∈ K, MulAut.conj k • E = E := by
  obtain ⟨E, hES, hmul, hdisj, hnorm⟩ :=
    exists_invariant_complement_of_coprime hSmul hSK hS hHS hH
  exact ⟨E, hES, SetLike.coe_injective ((Subgroup.normal_mul H E).trans hmul), hdisj,
    fun k hk => conj_smul_eq_self_of_mem_normalizer (hnorm hk)⟩

theorem exists_invariant_isComplement'_subgroupOf_of_coprime
    [Finite M] [Group.IsSolvable M] {S K H : Subgroup M} [S.Normal] [H.Normal]
    (hSmul : (S : Set M) * (K : Set M) = Set.univ) (hSK : S ⊓ K = ⊥)
    (hS : Nat.Coprime (Nat.card S) S.index)
    (hHS : H ≤ S) (hH : Nat.Coprime (Nat.card H) (H.relIndex S)) :
    ∃ E : Subgroup M, E ≤ S ∧ (H.subgroupOf S).IsComplement' (E.subgroupOf S) ∧
      K ≤ Subgroup.normalizer (E : Set M) := by
  obtain ⟨E, hES, hmul, hdisj, hnorm⟩ :=
    exists_invariant_complement_of_coprime hSmul hSK hS hHS hH
  exact ⟨E, hES, isComplement'_subgroupOf_of_coe_mul_coe_eq hmul hdisj, hnorm⟩

end CFSG.FeitThompson


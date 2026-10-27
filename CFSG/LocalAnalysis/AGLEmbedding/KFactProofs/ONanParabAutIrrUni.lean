module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanParabAutIrrIso
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryDiagonalOuterOrder
public import CFSG.RankThree.PartOne.S11d.OutAbstract

public section

namespace CFSG.AGLEmbedding.ParabAutIrr

open Subgroup CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  CFSG.ClassicalGroups.UnitaryFlag CFSG.Assembly.LowTwoRank CFSG.RankThree.PartOne.OutStructure

section Quot

variable {A : Type*} [Group A]

theorem exists_gen_mod_of_isCyclic_quotient {D I : Subgroup A}
    [(I.subgroupOf D).Normal] (hcyc : IsCyclic (↥D ⧸ I.subgroupOf D)) :
    ∃ d ∈ D, ∀ x ∈ D, ∃ k : ℤ, d ^ k * x ∈ I := by
  obtain ⟨γ, hγ⟩ := hcyc.exists_generator
  obtain ⟨d, rfl⟩ := QuotientGroup.mk_surjective γ
  refine ⟨d.1, d.2, fun x hx => ?_⟩
  obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.1 (hγ (QuotientGroup.mk (⟨x, hx⟩ : ↥D)))
  refine ⟨-m, ?_⟩
  have h1 : (QuotientGroup.mk (d ^ (-m) * ⟨x, hx⟩ : ↥D) : ↥D ⧸ I.subgroupOf D) = 1 := by
    rw [QuotientGroup.mk_mul, QuotientGroup.mk_zpow, zpow_neg, ← hm]
    simp
  rw [QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf] at h1
  simpa using h1

end Quot

section Prime

variable {p f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData p f K) {n : ℕ} (hn : 3 ≤ n)
  (hq : ¬(n = 3 ∧ p ^ f = 2))

include h hn hq in
theorem outPTwoGen_primeFormP {r : ℕ} :
    OutPTwoGen (primeFormP h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) r := by
  have : Finite K := h.finite
  have hC : IsPrimeFormGram (1 : GL (Fin n) K) := isPrimeFormGram_one
  obtain ⟨-, -, -, -, -, -, hFsurj, hFker, hDn, hinn, -⟩ :=
    unitary_prime_form_full_semilinear_realization h hC hn hq
  obtain ⟨-, hcyc, -⟩ := unitary_full_diagonal_outer_order h hn hq
  set T := primeFormP h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) with hT
  set D := primeFormD h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) with hD
  have hID : inn T ≤ D := fun α hα => by
    obtain ⟨s, rfl⟩ := (hinn α).1 hα
    exact ⟨_, rfl⟩
  have : (inn T).Normal := inn_normal
  have hnormal : ((inn T).subgroupOf D).Normal := Subgroup.Normal.subgroupOf inferInstance D
  have hDcyc : ∃ d ∈ D, ∀ x ∈ D, ∃ k : ℤ, d ^ k * x ∈ inn T :=
    exists_gen_mod_of_isCyclic_quotient hcyc
  have hring := card_ringAut_and_isCyclic h.prime K h.card
  have : Finite (RingAut K) :=
    Nat.finite_of_card_ne_zero (by rw [hring.1]; have := h.one_le; omega)
  have : IsCyclic (RingAut K) := hring.2
  obtain ⟨σ₀, hσ₀⟩ := IsCyclic.exists_generator (α := RingAut K)
  obtain ⟨g, hg⟩ := hFsurj σ₀
  refine OutPTwoGen.of_tower D ⊤ ?_ hDcyc ?_ (fun x _ => trivial)
  · intro x _
    rw [Subgroup.mem_normalizer_iff]
    intro d
    exact ⟨fun hd => hDn.conj_mem d hd x, fun hd => by
      simpa [mul_assoc] using hDn.conj_mem _ hd x⁻¹⟩
  · refine ⟨g, trivial, fun x _ => ?_⟩
    obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.1 (hσ₀ (primeFormFieldFactor h hC hn hq x))
    refine ⟨-m, ?_⟩
    rw [← hFker, MonoidHom.mem_ker, map_mul, map_zpow, hg, zpow_neg, ← hm]
    simp

end Prime

section Model

theorem exists_equiv_primeFormP {Y : Type} [Group Y] {n f : ℕ}
    (h : StatedClassicalModel Y .PSU n 2 f) :
    ∃ (K : Type) (_ : Field K) (hU : UnitaryFieldData 2 f K), ¬(n = 3 ∧ 2 ^ f = 2) ∧
      3 ≤ n ∧ Nonempty (Y ≃* primeFormP hU ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) := by
  obtain ⟨⟨hℓ, hm, hn3, hne⟩, K, _, _, hK, ⟨e⟩⟩ := h
  have hU : UnitaryFieldData 2 f K := ⟨hℓ, hm, by rw [hK, ← pow_mul, mul_comm]⟩
  have hq : ¬(n = 3 ∧ 2 ^ f = 2) := fun ⟨h1, h2⟩ => hne (by rw [h1, h2])
  obtain ⟨⟨eT⟩, -⟩ := unitary_prime_form_full_semilinear_realization hU
    (isPrimeFormGram_one (n := n)) hn3 hq
  exact ⟨K, inferInstance, hU, hq, hn3,
    ⟨(e.trans (unitaryPSUEquiv hU (by omega)).symm).trans eT.symm⟩⟩

theorem outPTwoGen_psu {Y : Type} [Group Y] [Finite Y] {n f : ℕ}
    (h : StatedClassicalModel Y .PSU n 2 f) {r : ℕ} : OutPTwoGen Y r := by
  obtain ⟨K, _, hU, hq, hn3, ⟨e⟩⟩ := exists_equiv_primeFormP h
  exact OutPTwoGen.of_mulEquiv e.symm (outPTwoGen_primeFormP hU hn3 hq)

theorem outPInner_psu_two {Y : Type} [Group Y] [Finite Y] {n : ℕ}
    (h : StatedClassicalModel Y .PSU n 2 1) {r : ℕ} (hr : r.Prime) (hr5 : 5 ≤ r) :
    OutPInner Y r := by
  obtain ⟨K, _, hU, hq, hn3, ⟨e⟩⟩ := exists_equiv_primeFormP h
  refine OutPInner.of_mulEquiv e.symm (OutPInner.of_not_dvd hr ?_)
  obtain ⟨-, -, -, hcard, -⟩ := unitary_full_diagonal_outer_order hU hn3 hq
  have h1 : Nat.card (MulAut (primeFormP hU ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) ⧸
      inn (primeFormP hU ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K))) =
      2 * 1 * Nat.gcd n (2 ^ 1 + 1) := hcard
  rw [h1]
  intro hd
  have h6 : r ∣ 6 := hd.trans ((Nat.mul_dvd_mul_left 2 (Nat.gcd_dvd_right n (2 ^ 1 + 1))).trans
    (by norm_num))
  have hle : r ≤ 6 := Nat.le_of_dvd (by norm_num) h6
  interval_cases r
  · norm_num at h6
  · exact absurd hr (by norm_num)

end Model

end CFSG.AGLEmbedding.ParabAutIrr

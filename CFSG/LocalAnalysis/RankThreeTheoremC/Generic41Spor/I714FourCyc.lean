module

public import CFSG.Walter.Cited.Huppert
public import CFSG.GroupTheory.ABGLocalTools.Basic
public import CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.NoM125Struct

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor

open Subgroup CFSG.ABGLocalTools
open scoped commutatorElement

variable {X : Type*} [Group X] [Finite X]

theorem orderOf_eq_twentyFive {Q : Subgroup X} (hQ : Nat.card Q = 5 ^ 3)
    (hnab : ¬ IsMulCommutative Q) {q : X} (hq : q ∈ Q) (hq5 : q ^ 5 ≠ 1) : orderOf q = 25 := by
  have hord : orderOf (⟨q, hq⟩ : Q) = orderOf q := Subgroup.orderOf_mk q hq
  have hdvd : orderOf q ∣ 5 ^ 3 := by
    rw [← hord, ← hQ]
    exact orderOf_dvd_natCard _
  obtain ⟨k, hk, hk'⟩ := (Nat.dvd_prime_pow Nat.prime_five).mp hdvd
  interval_cases k
  · exfalso
    apply hq5
    have h1 : orderOf q = 1 := by simpa using hk'
    rw [orderOf_eq_one_iff.mp h1, one_pow]
  · exfalso
    apply hq5
    have := pow_orderOf_eq_one q
    rwa [hk', pow_one] at this
  · simpa using hk'
  · exfalso
    apply hnab
    have : IsCyclic Q := isCyclic_of_orderOf_eq_card (⟨q, hq⟩ : Q) (by rw [hord, hk', hQ])
    infer_instance

theorem isMetacyclic_of_orderOf_eq_twentyFive {Q : Subgroup X} (hQ : Nat.card Q = 5 ^ 3) {a : X}
    (ha : a ∈ Q) (ha25 : orderOf a = 25) : CFSG.IsMetacyclic Q := by
  haveI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  set C : Subgroup Q := zpowers ⟨a, ha⟩ with hC
  have hCcard : Nat.card C = 25 := by rw [hC, Nat.card_zpowers, Subgroup.orderOf_mk, ha25]
  have hidx : C.index = 5 := by
    have h := C.card_mul_index
    rw [hCcard, hQ] at h
    omega
  have hCn : C.Normal := Subgroup.normal_of_index_eq_minFac_card (by
    rw [hidx, hQ, Nat.Prime.pow_minFac Nat.prime_five (by norm_num)])
  refine ⟨C, hCn, inferInstance, ?_⟩
  exact isCyclic_of_prime_card (p := 5) (by rw [← Subgroup.index_eq_card, hidx])

theorem exists_cyclic_inf_commutator_five (P : Sylow 5 X)
    (hmeta : CFSG.IsMetacyclic (P : Subgroup X)) (hnab : ¬ IsMulCommutative (P : Subgroup X)) :
    ∃ D : Subgroup X, D ≤ P ∧ IsCyclic D ∧ (P : Subgroup X) ⊓ commutator X ≤ D := by
  haveI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  obtain ⟨D, hDP, hDcyc, hD⟩ :=
    CFSG.Walter.Huppert.exists_cyclic_of_normalizer (by norm_num) P hmeta hnab
  refine ⟨D, hDP, hDcyc, ?_⟩
  have hfocal : (P : Subgroup X) ⊓ CFSG.derivedSubgroup X ≤ D := by
    rw [CFSG.sylow_inf_derivedSubgroup_eq_focalSubgroup 5 P, Subgroup.closure_le]
    rintro _ ⟨x, hx, y, hy, hxy, rfl⟩
    obtain ⟨g, rfl⟩ := isConj_iff.mp hxy
    obtain ⟨c, hc, hcx⟩ := CFSG.Walter.Huppert.exists_mem_normalizer_conj_eq (by norm_num) P
      hmeta (g := g⁻¹) hx (by simpa using hy)
    have := hD x hx c hc
    rw [hcx] at this
    simpa using this
  rwa [CFSG.derivedSubgroup, derivedSeries_one] at hfocal

theorem le_commutator_of_simple {K : Subgroup X} (hKs : IsSimpleGroup K)
    (hnab : ∃ a b : K, a * b ≠ b * a) : K ≤ commutator X := by
  have htop : commutator K = ⊤ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (commutator K) with h | h
    · obtain ⟨a, b, hab⟩ := hnab
      refine (hab ?_).elim
      have hmem : ⁅a, b⁆ ∈ commutator K :=
        Subgroup.commutator_mem_commutator (Subgroup.mem_top a) (Subgroup.mem_top b)
      rw [h, Subgroup.mem_bot] at hmem
      exact commutatorElement_eq_one_iff_mul_comm.mp hmem
    · exact h
  intro k hk
  have hmem : (⟨k, hk⟩ : K) ∈ commutator K := htop ▸ Subgroup.mem_top _
  have hmap := Subgroup.mem_map_of_mem K.subtype hmem
  rw [Subgroup.map_subtype_commutator] at hmap
  exact Subgroup.commutator_mono le_top le_top hmap

theorem isCyclic_inf_of_isM125 {K : Subgroup X} (hKs : IsSimpleGroup K)
    (hKnab : ∃ a b : K, a * b ≠ b * a) (Q : Sylow 5 X)
    (h : NoM125.IsM125 5 (Q : Subgroup X)) : IsCyclic ↥((Q : Subgroup X) ⊓ K) := by
  obtain ⟨a, ha, ha5⟩ := h.big
  have ha25 := orderOf_eq_twentyFive h.card h.nonab ha ha5
  obtain ⟨D, -, hDcyc, hD⟩ :=
    exists_cyclic_inf_commutator_five Q (isMetacyclic_of_orderOf_eq_twentyFive h.card ha ha25)
      h.nonab
  have hle : (Q : Subgroup X) ⊓ K ≤ D :=
    le_trans (inf_le_inf_left (Q : Subgroup X) (le_commutator_of_simple hKs hKnab)) hD
  exact Subgroup.isCyclic_of_le hle

theorem exists_pow_five_eq_one_not_mem {K Q : Subgroup X} (h : NoM125.IsM125 5 Q)
    (hcyc : IsCyclic ↥(Q ⊓ K)) (hcard : Nat.card ↥(Q ⊓ K) = 25) :
    ∃ a ∈ Q, a ∉ K ∧ a ^ 5 = 1 := by
  by_contra hcon
  push Not at hcon
  have hEle : h.E ≤ Q ⊓ K := by
    intro e he
    obtain ⟨heQ, he5⟩ := (NoM125.IsM125.mem_E h).mp he
    refine ⟨heQ, ?_⟩
    by_contra heK
    exact hcon e heQ heK he5
  have hEcard : Nat.card h.E = 25 := by rw [NoM125.IsM125.card_E h]; norm_num
  have heq : h.E = Q ⊓ K :=
    Subgroup.eq_of_le_of_card_ge hEle (by rw [hcard, hEcard])
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := ↥(Q ⊓ K))
  have hgord : orderOf g = 25 := by
    rw [orderOf_eq_card_of_forall_mem_zpowers hg, hcard]
  have hgE : (g : X) ∈ h.E := by rw [heq]; exact g.2
  have hg5 : (g : X) ^ 5 = 1 := ((NoM125.IsM125.mem_E h).mp hgE).2
  have hdvd : orderOf g ∣ 5 := by
    apply orderOf_dvd_of_pow_eq_one
    exact Subtype.ext (by simpa using hg5)
  rw [hgord] at hdvd
  omega

end CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor

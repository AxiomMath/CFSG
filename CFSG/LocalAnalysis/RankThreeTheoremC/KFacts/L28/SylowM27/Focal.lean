module

public import CFSG.Walter.Cited.Huppert
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.GroupTheory.ABGLocalTools.Basic
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.L28.SylowM27

open Subgroup CFSG.ABGLocalTools
open scoped commutatorElement

variable {X : Type*} [Group X] [Finite X]

theorem orderOf_eq_nine {Q : Subgroup X} (hQ : Nat.card Q = 3 ^ 3) (hnab : ¬ IsMulCommutative Q)
    {q : X} (hq : q ∈ Q) (hq3 : q ^ 3 ≠ 1) : orderOf q = 9 := by
  have hord : orderOf (⟨q, hq⟩ : Q) = orderOf q := Subgroup.orderOf_mk q hq
  have hdvd : orderOf q ∣ 3 ^ 3 := by
    rw [← hord, ← hQ]
    exact orderOf_dvd_natCard _
  obtain ⟨k, hk, hk'⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp hdvd
  interval_cases k
  · exfalso
    apply hq3
    have h1 : orderOf q = 1 := by simpa using hk'
    rw [orderOf_eq_one_iff.mp h1, one_pow]
  · exfalso
    apply hq3
    have := pow_orderOf_eq_one q
    rwa [hk', pow_one] at this
  · simpa using hk'
  · exfalso
    apply hnab
    have : IsCyclic Q := isCyclic_of_orderOf_eq_card (⟨q, hq⟩ : Q) (by rw [hord, hk', hQ])
    infer_instance

theorem isMetacyclic {Q : Subgroup X} (hQ : Nat.card Q = 3 ^ 3) {a : X} (ha : a ∈ Q)
    (ha9 : orderOf a = 9) : CFSG.IsMetacyclic Q := by
  set C : Subgroup Q := zpowers ⟨a, ha⟩ with hC
  have hCcard : Nat.card C = 9 := by rw [hC, Nat.card_zpowers, Subgroup.orderOf_mk, ha9]
  have hidx : C.index = 3 := by
    have h := C.card_mul_index
    rw [hCcard, hQ] at h
    omega
  have hCn : C.Normal := Subgroup.normal_of_index_eq_minFac_card (by rw [hidx, hQ]; norm_num)
  refine ⟨C, hCn, inferInstance, ?_⟩
  exact isCyclic_of_prime_card (p := 3) (by rw [← Subgroup.index_eq_card, hidx])

theorem exists_cyclic_inf_commutator (P : Sylow 3 X) (hmeta : CFSG.IsMetacyclic (P : Subgroup X))
    (hnab : ¬ IsMulCommutative (P : Subgroup X)) :
    ∃ D : Subgroup X, D ≤ P ∧ IsCyclic D ∧ (P : Subgroup X) ⊓ commutator X ≤ D := by
  obtain ⟨D, hDP, hDcyc, hD⟩ :=
    CFSG.Walter.Huppert.exists_cyclic_of_normalizer (by norm_num) P hmeta hnab
  refine ⟨D, hDP, hDcyc, ?_⟩
  have hfocal : (P : Subgroup X) ⊓ CFSG.derivedSubgroup X ≤ D := by
    rw [CFSG.sylow_inf_derivedSubgroup_eq_focalSubgroup 3 P, Subgroup.closure_le]
    rintro _ ⟨x, hx, y, hy, hxy, rfl⟩
    obtain ⟨g, rfl⟩ := isConj_iff.mp hxy
    obtain ⟨c, hc, hcx⟩ := CFSG.Walter.Huppert.exists_mem_normalizer_conj_eq (by norm_num) P
      hmeta (g := g⁻¹) hx (by simpa using hy)
    have := hD x hx c hc
    rw [hcx] at this
    simpa using this
  rwa [CFSG.derivedSubgroup, derivedSeries_one] at hfocal

theorem le_commutator {K : Subgroup X} (hKs : IsSimpleGroup K) (hnab : ∃ a b : K, a * b ≠ b * a) :
    K ≤ commutator X := by
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

theorem isCyclic_inf_and_not_le {K Q : Subgroup X} (hKs : IsSimpleGroup K)
    (hKnab : ∃ a b : K, a * b ≠ b * a) (hQsyl : IsSylowOf 3 Q ⊤) (hQ : Nat.card Q = 3 ^ 3)
    (hQnab : ¬ IsMulCommutative Q) {a : X} (ha : a ∈ Q) (ha9 : orderOf a = 9) :
    IsCyclic ↥(Q ⊓ K) ∧ ¬ Q ≤ K := by
  obtain ⟨-, hQp, hidx⟩ := isSylowOf_iff.mp hQsyl
  rw [Subgroup.relIndex_top_right] at hidx
  obtain ⟨D, hDP, hDcyc, hD⟩ :=
    exists_cyclic_inf_commutator (hQp.toSylow hidx) (isMetacyclic hQ ha ha9) hQnab
  have hle : Q ⊓ K ≤ D := le_trans (inf_le_inf_left Q (le_commutator hKs hKnab)) hD
  refine ⟨Subgroup.isCyclic_of_le hle, fun hQK => hQnab ?_⟩
  have hQD : Q ≤ D := fun x hx => hle ⟨hx, hQK hx⟩
  have : IsCyclic Q := Subgroup.isCyclic_of_le hQD
  infer_instance

end CFSG.LocalAnalysis.RankThreeTheoremC.L28.SylowM27

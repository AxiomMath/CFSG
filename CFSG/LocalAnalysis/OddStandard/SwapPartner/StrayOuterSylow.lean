module

public import Mathlib.GroupTheory.Sylow
import CFSG.LocalAnalysis.OddStandard.SwapPartner.StrayPerfect
import CFSG.LocalAnalysis.ComponentClassification.AschbacherKnownGroupLemma39

public section

namespace CFSG.OddStandard.AltStdSec.SwapPartner

open Subgroup

theorem exists_sylow_index_two {G : Type*} [Group G] [Finite G] {L : Subgroup G} {a : G}
    (ha : a ^ 2 = 1) (haN : a ∈ normalizer (L : Set G)) (haL : a ∉ L) :
    ∃ Ts : Subgroup G, IsPGroup 2 Ts ∧ a ∈ Ts ∧ Ts ≤ zpowers a ⊔ L ∧
      (Ts ⊓ L).relIndex Ts = 2 ∧ Nat.card ↥(Ts ⊓ L) = 2 ^ (Nat.card ↥L).factorization 2 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let M : Subgroup G := zpowers a ⊔ L
  have haM : a ∈ M := Subgroup.mem_sup_left (Subgroup.mem_zpowers a)
  have hcardM : Nat.card ↥M = 2 * Nat.card ↥L := by
    show Nat.card ↥(zpowers a ⊔ L) = 2 * Nat.card ↥L
    rw [sup_comm]
    exact card_sup_zpowers_eq_two_mul ha haN haL
  have hz : IsPGroup 2 (zpowers a) := by
    refine IsPGroup.of_card_dvd_pow (n := 1) ?_
    rw [Nat.card_zpowers]
    simpa using orderOf_dvd_iff_pow_eq_one.mpr ha
  have hA2 : IsPGroup 2 ((zpowers a).subgroupOf M) := hz.comap_subtype
  obtain ⟨P, hAP⟩ := hA2.exists_le_sylow
  let Ts : Subgroup G := (P : Subgroup ↥M).map M.subtype
  have haA : (⟨a, haM⟩ : ↥M) ∈ (zpowers a).subgroupOf M :=
    Subgroup.mem_subgroupOf.mpr (Subgroup.mem_zpowers a)
  have haP : (⟨a, haM⟩ : ↥M) ∈ (P : Subgroup ↥M) := hAP haA
  have haTs : a ∈ Ts := Subgroup.mem_map_of_mem M.subtype haP
  have hTsM : Ts ≤ zpowers a ⊔ L := Subgroup.map_subtype_le (P : Subgroup ↥M)
  have hrel : (Ts ⊓ L).relIndex Ts = 2 := by
    rw [Subgroup.relIndex_eq_two_iff_exists_notMem_and]
    refine ⟨a, haTs, fun haT => haL haT.2, fun b hb => ?_⟩
    by_cases hbL : b ∈ L
    · exact Or.inr ⟨hb, hbL⟩
    · left
      have hbM : b ∈ zpowers a ⊔ L := hTsM hb
      rcases CFSG.ComponentClassification.AschbacherKnownGroup.Lemma39.mem_zpowers_sup ha haN hbM
        with hbL' | ⟨y, hy, hby⟩
      · exact absurd hbL' hbL
      · refine ⟨Ts.mul_mem hb haTs, ?_⟩
        have hconj : a * y * a⁻¹ ∈ L := (Subgroup.mem_normalizer_iff.1 haN y).1 hy
        have hainv : a⁻¹ = a := inv_eq_of_mul_eq_one_right (by rw [← pow_two]; exact ha)
        rw [hby]
        simpa [hainv] using hconj
  have hTscard : Nat.card ↥Ts = 2 * 2 ^ (Nat.card ↥L).factorization 2 := by
    have h1 : Nat.card ↥Ts = 2 ^ (Nat.card ↥M).factorization 2 := by
      have hmap := Subgroup.card_map_of_injective (K := (P : Subgroup ↥M)) M.subtype_injective
      show Nat.card ↥((P : Subgroup ↥M).map M.subtype) = 2 ^ (Nat.card ↥M).factorization 2
      rw [hmap, Sylow.card_eq_multiplicity P]
    have hLne : Nat.card ↥L ≠ 0 := by
      haveI : Nonempty ↥L := ⟨⟨1, L.one_mem⟩⟩
      exact Nat.card_pos.ne'
    have hfac : (Nat.card ↥M).factorization 2 = (Nat.card ↥L).factorization 2 + 1 := by
      rw [hcardM, Nat.factorization_mul (by norm_num) hLne, Finsupp.add_apply,
        Nat.Prime.factorization_self Nat.prime_two, Nat.add_comm]
    rw [h1, hfac, pow_succ']
  have hcardrel : (Ts ⊓ L).relIndex Ts * Nat.card ↥(Ts ⊓ L) = Nat.card ↥Ts := by
    have h := Subgroup.relIndex_mul_card (H := Ts ⊓ L) (K := Ts)
    rwa [inf_of_le_left inf_le_left] at h
  have hfinal : Nat.card ↥(Ts ⊓ L) = 2 ^ (Nat.card ↥L).factorization 2 := by
    have h2 : 2 * Nat.card ↥(Ts ⊓ L) = 2 * 2 ^ (Nat.card ↥L).factorization 2 := by
      rw [hrel] at hcardrel
      rw [hcardrel, hTscard]
    exact Nat.mul_left_cancel (by norm_num) h2
  exact ⟨Ts, P.isPGroup'.map M.subtype, haTs, hTsM, hrel, hfinal⟩

end CFSG.OddStandard.AltStdSec.SwapPartner

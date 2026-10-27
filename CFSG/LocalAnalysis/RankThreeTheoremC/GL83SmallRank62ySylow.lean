module

public import Mathlib.GroupTheory.Solvable
public import Mathlib.GroupTheory.Sylow
import Mathlib.GroupTheory.Nilpotent
import CFSG.RankThree.PGroups.CoprimeInvariantSylow
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.CardSupOfDisjointNormalizer

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open Subgroup

variable {G : Type} [Group G] [Finite G]

theorem sr628_exists_invariant_sylow {O A : Subgroup G} (hAO : A ≤ normalizer (O : Set G))
    (hcop : Nat.Coprime (Nat.card A) (Nat.card O)) [Group.IsSolvable A] [Group.IsSolvable O]
    {q : ℕ} (hq : q.Prime) :
    ∃ F : Subgroup G, F ≤ O ∧ IsPGroup q F ∧ Nat.card F = q ^ (Nat.card O).factorization q ∧
      A ≤ normalizer (F : Set G) := by
  have : Fact q.Prime := ⟨hq⟩
  let ρ : ↥A →* MulAut ↥O := O.normalizerMonoidHom.comp (Subgroup.inclusion hAO)
  obtain ⟨Q, hQ⟩ :=
    (CFSG.RankThree.PGroups.solvable_coprime_invariant_sylow_containment hcop ρ hq).2
  refine ⟨(Q : Subgroup O).map O.subtype, Subgroup.map_subtype_le _,
    Q.isPGroup'.map O.subtype, ?_, ?_⟩
  · rw [Subgroup.card_map_of_injective O.subtype_injective]
    exact Sylow.card_eq_multiplicity Q
  · rw [le_normalizer_iff]
    rintro a ha _ ⟨k, hk, rfl⟩
    have h1 := hQ ⟨a, ha⟩
    have h2 : ρ ⟨a, ha⟩ k ∈ (Q : Subgroup O).map (ρ ⟨a, ha⟩).toMonoidHom :=
      Subgroup.mem_map_of_mem _ hk
    rw [h1] at h2
    exact ⟨ρ ⟨a, ha⟩ k, h2, O.normalizerMonoidHom_apply_apply_coe ⟨a, hAO ha⟩ k⟩

theorem sr628_exists_invariant_pGroup_not_le {O A M : Subgroup G}
    (hAO : A ≤ normalizer (O : Set G)) (hcop : Nat.Coprime (Nat.card A) (Nat.card O))
    [Group.IsSolvable A] [Group.IsSolvable O] (hOM : ¬ O ≤ M) :
    ∃ q : ℕ, q.Prime ∧ ∃ F : Subgroup G, F ≤ O ∧ IsPGroup q F ∧
      A ≤ normalizer (F : Set G) ∧ ¬ F ≤ M := by
  by_contra hcon
  push Not at hcon
  let W : Subgroup G := sSup {F | ∃ q : ℕ, q.Prime ∧ F ≤ O ∧ IsPGroup q F ∧
    A ≤ normalizer (F : Set G)}
  have hWM : W ≤ M := sSup_le fun F ⟨q, hq, hFO, hFp, hAF⟩ => hcon q hq F hFO hFp hAF
  have hWO : W ≤ O := sSup_le fun F ⟨_, _, hFO, _, _⟩ => hFO
  have hdvd : Nat.card O ∣ Nat.card W := by
    refine (Nat.factorization_prime_le_iff_dvd Nat.card_pos.ne' Nat.card_pos.ne').mp ?_
    intro q hq
    obtain ⟨F, hFO, hFp, hFc, hAF⟩ := sr628_exists_invariant_sylow hAO hcop hq
    have hFW : F ≤ W := le_sSup ⟨q, hq, hFO, hFp, hAF⟩
    have hpow : q ^ (Nat.card O).factorization q ∣ Nat.card W :=
      hFc ▸ Subgroup.card_dvd_of_le hFW
    exact (hq.pow_dvd_iff_le_factorization Nat.card_pos.ne').mp hpow
  have hWeq : W = O := Subgroup.eq_of_le_of_card_ge hWO (Nat.le_of_dvd Nat.card_pos hdvd)
  exact hOM (hWeq ▸ hWM)

theorem sr628_card_sup_and_solvable {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {S B : Subgroup G}
    (hS : IsPGroup 2 S) (hB : IsPGroup p B) (hBS : B ≤ normalizer (S : Set G)) :
    Nat.card ↥(S ⊔ B) = Nat.card S * Nat.card B ∧ Group.IsSolvable ↥(S ⊔ B) := by
  have : Fact p.Prime := ⟨hp⟩
  have hdisj : Disjoint S B :=
    IsPGroup.disjoint_of_coprime hS hB ((Nat.coprime_primes Nat.prime_two hp).mpr hp2.symm)
  have hcard := CFSG.GorensteinWalter.card_sup_eq_mul_of_disjoint_of_le_normalizer S B hBS hdisj
  refine ⟨hcard, ?_⟩
  have hSA : S ≤ S ⊔ B := le_sup_left
  have hAS : S ⊔ B ≤ normalizer (S : Set G) := sup_le le_normalizer hBS
  have hnorm : (S.subgroupOf (S ⊔ B)).Normal := normal_subgroupOf_of_le_normalizer hAS
  have hS2 : IsPGroup 2 (S.subgroupOf (S ⊔ B)) :=
    hS.of_equiv (subgroupOfEquivOfLe hSA).symm
  have : Group.IsSolvable ↥(S.subgroupOf (S ⊔ B)) := by
    have := hS2.isNilpotent
    infer_instance
  have hq : Group.IsSolvable (↥(S ⊔ B) ⧸ S.subgroupOf (S ⊔ B)) := by
    obtain ⟨b, hb⟩ := hB.exists_card_eq
    have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup (S.subgroupOf (S ⊔ B))
    have h2 : Nat.card (S.subgroupOf (S ⊔ B)) = Nat.card S :=
      Nat.card_congr (subgroupOfEquivOfLe hSA).toEquiv
    rw [h2, hcard, hb] at h1
    have h3 : Nat.card (↥(S ⊔ B) ⧸ S.subgroupOf (S ⊔ B)) = p ^ b := by
      have hSpos : 0 < Nat.card S := Nat.card_pos
      refine Nat.eq_of_mul_eq_mul_left hSpos ?_
      rw [h1, mul_comm]
    have hp' : IsPGroup p (↥(S ⊔ B) ⧸ S.subgroupOf (S ⊔ B)) := IsPGroup.of_card h3
    have := hp'.isNilpotent
    infer_instance
  exact Group.isSolvable_of_subgroup_quotient (S.subgroupOf (S ⊔ B))

end CFSG.LocalAnalysis.RankThreeTheoremC

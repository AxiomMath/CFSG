module

public import CFSG.LocalAnalysis.AGLEmbedding.TheoremZGen
import CFSG.LocalAnalysis.AGLEmbedding.CoprimeSup
public import CFSG.LocalAnalysis.AGLEmbedding.ResidualTools

public section

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.PreuniquenessRankFour.Helpers
open CFSG.RankThreeCoreUniqueness.Helpers

section ZN

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem mem_of_mul_mem_of_coprime {p : ℕ} [Fact p.Prime] {A N : Subgroup G} {x n : G}
    (hx : IsPGroup p (Subgroup.zpowers x)) (hN : (Nat.card N).Coprime p)
    (hNA : N ≤ Subgroup.normalizer (A : Set G)) (hn : n ∈ N) (hxn : x * n ∈ A) : x ∈ A := by
  have hxAN : x ∈ A ⊔ N := by
    have e : x = x * n * n⁻¹ := by group
    rw [e]
    exact Subgroup.mul_mem_sup hxn (N.inv_mem hn)
  have hxNA : x ∈ N ⊔ A := by
    rw [sup_comm]
    exact hxAN
  exact le_of_le_sup_of_coprime_card_of_le ((Subgroup.zpowers_le).mpr hxNA) le_sup_right
    le_sup_left (Subgroup.normal_subgroupOf_sup_of_le_normalizer hNA) hx hN
    ((Subgroup.zpowers_le).mpr hxAN) (Subgroup.mem_zpowers x)

omit [Finite G] in
theorem le_sup_inf_of_le_sup_of_coprime {p : ℕ} [Fact p.Prime] {X N A : Subgroup G}
    (hX : IsPGroup p X) (hXN : X ≤ Subgroup.normalizer (N : Set G))
    (hN : (Nat.card N).Coprime p) (hNA : N ≤ Subgroup.normalizer (A : Set G))
    (hA : A ≤ X ⊔ N) : A ≤ X ⊔ (A ⊓ N) := by
  intro a ha
  have hmem : a ∈ ((X ⊔ N : Subgroup G) : Set G) := hA ha
  rw [Subgroup.coe_mul_of_left_le_normalizer_right X N hXN] at hmem
  obtain ⟨x, hx, n, hn, rfl⟩ := hmem
  have hxA : x ∈ A :=
    mem_of_mul_mem_of_coprime (hX.to_le ((Subgroup.zpowers_le).mpr hx)) hN hNA hn ha
  have hnA : n ∈ A := by
    have e : n = x⁻¹ * (x * n) := by group
    rw [e]
    exact A.mul_mem (A.inv_mem hxA) ha
  exact Subgroup.mul_mem_sup hx ⟨hnA, hn⟩

variable {p : ℕ} {P : Sylow p G} {M H R : Subgroup G}

theorem D1PhaseThree.false_of_normal_of_commutator_le (h : D1PhaseThree p P M H R)
    {E J : Subgroup G} (hEM : E ≤ M) (hME : M ≤ Subgroup.normalizer (E : Set G))
    (hQE : pCoreOf 2 M ≤ E) (hNJE : ⁅GLBPrimeCore p H, J⁆ ≤ E)
    (hNJ : ⁅GLBPrimeCore p H, J⁆ ≤ pCoreOf 2 H) (hEH : E ⊓ H ≤ R ⊔ GLBPrimeCore p H)
    (huniq : ∀ H' : Subgroup G, GLBIsMaxTwoLocal H' → J ≤ H' → R ≤ H' → H' = H)
    (hCGT : AschbacherLocalCGTBlock) (hD2 : D1NoXBlock) : False := by
  have : Fact p.Prime := ⟨h.prime⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set N := GLBPrimeCore p H with hNdef
  have hNH : N ≤ H := glbPrimeCore_le p H
  have hHN : H ≤ Subgroup.normalizer (N : Set G) := le_normalizer_glbPrimeCore p H
  have hSN : pCoreOf 2 H ≤ N := pCoreOf_le_glbPrimeCore Nat.prime_two
    ((Nat.coprime_primes h.prime Nat.prime_two).mpr h.ne_two) H
  have hN₁cop : p.Coprime (Nat.card (E ⊓ N : Subgroup G)) :=
    (glbPrimeCore_coprime p H).coprime_dvd_right (Subgroup.card_dvd_of_le inf_le_right)
  have hRN₁ : R ≤ Subgroup.normalizer ((E ⊓ N : Subgroup G) : Set G) :=
    (le_inf (h.le_M.trans hME) (h.le_H.trans hHN)).trans Subgroup.inf_normalizer_le_normalizer_inf
  obtain ⟨T, hTN, hT2, hTidx, hRT⟩ :=
    exists_le_normalizer_of_coprime (q := 2) h.isPGroup_R hRN₁ hN₁cop
  have hS₁T : pCoreOf 2 H ⊓ (E ⊓ N) ≤ T := by
    have hTS₁ : T ≤ Subgroup.normalizer ((pCoreOf 2 H ⊓ (E ⊓ N) : Subgroup G) : Set G) :=
      (le_inf (((hTN.trans inf_le_right).trans hNH).trans (localGroup_le_normalizer_pCoreOf 2 H))
        (hTN.trans Subgroup.le_normalizer)).trans Subgroup.inf_normalizer_le_normalizer_inf
    have h2 : IsPGroup 2 (pCoreOf 2 H ⊓ (E ⊓ N) ⊔ T : Subgroup G) :=
      IsPGroup.to_sup_of_normal_left'
        ((CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_isPGroup 2 H).to_le inf_le_left) hT2 hTS₁
    exact le_sup_left.trans
      (le_of_le_of_isPGroup_of_not_dvd_index le_sup_right (sup_le inf_le_right hTN) h2 hTidx)
  have hQS₁ : pCoreOf 2 M ≤ pCoreOf 2 H ⊓ (E ⊓ N) :=
    le_inf (h.twoCore_M_le h.twoCore_inf) (le_inf hQE h.twoCore_M_le_glbPrimeCore)
  have hT1 : T ≠ ⊥ := fun hbot => twoLocal_pCoreOf_ne_bot M h.maxTwoLocal_M.1
    (le_bot_iff.mp (hbot ▸ hQS₁.trans hS₁T))
  have hNJT : ⁅N, J⁆ ≤ T := (le_inf hNJ (le_inf hNJE (hNJ.trans hSN))).trans hS₁T
  have hJT : J ≤ Subgroup.normalizer (T : Set G) := by
    refine le_normalizer_of_forall_mul_mul_inv_mem fun j hj t ht => ?_
    have hc := hNJT (Subgroup.commutator_mem_commutator (N.inv_mem (hTN ht).2) hj)
    rw [commutatorElement_def, inv_inv] at hc
    have e : j * t * j⁻¹ = t * (t⁻¹ * j * t * j⁻¹) := by group
    rw [e]
    exact T.mul_mem ht hc
  have hNEH : N ≤ Subgroup.normalizer ((E ⊓ H : Subgroup G) : Set G) :=
    (le_inf (h.primeCore_le.trans hME) (hNH.trans Subgroup.le_normalizer)).trans
      Subgroup.inf_normalizer_le_normalizer_inf
  have hDH : E ⊓ H ≤ R ⊔ (E ⊓ N) :=
    (le_sup_inf_of_le_sup_of_coprime h.isPGroup_R (h.le_H.trans hHN)
      (glbPrimeCore_coprime p H).symm hNEH hEH).trans
      (sup_le_sup_left (le_inf (inf_le_left.trans inf_le_left) inf_le_right) R)
  exact h.false_of_normal_inf_le_sup_of h.isPGroup_R h.le_H (inf_le_right.trans hNH) hRN₁ hTN
    hT2 hTidx hT1
    (fun C hCT hC hchar => normalizer_le_of_forall_maxTwoLocal_eq hT2 hJT hRT huniq hCT hC hchar)
    hEM hME hQE inf_le_left hDH hCGT hD2

end ZN

end CFSG.AGLEmbedding

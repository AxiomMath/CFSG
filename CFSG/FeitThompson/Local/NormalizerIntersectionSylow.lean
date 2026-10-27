module

public import CFSG.FeitThompson.Statements.NonconjugateOutsideSigmaStatements
import CFSG.FeitThompson.Local.NoncyclicSigmaNormalizer
import CFSG.FeitThompson.Local.OddFrobeniusComplementPrimeSubgroupsNormal
import CFSG.FeitThompson.Local.CentralSylowFixedFreeCycle
import CFSG.FeitThompson.Local.PrimeFixedSectionExtension
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Basic

namespace CFSG.FeitThompson.Proofs

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

open Subgroup CFSG.FeitThompson CFSG.FeitThompson.Prep08

universe u

theorem eq_of_isPGroup_of_natCard_eq_pow_factorization {G : Type*} [Group G] [Finite G] {p : ℕ}
    (hp : p.Prime) {K T W : Subgroup G}
    (hT : Nat.card ↥T = p ^ (Nat.card ↥K).factorization p)
    (hTW : T ≤ W) (hWK : W ≤ K) (hWp : IsPGroup p ↥W) : W = T := by
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.1 hWp
  have hdvd : p ^ k ∣ Nat.card ↥K := hk ▸ Subgroup.card_dvd_of_le hWK
  have hKne : Nat.card ↥K ≠ 0 := Nat.card_pos.ne'
  have hle : k ≤ (Nat.card ↥K).factorization p := (hp.pow_dvd_iff_le_factorization hKne).1 hdvd
  refine (Subgroup.eq_of_le_of_card_ge hTW ?_).symm
  rw [hk, hT]
  exact Nat.pow_le_pow_right hp.pos hle

theorem FTS_normalizer_intersection_sylow
    (h₁ : Statements.FTS_plane_maximal_overgroups.{u}) :
    Statements.FTS_normalizer_intersection_sylow.{u} := by
  intro G _ _ hG M N Q T p hM hN hMN hpσ hQM hQcard hQN hT hQT
  have := hG.isSimpleGroup
  have hp : p.Prime := prime_of_mem_sigmaPrimes hpσ
  have : Fact p.Prime := ⟨hp⟩
  have hTMN : T ≤ M ⊓ N := hT.le
  have hTM : T ≤ M := hTMN.trans inf_le_left
  have hTN : T ≤ N := hTMN.trans inf_le_right
  have hTp : IsPGroup p ↥T := hT.isPGroup
  have hTcard : Nat.card ↥T = p ^ (Nat.card ↥(M ⊓ N)).factorization p :=
    (isSylowOf_iff_natCard hp hTMN).1 hT
  have hNTM : normalizer ((T : Subgroup G) : Set G) ≤ M := by
    by_cases hcyc : IsCyclic ↥T
    ·
      have : IsCyclic ↥T := hcyc
      have : (Q.subgroupOf T).Characteristic := characteristic_of_isCyclic _
      have hNTN : normalizer ((T : Subgroup G) : Set G) ≤ N := by
        have h := normalizer_le_normalizer_map_subtype T (Q.subgroupOf T)
        rw [Subgroup.map_subgroupOf_eq_of_le hQT] at h
        exact h.trans hQN
      obtain ⟨S, hS⟩ := IsPGroup.exists_le_sylow (P := T.subgroupOf M)
        (hTp.comap_of_injective M.subtype M.subtype_injective)
      set P : Subgroup G := map M.subtype (S : Subgroup ↥M) with hPdef
      have hTP : T ≤ P := by
        rw [← Subgroup.map_subgroupOf_eq_of_le hTM]; exact Subgroup.map_mono hS
      have hPp : IsPGroup p ↥P := S.isPGroup'.map M.subtype
      have hW : P ⊓ normalizer ((T : Subgroup G) : Set G) = T :=
        eq_of_isPGroup_of_natCard_eq_pow_factorization hp hTcard
          (le_inf hTP Subgroup.le_normalizer)
          (le_inf (inf_le_left.trans (Subgroup.map_subtype_le _)) (inf_le_right.trans hNTN))
          (hPp.to_le inf_le_left)
      have hTeq : T = P := by
        rcases eq_or_lt_of_le hTP with h | h
        · exact h
        · have hlt := lt_inf_normalizer_of_isPGroup hp hPp h
          rw [hW] at hlt
          exact absurd hlt (lt_irrefl T)
      rw [hTeq, hPdef]
      exact ((mem_sigmaPrimes_iff_forall hp).1 hpσ).2 S
    ·
      exact FTS_noncyclic_sigma_normalizer h₁ G hG M T p hM hpσ hTM hTp hcyc
  refine ⟨hNTM, ?_⟩
  obtain ⟨U, hU⟩ := IsPGroup.exists_le_sylow (P := T.subgroupOf N)
    (hTp.comap_of_injective N.subtype N.subtype_injective)
  refine ⟨U, ?_⟩
  have hTU : T ≤ map N.subtype (U : Subgroup ↥N) := by
    rw [← Subgroup.map_subgroupOf_eq_of_le hTN]; exact Subgroup.map_mono hU
  have hUp : IsPGroup p ↥(map N.subtype (U : Subgroup ↥N)) := U.isPGroup'.map N.subtype
  rcases eq_or_lt_of_le hTU with h | h
  · exact h.symm
  · exfalso
    have hW : map N.subtype (U : Subgroup ↥N) ⊓ normalizer ((T : Subgroup G) : Set G) = T :=
      eq_of_isPGroup_of_natCard_eq_pow_factorization hp hTcard
        (le_inf hTU Subgroup.le_normalizer)
        (le_inf (inf_le_right.trans hNTM) (inf_le_left.trans (Subgroup.map_subtype_le _)))
        (hUp.to_le inf_le_left)
    have hlt := lt_inf_normalizer_of_isPGroup hp hUp h
    rw [hW] at hlt
    exact absurd hlt (lt_irrefl T)

end

end CFSG.FeitThompson.Proofs

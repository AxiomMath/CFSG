module

public import CFSG.FeitThompson.Definitions.ElementaryAbelianPRank
import CFSG.FeitThompson.Local.CyclicIndexPGroupTorsionPlane
import CFSG.FeitThompson.Local.NormalSubgroupsOfEveryPrimePowerOrder
import CFSG.FeitThompson.Foundations.CharacteristicSubgroupInvariance

namespace CFSG.FeitThompson

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

open Subgroup

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

variable {p a : ℕ} {P : Type*} [Group P]

theorem exists_minimal_noncyclic_normal_le (N : Subgroup P) [N.Normal] (hnc : ¬ IsCyclic N) :
    ∃ M : Subgroup P, M ≤ N ∧ M.Normal ∧ ¬ IsCyclic M ∧
      ∀ K : Subgroup P, K ≤ N → K.Normal → ¬ IsCyclic K → Nat.card M ≤ Nat.card K := by
  have hne : {n : ℕ |
      ∃ K : Subgroup P, K ≤ N ∧ K.Normal ∧ ¬ IsCyclic K ∧ Nat.card K = n}.Nonempty :=
    ⟨Nat.card N, N, le_rfl, ‹N.Normal›, hnc, rfl⟩
  obtain ⟨M, hMN, hMnorm, hMnc, hMcard⟩ := Nat.sInf_mem hne
  refine ⟨M, hMN, hMnorm, hMnc, fun K hKN hKnorm hKnc => ?_⟩
  rw [hMcard]
  exact Nat.sInf_le ⟨K, hKN, hKnorm, hKnc, rfl⟩

theorem normal_map_subtype_of_characteristic (M : Subgroup P) [M.Normal] (K : Subgroup M)
    [K.Characteristic] : (K.map M.subtype).Normal := by
  have h1 : (K.map M.subtype).subgroupOf M = K :=
    Subgroup.comap_map_eq_self_of_injective M.subtype_injective K
  have h2 : ((K.map M.subtype).subgroupOf M).Characteristic := by rw [h1]; infer_instance
  exact normal_of_characteristic_subgroupOf_of_normal (Subgroup.map_subtype_le K)

theorem index_subgroupOf_eq_prime_of_natCard {m : ℕ} (hp : p.Prime) {M A : Subgroup P} (hAM : A ≤ M)
    (hM : Nat.card M = p ^ m) (hA : Nat.card A = p ^ (m - 1)) (hm : 1 ≤ m) :
    (A.subgroupOf M).index = p := by
  have hcard : Nat.card (A.subgroupOf M) = p ^ (m - 1) := by
    rw [Nat.card_congr (subgroupOfEquivOfLe hAM).toEquiv, hA]
  have h := Subgroup.index_mul_card (A.subgroupOf M)
  rw [hcard, hM] at h
  have hpm : p ^ m = p * p ^ (m - 1) := by rw [← pow_succ']; congr 1; omega
  exact Nat.eq_of_mul_eq_mul_right (pow_pos hp.pos _) (h.trans hpm)

theorem exists_normal_le_mulEquiv_zmod_prod_of_not_isCyclic (hp : p.Prime) (hodd : Odd p)
    (hP : Nat.card P = p ^ a) (N : Subgroup P) [N.Normal] (hnc : ¬ IsCyclic N) :
    ∃ E : Subgroup P, E ≤ N ∧ E.Normal ∧ Nonempty (E ≃* Multiplicative (ZMod p × ZMod p)) := by
  have := Fact.mk hp
  have hfin : Finite P := Nat.finite_of_card_ne_zero (by rw [hP]; exact pow_ne_zero _ hp.pos.ne')
  have hPp : IsPGroup p P := IsPGroup.of_card hP
  obtain ⟨M, hMN, hMnorm, hMnc, hmin⟩ := exists_minimal_noncyclic_normal_le N hnc
  have := hMnorm
  obtain ⟨m, hm⟩ := (hPp.to_subgroup M).exists_card_eq
  have hm2 : 2 ≤ m := by
    rcases Nat.lt_or_ge m 2 with h | h
    · interval_cases m
      · have : Subsingleton M := (Nat.card_eq_one_iff_unique.mp (by simpa using hm)).1
        exact absurd isCyclic_of_subsingleton hMnc
      · exact absurd (@isCyclic_of_prime_card M _ p ⟨hp⟩ (by simpa using hm)) hMnc
    · exact h
  obtain ⟨A, hAM, hAnorm, hAcard⟩ := exists_normal_le_natCard_eq_pow_of_isPGroup hp hPp M
    (d := m - 1) (by rw [hm]; exact pow_dvd_pow p (by omega))
  have := hAnorm
  have hAcyc : IsCyclic A := by
    by_contra hc
    have hle := hmin A (hAM.trans hMN) hAnorm hc
    rw [hm, hAcard] at hle
    exact absurd hle (by simpa using Nat.pow_lt_pow_right hp.one_lt (by omega : m - 1 < m))
  have hA'cyc : IsCyclic (A.subgroupOf M) :=
    isCyclic_of_injective (subgroupOfEquivOfLe hAM).toMonoidHom
      (subgroupOfEquivOfLe hAM).injective
  have hidx : (A.subgroupOf M).index = p :=
    index_subgroupOf_eq_prime_of_natCard hp hAM hm hAcard (by omega)
  obtain ⟨f⟩ := nonempty_mulEquiv_omega1_of_isCyclic_of_index_eq_prime (A.subgroupOf M) hp hodd
    (hPp.to_subgroup M) hMnc hidx
  exact ⟨(omega1 p M).map M.subtype, (Subgroup.map_subtype_le _).trans hMN,
    normal_map_subtype_of_characteristic M _,
    ⟨((omega1 p M).equivMapOfInjective M.subtype M.subtype_injective).symm.trans f⟩⟩

theorem exists_normal_le_mulEquiv_zmod_prod_of_not_isCyclic_of_isPGroup [Finite P] (hp : p.Prime)
    (hodd : Odd p) (hP : IsPGroup p P) (N : Subgroup P) [N.Normal] (hnc : ¬ IsCyclic N) :
    ∃ E : Subgroup P, E ≤ N ∧ E.Normal ∧ Nonempty (E ≃* Multiplicative (ZMod p × ZMod p)) := by
  have := Fact.mk hp
  obtain ⟨a, ha⟩ := hP.exists_card_eq
  exact exists_normal_le_mulEquiv_zmod_prod_of_not_isCyclic hp hodd ha N hnc

theorem exists_normal_le_mulEquiv_pi_of_not_isCyclic [Finite P] (hp : p.Prime) (hodd : Odd p)
    (hP : IsPGroup p P) (N : Subgroup P) [N.Normal] (hnc : ¬ IsCyclic N) :
    ∃ E : Subgroup P, E ≤ N ∧ E.Normal ∧
      Nonempty (E ≃* (Fin 2 → Multiplicative (ZMod p))) := by
  obtain ⟨E, hEN, hEnorm, ⟨f⟩⟩ :=
    exists_normal_le_mulEquiv_zmod_prod_of_not_isCyclic_of_isPGroup hp hodd hP N hnc
  exact ⟨E, hEN, hEnorm, ⟨f.trans (piMultiplicativeZModMulEquivProd p).symm⟩⟩

theorem exists_normal_le_natCard_eq_prime_sq_of_not_isCyclic [Finite P] (hp : p.Prime)
    (hodd : Odd p) (hP : IsPGroup p P) (N : Subgroup P) [N.Normal] (hnc : ¬ IsCyclic N) :
    ∃ E : Subgroup P, E ≤ N ∧ E.Normal ∧ Nat.card E = p ^ 2 := by
  obtain ⟨E, hEN, hEnorm, ⟨f⟩⟩ := exists_normal_le_mulEquiv_pi_of_not_isCyclic hp hodd hP N hnc
  exact ⟨E, hEN, hEnorm, by rw [Nat.card_congr f.toEquiv, card_pi_multiplicative_zmod]⟩

theorem two_le_elementaryAbelianPRank_of_not_isCyclic [Finite P] (hp : p.Prime) (hodd : Odd p)
    (hP : IsPGroup p P) (hnc : ¬ IsCyclic P) : 2 ≤ elementaryAbelianPRank p P := by
  obtain ⟨E, -, -, hE⟩ := exists_normal_le_mulEquiv_pi_of_not_isCyclic hp hodd hP (⊤ : Subgroup P)
    (fun _ => hnc (isCyclic_of_surjective (⊤ : Subgroup P).subtype fun x => ⟨⟨x, trivial⟩, rfl⟩))
  exact le_elementaryAbelianPRank hp.one_lt (mem_elementaryAbelianRanks.mpr ⟨E, hE⟩)

end

end CFSG.FeitThompson

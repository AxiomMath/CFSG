module

public import CFSG.LocalAnalysis.ComponentClassification.GMS78Basic

public section

namespace CFSG.ComponentClassification.GMS78

open Subgroup CFSG.Open
open scoped MatrixGroups

variable {Q : Type} [Group Q]

theorem NativeBenderType.exists_borel (h : NativeBenderType Q) :
    ∃ q k : ℕ, 8 ≤ q ^ k ∧ @fusionBenderBorel Q _ q k := by
  have := h.finite
  rcases h with ⟨m, hm, ⟨e⟩⟩ | ⟨m, hm, ⟨e⟩⟩ | ⟨a, ha, ⟨e⟩⟩
  · refine ⟨2 ^ m, 1, ?_, ?_⟩
    · rw [pow_one]
      calc 8 = 2 ^ 3 := by norm_num
        _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hm
    · have : Finite PSL(2, GaloisField 2 m) := Finite.of_equiv Q e.toEquiv
      exact (CFSG.Milestones.ctgms_bender_1971_even_rank_one_model_and_strong_embedding_input_1
        m (by omega)).map_mulEquiv e.symm
  · refine ⟨2 ^ m, 3, ?_, ?_⟩
    · calc 8 = (2 ^ 1) ^ 3 := by norm_num
        _ ≤ (2 ^ m) ^ 3 := Nat.pow_le_pow_left (Nat.pow_le_pow_right (by norm_num) (by omega)) 3
    · have : Finite (PSU3 2 m) := Finite.of_equiv Q e.toEquiv
      exact (CFSG.Milestones.ctgms_bender_1971_even_rank_one_model_and_strong_embedding_input_2
        m hm).map_mulEquiv e.symm
  · refine ⟨2 ^ (2 * a + 1), 2, ?_, ?_⟩
    · calc 8 ≤ (2 ^ 1) ^ 2 * 2 := by norm_num
        _ ≤ (2 ^ (2 * a + 1)) ^ 2 := by
          have h1 : 2 ^ 1 ≤ 2 ^ (2 * a + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
          have h2 : 8 ≤ 2 ^ (2 * a + 1) :=
            calc 8 = 2 ^ 3 := by norm_num
              _ ≤ 2 ^ (2 * a + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
          nlinarith
    · have : Finite (Sz a) := Finite.of_equiv Q e.toEquiv
      exact (CFSG.Milestones.ctgms_bender_1971_even_rank_one_model_and_strong_embedding_input_4
        a ha).map_mulEquiv e.symm

theorem NativeBenderType.eight_le_card_sylow (h : NativeBenderType Q)
    (P : Sylow 2 Q) :
    8 ≤ Nat.card (P : Subgroup Q) := by
  obtain ⟨q, k, hqk, hB⟩ := h.exists_borel
  rw [(hB P).2.2.2.2]
  exact hqk

theorem isSolvable_normalizer_of_sup_cyclic {X : Type} [Group X] [Finite X] {p : ℕ}
    [Fact p.Prime] {U D : Subgroup X} (hU : IsPGroup p U) (hD : IsCyclic D)
    (hsup : U ⊔ D = normalizer (U : Set X)) : Group.IsSolvable (normalizer (U : Set X)) := by
  set N := normalizer (U : Set X)
  have hUN : U ≤ N := le_normalizer
  have hDN : D ≤ N := hsup ▸ le_sup_right
  set U' := U.subgroupOf N
  have : U'.Normal := (normal_subgroupOf_iff_le_normalizer hUN).mpr le_rfl
  have : IsPGroup p U' := hU.of_equiv (subgroupOfEquivOfLe hUN).symm
  have : Group.IsNilpotent U' := this.isNilpotent
  have htop : D.subgroupOf N ⊔ U' = ⊤ := by
    rw [← (subgroupOf_sup hDN hUN), sup_comm, hsup, subgroupOf_self]
  have hdec : ∀ x : N, ∃ d ∈ D.subgroupOf N, ∃ u ∈ U', d * u = x := fun x => by
    have hx : x ∈ ((D.subgroupOf N ⊔ U' : Subgroup N) : Set N) := by rw [htop]; trivial
    rw [mul_normal] at hx
    obtain ⟨d, hd, u, hu, rfl⟩ := hx
    exact ⟨d, hd, u, hu, rfl⟩
  have : IsMulCommutative D := hD.isMulCommutative
  have hcomm : ∀ a b : N ⧸ U', a * b = b * a := by
    intro a b
    induction a using QuotientGroup.induction_on with | H x => ?_
    induction b using QuotientGroup.induction_on with | H y => ?_
    obtain ⟨d, hd, u, hu, rfl⟩ := hdec x
    obtain ⟨d', hd', u', hu', rfl⟩ := hdec y
    have huu : ((u : N) : N ⧸ U') = 1 := (QuotientGroup.eq_one_iff _).mpr hu
    have huu' : ((u' : N) : N ⧸ U') = 1 := (QuotientGroup.eq_one_iff _).mpr hu'
    have hdd : d * d' = d' * d := by
      have h1 := isMulCommutative_iff.mp this (⟨(d : X), hd⟩ : D) ⟨(d' : X), hd'⟩
      exact Subtype.ext (congrArg (fun z : D => (z : X)) h1)
    rw [QuotientGroup.mk_mul, QuotientGroup.mk_mul, huu, huu', mul_one, mul_one,
      ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, hdd]
  have : Group.IsSolvable (N ⧸ U') := Group.isSolvable_of_comm hcomm
  exact Group.isSolvable_of_ker_le_range U'.subtype (QuotientGroup.mk' U')
    (by rw [QuotientGroup.ker_mk', range_subtype])

theorem isSolvable_centralizer_of_bender {X : Type} [Group X]
    [Finite X] (hX : fusionIsBenderGroup X) {t : X} (ht1 : t ≠ 1) (ht : t ^ 2 = 1) :
    Group.IsSolvable (centralizer ({t} : Set X)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hpt : IsPGroup 2 (zpowers t) := by
    have h2 : orderOf t = 2 := orderOf_eq_prime ht ht1
    exact IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, h2, pow_one])
  obtain ⟨U, hU⟩ := hpt.exists_le_sylow
  have htU : t ∈ (U : Subgroup X) := hU (mem_zpowers t)
  have hle := RankTwoBender.centralizer_le_normalizer_of_mem hX U htU ht1
  obtain ⟨q, k, -, hB⟩ := (AschbacherToolkit.BenderExt.benderData_of_isBenderGroup hX).borel
  obtain ⟨-, ⟨D, hcyc, -, -, hsup⟩, -⟩ := hB U
  have := isSolvable_normalizer_of_sup_cyclic U.isPGroup' hcyc hsup
  exact Group.isSolvable_of_isSolvable_injective (Subgroup.inclusion_injective hle)

end CFSG.ComponentClassification.GMS78

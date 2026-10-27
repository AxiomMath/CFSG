module

public import CFSG.LocalAnalysis.RankThreeTheoremC.KFacts.WeakClosureThree.Dispatch
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFacts.WeakClosureHeis.GlueGroup

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.WeakClosureThree

open CFSG.Open
open CFSG.RankThree.PartOne.StrongP (HasNoncommPair)
open CFSG.LocalAnalysis.RankThreeTheoremC.WeakClosureHeis

@[expose] def OmegaDichLieAt (K : Type) [Group K] [Finite K] : Prop :=
  (∀ S : Sylow 3 K, IsMulCommutative (S : Subgroup K)) ∨ HasNoncommPair 3 K ∨
    4 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup K)

@[expose] def DichThreeLieAt (K : Type) [Group K] [Finite K] : Prop :=
  OmegaDichLieAt K ∧ HeisDichAt K

section Transport

variable {K L : Type} [Group K] [Finite K] [Group L] [Finite L]

theorem OmegaDichLieAt.omegaDichAt (h : OmegaDichLieAt K) : OmegaDichAt K := by
  rcases h with h | h | h
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr (Or.inl h))

theorem DichThreeLieAt.dichThreeAt (h : DichThreeLieAt K) : DichThreeAt K :=
  ⟨h.1.omegaDichAt, h.2⟩

theorem OmegaDichLieAt.of_mulEquiv (e : K ≃* L) (h : OmegaDichLieAt L) : OmegaDichLieAt K := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  rcases h with h | h | h
  · exact Or.inl (sylow_comm_of_mulEquiv e h)
  · exact Or.inr (Or.inl (h.map e.symm.toMonoidHom e.symm.injective))
  · refine Or.inr (Or.inr ?_)
    have := pRank_map_mulEquiv (p := 3) e (⊤ : Subgroup K)
    rw [Subgroup.map_top_of_surjective _ e.surjective] at this
    omega

theorem DichThreeLieAt.of_mulEquiv (e : K ≃* L) (h : DichThreeLieAt L) : DichThreeLieAt K :=
  ⟨OmegaDichLieAt.of_mulEquiv e h.1, HeisDichAt.of_mulEquiv e h.2⟩

end Transport

variable {K : Type} [Group K] [Finite K]

theorem factorization_lt_of_not_dvd {k : ℕ} (h : ¬ 3 ^ k ∣ Nat.card K) :
    (Nat.card K).factorization 3 < k := by
  by_contra hle
  push Not at hle
  exact h ((Nat.prime_three.pow_dvd_iff_le_factorization Nat.card_pos.ne').2 hle)

theorem sylow_comm_of_factorization_le_two (h : (Nat.card K).factorization 3 ≤ 2) :
    ∀ S : Sylow 3 K, IsMulCommutative (S : Subgroup K) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  intro S
  by_contra hS
  have h1 := pow_three_le_card_of_nonabelian S.isPGroup' hS
  rw [S.card_eq_multiplicity] at h1
  have h2 : 3 ^ (Nat.card K).factorization 3 ≤ 3 ^ 2 := Nat.pow_le_pow_right (by norm_num) h
  omega

theorem dichThreeLieAt_of_factorization_le_two (h : (Nat.card K).factorization 3 ≤ 2) :
    DichThreeLieAt K :=
  ⟨Or.inl (sylow_comm_of_factorization_le_two h),
    Or.inl (SylowDichotomyAt.of_factorization_le (by omega))⟩

theorem dichThreeAt_of_factorization_le_two (h : (Nat.card K).factorization 3 ≤ 2) :
    DichThreeAt K :=
  (dichThreeLieAt_of_factorization_le_two h).dichThreeAt

theorem dichThreeAt_of_not_dvd_27 (h : ¬ 27 ∣ Nat.card K) : DichThreeAt K := by
  have := factorization_lt_of_not_dvd (K := K) (k := 3) (by norm_num; exact h)
  exact dichThreeAt_of_factorization_le_two (by omega)

theorem dichThreeAt_of_pair (h : ¬ 81 ∣ Nat.card K) (hp : HasNoncommPair 3 K) :
    DichThreeAt K := by
  have := factorization_lt_of_not_dvd (K := K) (k := 4) (by norm_num; exact h)
  exact ⟨Or.inr (Or.inl hp), Or.inl (SylowDichotomyAt.of_factorization_le (by omega))⟩

theorem dichThreeLieAt_of_pair_of_le (h : (Nat.card K).factorization 3 ≤ 3)
    (hp : HasNoncommPair 3 K) : DichThreeLieAt K :=
  ⟨Or.inr (Or.inl hp), Or.inl (SylowDichotomyAt.of_factorization_le h)⟩

theorem dichThreeLieAt_of_elemAbelian {E : Subgroup K} (hE : IsElemAbelian 3 E)
    (hcard : Nat.card E = 3 ^ 4) : DichThreeLieAt K :=
  ⟨Or.inr (Or.inr (le_pRank_of_elemAbelian (by norm_num) le_top hE hcard)),
    Or.inl (SylowDichotomyAt.of_elemAbelian Nat.prime_three hE hcard le_rfl)⟩

theorem dichThreeAt_of_elemAbelian {E : Subgroup K} (hE : IsElemAbelian 3 E)
    (hcard : Nat.card E = 3 ^ 4) : DichThreeAt K :=
  (dichThreeLieAt_of_elemAbelian hE hcard).dichThreeAt

theorem dichThreeLieAt_of_pair_exponent (hp : HasNoncommPair 3 K) {U : Subgroup K}
    (hU : IsPGroup 3 U) (hexp : ∀ u ∈ U, u ^ 3 = 1) (hcard : 3 ^ 5 ≤ Nat.card U) :
    DichThreeLieAt K :=
  ⟨Or.inr (Or.inl hp), Or.inl (SylowDichotomyAt.of_exponent hU hexp hcard)⟩

theorem dichThreeAt_of_pair_exponent (hp : HasNoncommPair 3 K) {U : Subgroup K}
    (hU : IsPGroup 3 U) (hexp : ∀ u ∈ U, u ^ 3 = 1) (hcard : 3 ^ 5 ≤ Nat.card U) :
    DichThreeAt K :=
  (dichThreeLieAt_of_pair_exponent hp hU hexp hcard).dichThreeAt

theorem dichThreeLieAt_of_pair_derived (hp : HasNoncommPair 3 K) {U : Subgroup K}
    (hU : IsPGroup 3 U) (hnc : ¬ IsCyclic ↥⁅U, U⁆) : DichThreeLieAt K :=
  ⟨Or.inr (Or.inl hp), Or.inl (SylowDichotomyAt.of_not_cyclic_derived hU hnc)⟩

theorem dichThreeAt_of_centralFusion (h : CentralFusionAt K) : DichThreeAt K :=
  ⟨Or.inr (Or.inr (Or.inr h)), Or.inr h⟩

theorem dichThreeLieAt_of_four_le_pRank (h : 4 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup K)) :
    DichThreeLieAt K :=
  ⟨Or.inr (Or.inr h), Or.inl (SylowDichotomyAt.of_four_le_pRank_top Nat.prime_three h)⟩

theorem sylow_comm_of_abelian_full {A : Subgroup K} (hA : IsMulCommutative A)
    (hcard : Nat.card A = 3 ^ (Nat.card K).factorization 3) :
    ∀ S : Sylow 3 K, IsMulCommutative (S : Subgroup K) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  intro S
  let A' : Sylow 3 K := Sylow.ofCard A hcard
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq K A' S
  have h2 : ((g • A' : Sylow 3 K) : Subgroup K) = (S : Subgroup K) := congrArg _ hg
  have hA' : (A' : Subgroup K) = A := Sylow.coe_ofCard _ _
  have hS : (S : Subgroup K) = A.map (MulAut.conj g).toMonoidHom := by
    rw [← h2, Sylow.coe_subgroup_smul, hA']
    ext x
    simp [Subgroup.mem_map, Subgroup.mem_smul_pointwise_iff_exists]
  rw [hS]
  exact (isMulCommutative_map_iff_of_injective _ (MulAut.conj g).injective A).2 hA

theorem dichThreeLieAt_of_factorization_le_pRank
    (h : (Nat.card K).factorization 3 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup K)) :
    DichThreeLieAt K := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hne : {k | ∃ E : Subgroup K, E ≤ ⊤ ∧ IsElemAbelian 3 E ∧ Nat.card E = 3 ^ k}.Nonempty :=
    ⟨0, ⊥, bot_le, ⟨inferInstance, fun x hx => by rw [(Subgroup.mem_bot).1 hx, one_pow]⟩,
      by simp⟩
  have hbdd : BddAbove {k | ∃ E : Subgroup K, E ≤ ⊤ ∧ IsElemAbelian 3 E ∧
      Nat.card E = 3 ^ k} := by
    refine ⟨Nat.card K, ?_⟩
    rintro k' ⟨E', -, -, hk'⟩
    have h1 : 3 ^ k' ≤ Nat.card K := hk' ▸ Subgroup.card_le_card_group E'
    exact (Nat.lt_pow_self (by norm_num)).le.trans h1
  obtain ⟨E, -, hE, hk⟩ := Nat.sSup_mem hne hbdd
  set j := sSup {k | ∃ E : Subgroup K, E ≤ ⊤ ∧ IsElemAbelian 3 E ∧ Nat.card E = 3 ^ k}
  have hj : (Nat.card K).factorization 3 ≤ j := h
  have hEp : IsPGroup 3 E := IsPGroup.of_card hk
  obtain ⟨P, hEP⟩ := hEp.exists_le_sylow
  have hle := Subgroup.card_le_of_le hEP
  rw [hk, P.card_eq_multiplicity] at hle
  have hj' : j ≤ (Nat.card K).factorization 3 :=
    (Nat.pow_le_pow_iff_right (by norm_num)).1 hle
  have hcard : Nat.card E = 3 ^ (Nat.card K).factorization 3 := by
    rw [hk, show j = (Nat.card K).factorization 3 by omega]
  exact ⟨Or.inl (sylow_comm_of_abelian_full hE.1 hcard),
    Or.inl (SylowDichotomyAt.of_abelian_full Nat.prime_three hE.1 hcard)⟩

end CFSG.LocalAnalysis.RankThreeTheoremC.WeakClosureThree

module

public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.I291P65Defs
public import CFSG.LocalAnalysis.RankFourTheoremC.InvariantTwo.KFacts.Lemma212InputsProofCoverLie
public import CFSG.GH74.L5U5.Models
public import CFSG.Models.PGLSimple

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.KD309M

open CFSG.Open CFSG.Open.StatedAPI Subgroup
open CFSG.LocalAnalysis.RankFourTheoremC (IsLinearOrUnitaryAt exists_char_pow_card)

theorem center_eq_bot_of_simple {L : Type} [Group L] [IsSimpleGroup L]
    (hperf : commutator L = ⊤) : center L = ⊥ := by
  haveI : Group.IsPerfect L := ⟨hperf⟩
  exact TauCeti.IsSimpleGroup.center_eq_bot_of_not_isMulCommutative
    (Group.IsPerfect.not_isMulCommutative L)

theorem linuni_of_sl {L : Type} [Group L] {K : Type} [Field K] [Finite K]
    (hpK : 5 ∣ Nat.card K - 1) (e : L ≃* StatedSL 5 K) :
    IsLinearOrUnitaryAt 5 (L ⧸ center L) := by
  refine Or.inl ⟨5, K, inferInstance, inferInstance, dvd_refl 5, hpK, ⟨?_⟩⟩
  exact (QuotientGroup.congr _ _ e (CFSG.LieType.Universal.Unitary.map_center_mulEquiv e)).trans
    (QuotientGroup.quotientMulEquivOfEq (CFSG.GH74.L5U5.center_statedSL_eq 5))

theorem center_eq_bot_of_psl {L : Type} [Group L] (hperf : commutator L = ⊤) {K : Type} [Field K]
    (e : L ≃* StatedProj (StatedSL 5 K)) : center L = ⊥ := by
  haveI : IsSimpleGroup (StatedProj (StatedSL 5 K)) :=
    isSimpleGroup_statedProj_statedSL K (by norm_num) (Or.inl (by norm_num))
      (Or.inl (by norm_num))
  haveI : IsSimpleGroup L := e.isSimpleGroup
  exact center_eq_bot_of_simple hperf

theorem linuni_of_psl {L : Type} [Group L] (hperf : commutator L = ⊤) {K : Type} [Field K]
    [Finite K] (hpK : 5 ∣ Nat.card K - 1) (e : L ≃* StatedProj (StatedSL 5 K)) :
    IsLinearOrUnitaryAt 5 (L ⧸ center L) := by
  refine Or.inl ⟨5, K, inferInstance, inferInstance, dvd_refl 5, hpK, ⟨?_⟩⟩
  have hZ : center L = ⊥ := center_eq_bot_of_psl hperf e
  exact ((QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot).trans e

theorem exists_char_pow_of_sq {K : Type} [Field K] [Finite K] {q : ℕ} (hK : Nat.card K = q ^ 2) :
    ∃ r f : ℕ, r.Prime ∧ q = r ^ f := by
  obtain ⟨r, m, hr, -, -, hKr⟩ := exists_char_pow_card K
  obtain ⟨f, -, hqf⟩ : ∃ f ≤ m, q = r ^ f := by
    refine (Nat.dvd_prime_pow hr).1 ?_
    rw [← hKr, hK]
    exact dvd_pow_self q two_ne_zero
  exact ⟨r, f, hr, hqf⟩

theorem linuni_of_su {L : Type} [Group L] {K : Type} [Field K] [Finite K] {q : ℕ}
    (hK : Nat.card K = q ^ 2) (hpq : 5 ∣ q + 1) (e : L ≃* StatedSU 5 q K) :
    IsLinearOrUnitaryAt 5 (L ⧸ center L) := by
  obtain ⟨r, f, hr, rfl⟩ := exists_char_pow_of_sq hK
  haveI : Fact r.Prime := ⟨hr⟩
  have hnq : (5, r ^ f) ≠ (3, 2) := fun h => by simpa using congrArg Prod.fst h
  refine Or.inr ⟨5, r ^ f, K, inferInstance, inferInstance, hK, dvd_refl 5, hpq, ⟨?_⟩⟩
  exact (QuotientGroup.congr _ _ e (CFSG.LieType.Universal.Unitary.map_center_mulEquiv e)).trans
    (QuotientGroup.quotientMulEquivOfEq
      (CFSG.LieType.Universal.Unitary.isQuasisimple_statedSU_of_card hK (by norm_num) hnq).2)

theorem center_eq_bot_of_psu {L : Type} [Group L] (hperf : commutator L = ⊤) {K : Type} [Field K]
    [Finite K] {q : ℕ} (hK : Nat.card K = q ^ 2) (e : L ≃* StatedProj (StatedSU 5 q K)) :
    center L = ⊥ := by
  obtain ⟨r, f, hr, rfl⟩ := exists_char_pow_of_sq hK
  haveI : Fact r.Prime := ⟨hr⟩
  have hnq : (5, r ^ f) ≠ (3, 2) := fun h => by simpa using congrArg Prod.fst h
  haveI : IsSimpleGroup (StatedProj (StatedSU 5 (r ^ f) K)) :=
    CFSG.ClassicalGroups.Unitary.isSimpleGroup_statedProj_statedSU K r f hK 5 (by norm_num) hnq
  haveI : IsSimpleGroup L := e.isSimpleGroup
  exact center_eq_bot_of_simple hperf

theorem linuni_of_psu {L : Type} [Group L] (hperf : commutator L = ⊤) {K : Type} [Field K]
    [Finite K] {q : ℕ} (hK : Nat.card K = q ^ 2) (hpq : 5 ∣ q + 1)
    (e : L ≃* StatedProj (StatedSU 5 q K)) : IsLinearOrUnitaryAt 5 (L ⧸ center L) := by
  obtain ⟨r, f, hr, rfl⟩ := exists_char_pow_of_sq hK
  refine Or.inr ⟨5, r ^ f, K, inferInstance, inferInstance, hK, dvd_refl 5, hpq, ⟨?_⟩⟩
  have hZ : center L = ⊥ := center_eq_bot_of_psu hperf hK e
  exact ((QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot).trans e

theorem is29a_isLinearOrUnitaryAt {L : Type} [Group L] (hq : CFSG.Open.IsQuasisimple L)
    (h : I291P65.Is29a L) : IsLinearOrUnitaryAt 5 (L ⧸ center L) := by
  rcases h with ⟨K, _, _, hpK, he⟩ | ⟨q, K, _, _, hK, hpq, he⟩
  · rcases he with ⟨⟨e⟩⟩ | ⟨⟨e⟩⟩
    · exact linuni_of_sl hpK e
    · exact linuni_of_psl hq.1 hpK e
  · rcases he with ⟨⟨e⟩⟩ | ⟨⟨e⟩⟩
    · exact linuni_of_su hK hpq e
    · exact linuni_of_psu hq.1 hK hpq e

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.KD309M

module

public import CFSG.LocalAnalysis.ComponentClassification.AschbacherToolkitBenderBasic
public import CFSG.Milestones.CTGMS_Bender_1971_even_rank_one_model_and_strong_embedding_input
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherTheorem3Statement

public section

namespace CFSG.ComponentClassification.AschbacherTheorem3.FourEight

open CFSG.ComponentClassification.AschbacherTightEmbedding
open CFSG.ABGLocalTools
open CFSG.Open
open scoped MatrixGroups

variable {X : Type} [Group X] [Finite X]

theorem exists_benderBorel {L : Subgroup X} {n : ℕ} (hB : IsBenderType L n) :
    ∃ k : ℕ, 1 ≤ k ∧ fusionBenderBorel L (2 ^ n) k ∧
      (k = 1 → 2 ≤ n ∧ Nonempty (L ≃* PSL(2, GaloisField 2 n))) := by
  rcases hB with ⟨hn, ⟨e⟩⟩ | ⟨m, hm, rfl, ⟨e⟩⟩ | ⟨hn, ⟨e⟩⟩
  · have : Finite PSL(2, GaloisField 2 n) := Finite.of_surjective e e.surjective
    exact ⟨1, le_rfl,
      (CFSG.Milestones.ctgms_bender_1971_even_rank_one_model_and_strong_embedding_input_1 n
        hn).map_mulEquiv e.symm, fun _ => ⟨hn, ⟨e⟩⟩⟩
  · have : Finite (Sz m) := Finite.of_surjective e e.surjective
    exact ⟨2, by norm_num,
      (CFSG.Milestones.ctgms_bender_1971_even_rank_one_model_and_strong_embedding_input_4 m
        hm).map_mulEquiv e.symm, fun h => absurd h (by norm_num)⟩
  · have : Finite (PSU3 2 n) := Finite.of_surjective e e.surjective
    exact ⟨3, by norm_num,
      (CFSG.Milestones.ctgms_bender_1971_even_rank_one_model_and_strong_embedding_input_2 n
        hn).map_mulEquiv e.symm, fun h => absurd h (by norm_num)⟩

theorem bender_sylow {L P : Subgroup X} {n : ℕ} (hB : IsBenderType L n) (hP : IsSylowOf 2 P L) :
    (∀ x ∈ P, x ^ 2 = 1 → ∀ p ∈ P, x * p = p * x) ∧
    (Nat.card P ≤ 2 ^ n → 2 ≤ n ∧ Nonempty (L ≃* PSL(2, GaloisField 2 n))) := by
  obtain ⟨k, hk, hBB, hk1⟩ := exists_benderBorel hB
  obtain ⟨Q, hQ⟩ := hP
  obtain ⟨hSE, -, hZ2, hZcard, hQcard⟩ := hBB Q
  have hcardP : Nat.card P = (2 ^ n) ^ k := by
    rw [← hQ, Subgroup.card_map_of_injective L.subtype_injective, hQcard]
  have hn : 1 ≤ n := by
    rcases hB with ⟨hn, -⟩ | ⟨m, hm, rfl, -⟩ | ⟨hn, -⟩ <;> omega
  refine ⟨?_, fun hle => hk1 ?_⟩
  ·
    intro x hx hx2 p hp
    rw [← hQ] at hx hp
    obtain ⟨l, hlQ, rfl⟩ := hx
    obtain ⟨l', hl'Q, rfl⟩ := hp
    by_cases hl1 : l = 1
    · rw [hl1]
      simp
    have hl2 : l ^ 2 = 1 := Subtype.ext (by simpa using hx2)
    obtain ⟨z, hz1⟩ : ∃ z : Subgroup.center (Q : Subgroup L), z ≠ 1 := by
      have h1 : 1 < Nat.card (Subgroup.center (Q : Subgroup L)) := by
        rw [hZcard]
        exact Nat.one_lt_two_pow (by omega)
      have := Finite.one_lt_card_iff_nontrivial.mp h1
      exact exists_ne 1
    set z' : L := ((z : Q) : L) with hz'def
    have hz'Q : z' ∈ (Q : Subgroup L) := (z : Q).2
    have hz'1 : z' ≠ 1 := by
      intro h
      apply hz1
      exact Subtype.ext (Subtype.ext h)
    have hz'2 : z' ^ 2 = 1 := by
      have := congrArg Subtype.val (hZ2 (z : Q) z.2)
      simpa [hz'def] using this
    have hM :=
      CFSG.ComponentClassification.AschbacherToolkit.Bender.isStronglyEmbedded_of_fusion hSE
    obtain ⟨c, hcN, hc⟩ := hM.involutions_conjugate_in (Subgroup.le_normalizer hz'Q)
      ⟨hz'1, hz'2⟩ (Subgroup.le_normalizer hlQ) ⟨hl1, hl2⟩
    change c⁻¹ * z' * c = l at hc
    have hcomm : l * l' = l' * l := by
      have hl'c : c * l' * c⁻¹ ∈ (Q : Subgroup L) :=
        (Subgroup.mem_normalizer_iff.mp hcN l').mp hl'Q
      have hzc : z' * (c * l' * c⁻¹) = (c * l' * c⁻¹) * z' := by
        have := Subgroup.mem_center_iff.mp z.2 ⟨_, hl'c⟩
        exact (congrArg Subtype.val this).symm
      rw [← hc]
      calc c⁻¹ * z' * c * l' = c⁻¹ * (z' * (c * l' * c⁻¹)) * c := by group
        _ = c⁻¹ * ((c * l' * c⁻¹) * z') * c := by rw [hzc]
        _ = l' * (c⁻¹ * z' * c) := by group
    simpa using congrArg Subtype.val hcomm
  ·
    by_contra hk1'
    have hk2 : 2 ≤ k := by omega
    rw [hcardP] at hle
    have h1 : (2 ^ n) ^ 2 ≤ (2 ^ n) ^ k :=
      Nat.pow_le_pow_right (Nat.pos_of_ne_zero (by positivity)) hk2
    have h2 : 2 ^ n < (2 ^ n) ^ 2 := by
      have h3 : 1 < 2 ^ n := Nat.one_lt_two_pow (by omega)
      calc 2 ^ n = 2 ^ n * 1 := (mul_one _).symm
        _ < 2 ^ n * 2 ^ n := Nat.mul_lt_mul_of_pos_left h3 (by positivity)
        _ = (2 ^ n) ^ 2 := (pow_two _).symm
    omega

end CFSG.ComponentClassification.AschbacherTheorem3.FourEight

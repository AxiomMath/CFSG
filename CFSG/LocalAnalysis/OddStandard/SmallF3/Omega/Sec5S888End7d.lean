module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5S888End5c
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5S888End6b
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5S888End7c

public section

open CFSG.Open CFSG.Goldschmidt Subgroup CFSG.GH74.GLS.Th2.P412
open scoped MatrixGroups

namespace CFSG.OddStandard.SmallF3.Omega

theorem caseB_component (hN11b : S_N11b) {Y : Type} [Group Y] [Finite Y]
    (hY : IsGoldSemisimple Y) (D : Sylow 2 Y) {W : Fin 4 → Subgroup Y} {τ : Fin 4 → Y ≃* Y}
    (hP : IsPlanes (D : Subgroup Y) W) (hτ : IsPlaneAuts (D : Subgroup Y) W τ)
    (hperm : ∀ y : Y, (∀ x ∈ (D : Subgroup Y), y * x * y⁻¹ ∈ (D : Subgroup Y)) →
      ∀ i, ∃ j, ∀ w ∈ W i, y * w * y⁻¹ ∈ W j) :
    ∃ (J : Subgroup Y) (i : Fin 4) (p n : ℕ) (_ : Fact p.Prime), IsComponentOf J ⊤ ∧ W i ≤ J ∧
      Nat.card ↥((D : Subgroup Y) ⊓ J) = 4 ∧ Odd p ∧ 0 < n ∧ 5 ≤ p ^ n ∧
        (p ^ n % 8 = 3 ∨ p ^ n % 8 = 5) ∧ Nonempty (↥J ≃* PSL(2, GaloisField p n)) := by
  classical
  have hZ : Subgroup.center Y = ⊥ := GoldY.center_eq_bot hY.o2 hY.odd hY.layer
  have hcomp : ∃ J : Subgroup Y, IsComponentOf J ⊤ := by
    by_contra h
    have hset : {K : Subgroup Y | IsComponentOf K ⊤} = ∅ := by
      ext K
      simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
      exact fun hK => h ⟨K, hK⟩
    have hbot : goldschmidtLayer Y = ⊥ := by
      rw [goldschmidtLayer.eq_sSup, hset, sSup_empty]
    have htopbot : (⊤ : Subgroup Y) = ⊥ := by rw [← hY.layer, hbot]
    have hDbot : (D : Subgroup Y) = ⊥ := by
      rw [← le_bot_iff, ← htopbot]
      exact le_top
    have hcard1 : Nat.card (D : Subgroup Y) = 1 := by rw [hDbot, Subgroup.card_bot]
    rw [hP.card_D] at hcard1
    exact (by norm_num : (2 : ℕ) ^ 8 ≠ 1) hcard1
  obtain ⟨J, hJ⟩ := hcomp
  obtain ⟨hm1, hcard⟩ := plane_le_component hN11b hY D hP hτ hJ
  have hm_le : Nat.card {i : Fin 4 // W i ≤ J} ≤ 4 := by
    have h := Finite.card_subtype_le (fun i : Fin 4 => W i ≤ J)
    rwa [Nat.card_fin] at h
  have hne : Nonempty {i : Fin 4 // W i ≤ J} := by
    rw [← Fintype.card_pos_iff, ← Nat.card_eq_fintype_card]
    omega
  obtain ⟨i, hi⟩ := hne
  rcases component_classification hY D hP.comm hJ hm1 hcard with
      ⟨hm_eq, p, n, hp, hpodd, hn, h5, h8, e⟩ | ⟨f, hfeq, hf3, e⟩
  · refine ⟨J, i, p, n, hp, hJ, hi, ?_, hpodd, hn, h5, h8, e⟩
    rw [hcard, hm_eq, pow_one]
  · exfalso
    have hf : f = 4 ∨ f = 6 ∨ f = 8 := by omega
    exact false_of_psl2_even hY.layer hZ D hP hperm hJ hf e.some

end CFSG.OddStandard.SmallF3.Omega

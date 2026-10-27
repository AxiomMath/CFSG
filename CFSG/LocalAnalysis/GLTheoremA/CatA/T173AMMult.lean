module

public import CFSG.Milestones.CL_LIT_Griess_Schur_multipliers_Lie_type
import CFSG.Assembly.GL83StatedBridge
import CFSG.RankThree.GF2n.Stroth80.GriessLinear
public import CFSG.LinearAlgebra.LinearGroups.UnitaryScalarKernel
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.GLTheoremA.PartI.KD26
public import CFSG.LocalAnalysis.StandardType.MarkingClassical

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T173A

open CFSG CFSG.Open CFSG.Assembly CFSG.LocalAnalysis.GLTheoremA CFSG.Blueprint


private theorem exceptionalOrders_psu_our {d n : ℕ} (hn : 1 ≤ n) (hd4 : d ≠ 4) :
    Multiplier.exceptionalOrders .PSU d 2 n = if d = 6 ∧ n = 1 then (2, 2) else (1, 1) := by
  by_cases h : d = 6 ∧ n = 1
  · rw [if_pos h]
    obtain ⟨rfl, rfl⟩ := h
    rfl
  · rw [if_neg h]
    by_cases hn1 : n = 1
    · subst hn1
      by_cases hd6 : d = 6
      · exact absurd ⟨hd6, rfl⟩ h
      · unfold Multiplier.exceptionalOrders
        split <;> first | rfl | (exfalso; simp_all)
    · have hn2 : 2 ≤ n := by omega
      unfold Multiplier.exceptionalOrders
      split <;> first | rfl | (exfalso; simp_all <;> omega)

private theorem card_hopfMultiplier_of_blueprint_PSL {X : Type} [Group X] {d n : ℕ}
    (hm : Blueprint.LieModel X .PSL d 2 n) (hn : 2 ≤ n) (hd : 3 ≤ d)
    (hne : ¬ (d = 3 ∧ n = 2)) :
    Nat.card (CFSG.Open.griessHopfMultiplier X) = Nat.gcd d (2 ^ n - 1) := by
  obtain ⟨-, ⟨e⟩⟩ := CFSG.Milestones.cl_lit_griess_schur_multipliers_all_native_models
    X .PSL d 2 n hm
  rw [Nat.card_congr e.toEquiv,
    CFSG.RankThree.GF2n.Stroth80.card_generic_prod_exceptional,
    CFSG.RankThree.GF2n.Stroth80.genericOrders_psl,
    CFSG.RankThree.GF2n.Stroth80.exceptionalOrders_psl_eq_one hn (by omega) hne]
  simp

private theorem card_hopfMultiplier_of_blueprint_PSU {X : Type} [Group X] {d n : ℕ}
    (hm : Blueprint.LieModel X .PSU d 2 n) (hn : 1 ≤ n) (hd4 : d ≠ 4) :
    Nat.card (CFSG.Open.griessHopfMultiplier X) =
      Nat.gcd d (2 ^ n + 1) * 2 ^ (if d = 6 ∧ n = 1 then 2 else 0) := by
  obtain ⟨-, ⟨e⟩⟩ := CFSG.Milestones.cl_lit_griess_schur_multipliers_all_native_models
    X .PSU d 2 n hm
  rw [Nat.card_congr e.toEquiv,
    CFSG.RankThree.GF2n.Stroth80.card_generic_prod_exceptional,
    show Multiplier.genericOrders .PSU d 2 n = (Nat.gcd d (2 ^ n + 1), 1) from rfl,
    exceptionalOrders_psu_our hn hd4]
  by_cases h : d = 6 ∧ n = 1
  · simp [h]
  · simp [h]

theorem lin_hopf_row {d n : ℕ} {F : Type} [Field F] [Finite F] (hF : Nat.card F = 2 ^ n)
    (hn : 2 ≤ n) (hd : 3 ≤ d) (hne : ¬ (d = 3 ∧ n = 2)) :
    Finite (CFSG.Open.griessHopfMultiplier (LargeEvenProj (LargeEvenSLGroup (Fin d) F))) ∧
      Nat.card (CFSG.Open.griessHopfMultiplier (LargeEvenProj (LargeEvenSLGroup (Fin d) F))) ∣
        Nat.card (LargeEvenProjMk (LargeEvenSLGroup (Fin d) F)).ker := by
  have hadm : StatedLieAdmissible .PSL d 2 n :=
    ⟨Nat.prime_two, by omega, by omega, fun h => by simp at h; omega,
      fun h => by simp at h; omega⟩
  have hm : Blueprint.LieModel (LargeEvenProj (LargeEvenSLGroup (Fin d) F)) .PSL d 2 n :=
    Or.inl ⟨by decide, CFSG.StandardType.statedClassicalModel_linear (K := F) d n hF hadm⟩
  have hcardM := card_hopfMultiplier_of_blueprint_PSL hm hn hd hne
  have hcardK : Nat.card (LargeEvenProjMk (LargeEvenSLGroup (Fin d) F)).ker =
      Nat.gcd d (2 ^ n - 1) := by
    rw [QuotientGroup.ker_mk', CFSG.Assembly.largeEvenSLGroup_eq_statedSL,
      CFSG.Assembly.largeEvenScalars_eq_statedScalars]
    rw [CFSG.RankThree.GF2n.Stroth80.card_statedScalars_subgroupOf_statedSL (K := F) (m := d)
      (by omega), hF]
  refine ⟨?_, ?_⟩
  · exact Nat.finite_of_card_ne_zero
      (by rw [hcardM]; exact (Nat.gcd_pos_of_pos_left (2 ^ n - 1) (by omega)).ne')
  · rw [hcardM, hcardK]

theorem uni_hopf_row {d n : ℕ} {F : Type} [Field F] [Finite F] (hF : Nat.card F = (2 ^ n) ^ 2)
    (hn : 1 ≤ n) (hd : 3 ≤ d) (hdn : d = 3 → 2 ≤ n) (hd4 : d ≠ 4) :
    Finite (CFSG.Open.griessHopfMultiplier
      (LargeEvenProj (LargeEvenSUGroup (Fin d) F (2 ^ n)))) ∧
      Nat.card (CFSG.Open.griessHopfMultiplier
        (LargeEvenProj (LargeEvenSUGroup (Fin d) F (2 ^ n)))) ∣
        Nat.card (LargeEvenProjMk (LargeEvenSUGroup (Fin d) F (2 ^ n))).ker *
          2 ^ (if d = 6 ∧ n = 1 then 2 else 0) := by
  have hnf : (d, 2 ^ n) ≠ (3, 2) := by
    intro h
    have h1 : d = 3 := congrArg Prod.fst h
    have h2 : 2 ^ n = 2 := congrArg Prod.snd h
    have hn2 : 2 ≤ n := hdn h1
    have h4 : 4 ≤ 2 ^ n := by
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn2
    omega
  have hadm : StatedLieAdmissible .PSU d 2 n := ⟨Nat.prime_two, hn, hd, hnf⟩
  have hm : Blueprint.LieModel (LargeEvenProj (LargeEvenSUGroup (Fin d) F (2 ^ n))) .PSU d 2 n :=
    Or.inl ⟨by decide, CFSG.StandardType.statedClassicalModel_unitary (K := F) d n hF hadm⟩
  have hcardM := card_hopfMultiplier_of_blueprint_PSU hm hn hd4
  have hcardK : Nat.card (LargeEvenProjMk (LargeEvenSUGroup (Fin d) F (2 ^ n))).ker =
      Nat.gcd d (2 ^ n + 1) := by
    rw [QuotientGroup.ker_mk', CFSG.Assembly.largeEvenSUGroup_eq_statedSU,
      CFSG.Assembly.largeEvenScalars_eq_statedScalars]
    exact (CFSG.LinearGroups.unitary_scalar_kernel (K := F) (p := 2) (f := n)
      Nat.prime_two hF (n := d) (by omega)).2.2
  refine ⟨?_, ?_⟩
  · exact Nat.finite_of_card_ne_zero
      (by rw [hcardM]
          exact (mul_pos (Nat.gcd_pos_of_pos_left (2 ^ n + 1) (by omega))
            (pow_pos (by norm_num) _)).ne')
  · rw [hcardM, hcardK]

end CFSG.LocalAnalysis.GLTheoremA.T173A

end

module

public import CFSG.Open.StatedDefs
public import CFSG.LocalAnalysis.AGL81TheoremCD.Section15.K35Inner
import CFSG.HardMathSupport.Timmesfeld.Tables.T1b.LinModelAut
import CFSG.LocalAnalysis.AGL81TheoremCD.Section15.K35PlaneSL
import CFSG.LocalAnalysis.AGL81TheoremCD.Section15.K35PlaneSU
import CFSG.LocalAnalysis.AGL81TheoremCD.Section15.K35BlockSU
import CFSG.LocalAnalysis.ComponentInitial.LinearHigherFieldInvolution
import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherPrimeFormRealization
import CFSG.RankThree.PartTwo.Sec21.Hering214KEig
public import CFSG.GroupTheory.LocalCores.Fitting
public import CFSG.LocalAnalysis.ComponentClassification.DisjointSolvableKernels
public import CFSG.LocalAnalysis.ComponentClassification.LayerMultiplication
public import CFSG.LocalAnalysis.ComponentClassification.MinimalBCenter
public import CFSG.LocalAnalysis.ComponentClassification.OrdinaryComponentJoins
public import CFSG.LocalAnalysis.ComponentClassification.TwoLayer
public import CFSG.LocalAnalysis.ComponentClassification.UniversalOrbitBlock
public import CFSG.Open.GLBDefs
import CFSG.ClassicalInvolution.WeakCT.StandardPair
import CFSG.ClassicalInvolution.WeakCT.TorusAgree
import CFSG.LieType.CurtisTits.SpecialLinear
import CFSG.LocalAnalysis.ComponentInitial.LinearInvolutionFixedField
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Defs

public section

namespace CFSG.LocalAnalysis.AGL81TheoremCD.Section15.K35

open CFSG.Open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher CFSG.HardMathSupport.Timmesfeld.Tables
open CFSG.RankThree.PartTwo.Sec21

theorem k35Good_of_psl {X : Type} [Group X] {n r f : ℕ} (hm : StatedClassicalModel X .PSL n r f)
    (hn : 3 ≤ n) (h3 : 3 ∣ r ^ f - 1) : K35Good X := by
  obtain ⟨K, _, hK, _, ⟨e⟩⟩ := T1b.exists_mulEquiv_projectiveSL hm
  have hq : 3 ∣ Nat.card K - 1 := by rw [hK]; exact h3
  refine K35Good.of_mulEquiv e ?_
  intro A hA hA9
  rcases exists_inner_or_conj_fieldAut_psl hn hq hA.2 hA9 with hinn | ⟨h9, α, hαA, σ, B, hσ, rfl⟩
  · exact Or.inl hinn
  refine Or.inr (Or.inl ⟨_, hαA, fun h1 => ?_, ?_⟩)
  · have hf : conjAut n K 1 * fieldAut n K σ = 1 := by
      rw [map_one, one_mul]
      calc fieldAut n K σ = (conjAut n K B)⁻¹ *
            (conjAut n K B * fieldAut n K σ * (conjAut n K B)⁻¹) * conjAut n K B := by group
        _ = 1 := by rw [h1]; group
    rw [(eq_one_of_conjAut_mul_fieldAut_eq_one hn 1 σ hf).1, orderOf_one] at hσ
    omega
  · have h9n : 9 ∣ n := h9.trans (Nat.gcd_dvd_left _ _)
    have hn8 : 8 ≤ n := by have := Nat.le_of_dvd (by omega) h9n; omega
    obtain ⟨ω, hω, hω1⟩ := Hering214.exists_primitive_cube_root hq
    have hω3 : ω ^ 3 = 1 := by linear_combination (ω - 1) * hω
    have hσ3 : σ ^ 3 = 1 := by rw [← hσ]; exact pow_orderOf_eq_one σ
    exact (fixedBlocks_fieldAut hn8 hω3 hω1 σ
      (Hering214.ringEquiv_fixes_cube_root hσ3 hω hω1)).conj _

theorem k35Good_of_psu {X : Type} [Group X] {n r f : ℕ} (hm : StatedClassicalModel X .PSU n r f)
    (h3 : 3 ∣ r ^ f + 1) : K35Good X := by
  obtain ⟨K, _, h, hq, hn, ⟨e⟩⟩ := T1b.exists_mulEquiv_primeFormP hm
  have : Finite K := h.finite
  refine K35Good.of_mulEquiv e ?_
  intro A hA hA9
  rcases exists_inner_or_conj_fieldAut_psu h hn hq h3 hA.2 hA9 with
    hinn | ⟨h9, α, hαA, σ, M, hσ, rfl⟩
  · exact Or.inl hinn
  refine Or.inr (Or.inl ⟨_, hαA, fun h1 => ?_, ?_⟩)
  · have hf : primeFormFieldHom h isPrimeFormGram_one σ = 1 :=
      calc primeFormFieldHom h isPrimeFormGram_one σ = (primeFormConjHom h _ M)⁻¹ *
            (primeFormConjHom h _ M * primeFormFieldHom h isPrimeFormGram_one σ *
              (primeFormConjHom h _ M)⁻¹) * primeFormConjHom h _ M := by group
        _ = 1 := by rw [h1]; group
    have h2 := primeFormFieldFactor_apply h isPrimeFormGram_one hn hq 1 σ
    simp only [map_one, one_mul, hf] at h2
    rw [← h2, orderOf_one] at hσ
    omega
  · have h9n : 9 ∣ n := h9.trans (Nat.gcd_dvd_left _ _)
    have hn8 : 8 ≤ n := by have := Nat.le_of_dvd (by omega) h9n; omega
    have hK : 3 ∣ Nat.card K - 1 := by
      rw [h.card_eq_sq]
      exact h3.trans (T1b.succ_dvd_sq_sub_one (Nat.one_le_pow _ _ h.prime.pos))
    obtain ⟨ω, hω, hω1⟩ := Hering214.exists_primitive_cube_root hK
    have hω3 : ω ^ 3 = 1 := by linear_combination (ω - 1) * hω
    have hσ3 : σ ^ 3 = 1 := by rw [← hσ]; exact pow_orderOf_eq_one σ
    have hbar : h.bar ω * ω = 1 := by
      obtain ⟨k, hk⟩ := h3
      rw [h.bar_apply, ← pow_succ, hk, pow_mul, hω3, one_pow]
    exact (fixedBlocks_primeFormFieldHom h hn8 isPrimeFormGram_one hω3 hω1 hbar σ
      (Hering214.ringEquiv_fixes_cube_root hσ3 hω hω1)).conj _

end CFSG.LocalAnalysis.AGL81TheoremCD.Section15.K35

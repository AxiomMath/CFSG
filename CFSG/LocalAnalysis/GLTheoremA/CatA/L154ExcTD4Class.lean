module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.L154ExcTD4Res
public import CFSG.LocalAnalysis.GLTheoremA.CatA.L154ExcTD4Exact
public import CFSG.LocalAnalysis.GLTheoremA.CatA.L154ExcTD4E6
public import CFSG.LocalAnalysis.GLTheoremA.CatA.L154ExcTD4D4
public import CFSG.LocalAnalysis.GLTheoremA.CatA.MITD4
public import CFSG.LocalAnalysis.StandardType.GGLayerNotExcThreeAtTwoKac
public import CFSG.LocalAnalysis.GLTheoremA.CatA.L154NonCfgRank4

public section

namespace CFSG.LocalAnalysis.GLTheoremA.K155X

open CFSG.Open
open CFSG.Yardstones.Md0ec50421ce4 (catalogIs onLie)
open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.AlgebraicGroups
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.HardMathSupport.Timmesfeld.CrossChar
  CFSG.HardMathSupport.Solomon.Coordinator.LieComp
  CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple
open CFSG.StandardType (markTag)

section Exclusion

theorem l154td4_false_of_exact {X : Type} [Group X] (hX : CFSG.IsQuasisimple X)
    (h : L154ExactModel (X ⧸ Subgroup.center X))
    (hTD : catalogIs (X ⧸ Subgroup.center X) (onLie fun | .trialityD4 _ => True | _ => False)) :
    False := by
  have hperf : commutator X = ⊤ := Group.isPerfect_def.mp hX.1
  rcases h with ⟨t, n, f, hM, ht⟩ | h6
  · obtain ⟨lab, -, R, _, I, F, θ, -, -, ⟨hmt, -⟩, hMM⟩ :=
      CFSG.StandardType.Canonical.largeEvenMarking_exists_markedModel
        (CFSG.StandardType.Canonical.largeEvenMarking_of_lieModel_centerQuot hperf hM)
    have htag := CFSG.LocalAnalysis.GLTheoremA.MI.tag_triD4_of_isTD4 hMM hTD θ
    apply ht
    rw [← hmt]
    simp [markTag, htag]
  · obtain ⟨e⟩ := h6
    haveI : IsSimpleGroup (X ⧸ Subgroup.center X) := hX.2.1
    obtain ⟨lab, -, R, _, I, F, θ, -, -, hP, hMM⟩ :=
      CFSG.StandardType.Canonical.largeEvenMarking_exists_markedModel
        (l154_marking_b2der_label hperf e)
    have htag := CFSG.LocalAnalysis.GLTheoremA.MI.tag_triD4_of_isTD4 hMM hTD θ
    rw [hP] at htag
    exact absurd htag (by decide)

end Exclusion

section Dispatch

variable
  {L : Type} [Field L] [IsAlgClosed L] [CharP L 2] {p₀ : ℕ}

theorem l154td4_exactClass_E6 (S : LangSetup Tag.E6 L p₀) {a : Fin Tag.E6.rank → Lˣ}
    {i : KernelComponent (rootCharHom a)} (hcls : L154Cls S 3 a i)
    (hA1 : ¬ (1 ≤ compRank (componentRoots (rootCharHom a) i) ∧
      (componentRoots (rootCharHom a) i).ncard = compRank (componentRoots (rootCharHom a) i) *
        (compRank (componentRoots (rootCharHom a) i) + 1)))
    (hE6 : ¬ L154E6Class a i)
    (hexc : compRank (componentRoots (rootCharHom a) i) = 4 →
      twistInner (componentRoots (rootCharHom a) i)
        ((S.ρ : (Fin Tag.E6.rank → ℤ) → _)^[2 * componentOrbitLength S.ρ
          (componentRoots (rootCharHom a) i)])) :
    L154ExactClass S i := by
  have hℓp : ringChar L ≠ 3 := by rw [ringChar.eq L 2]; norm_num
  have hpL : ((3 : ℕ) : L) ≠ 0 := natCast_ne_zero_of_ringChar_ne hcls.prime hℓp
  have hTp : rootDiagUnit Tag.E6 a ^ 3 = 1 := rootDiagUnit_pow_eq_one_of_forall hcls.pow
  rcases l154_shape_E6 S hcls.prime hpL hTp i hA1 with hD | hE
  · by_cases hinner : twistInner (componentRoots (rootCharHom a) i)
        ((S.ρ : (Fin Tag.E6.rank → ℤ) → _)^[componentOrbitLength S.ρ
          (componentRoots (rootCharHom a) i)])
    · exact l154td4_exact_dInner_E6 S hcls.prime hpL hcls.torus hTp i hD.1 hD.2 hinner
    · by_cases h5 : 5 ≤ compRank (componentRoots (rootCharHom a) i)
      · exact l154td4_exact_twoD hcls.prime S hcls.torus hcls.pow hcls.ne_one i h5 hD.2 hinner
      · have h4 : compRank (componentRoots (rootCharHom a) i) = 4 := by
          have := hD.1
          omega
        exact l154td4_exact_d4_E6 S hcls.prime hpL hcls.torus hTp i h4 (by rw [hD.2, h4]) hinner
          (hexc h4)
  · exfalso
    have hr : compRank (componentRoots (rootCharHom a) i) ≤ 6 := compRank_le_rank _
    have h6 : compRank (componentRoots (rootCharHom a) i) = 6 := by
      have := hE.1
      omega
    exact hE6 ⟨h6, by rw [hE.2, h6]; rfl⟩

theorem l154td4_exactClass_E7 (S : LangSetup Tag.E7 L p₀) {a : Fin Tag.E7.rank → Lˣ}
    {i : KernelComponent (rootCharHom a)} (hcls : L154Cls S 3 a i)
    (hA1 : ¬ (1 ≤ compRank (componentRoots (rootCharHom a) i) ∧
      (componentRoots (rootCharHom a) i).ncard = compRank (componentRoots (rootCharHom a) i) *
        (compRank (componentRoots (rootCharHom a) i) + 1)))
    (hE6 : ¬ L154E6Class a i) : L154ExactClass S i := by
  have hℓp : ringChar L ≠ 3 := by rw [ringChar.eq L 2]; norm_num
  have hpL : ((3 : ℕ) : L) ≠ 0 := natCast_ne_zero_of_ringChar_ne hcls.prime hℓp
  have hTp : rootDiagUnit Tag.E7 a ^ 3 = 1 := rootDiagUnit_pow_eq_one_of_forall hcls.pow
  rcases l154_shape_E7 S hcls.prime hpL hTp i hA1 with hD | hE
  · by_cases hinner : twistInner (componentRoots (rootCharHom a) i)
        ((S.ρ : (Fin Tag.E7.rank → ℤ) → _)^[componentOrbitLength S.ρ
          (componentRoots (rootCharHom a) i)])
    · exact l154td4_exact_dInner_E7 S hcls.prime hpL hcls.torus hTp i hD.1 hD.2 hinner
    · by_cases h5 : 5 ≤ compRank (componentRoots (rootCharHom a) i)
      · exact l154td4_exact_twoD hcls.prime S hcls.torus hcls.pow hcls.ne_one i h5 hD.2 hinner
      · have h4 : compRank (componentRoots (rootCharHom a) i) = 4 := by
          have := hD.1
          omega
        exact (CFSG.StandardType.ExcThreeAtTwo.not_d4Shape_of_three_E7 S hpL hTp i
          ⟨h4, by rw [hD.2, h4]⟩).elim
  · exfalso
    have hr : compRank (componentRoots (rootCharHom a) i) ≤ 7 := compRank_le_rank _
    by_cases h6 : compRank (componentRoots (rootCharHom a) i) = 6
    · exact hE6 ⟨h6, by rw [hE.2, h6]; rfl⟩
    · have h7 : compRank (componentRoots (rootCharHom a) i) = 7 := by
        have := hE.1
        omega
      exact hcls.ne_one (rootDiagUnit_eq_one_of_ncard i (by rw [hE.2, h7]; decide))

theorem l154td4_exactClass_E8 (S : LangSetup Tag.E8 L p₀) {a : Fin Tag.E8.rank → Lˣ}
    {i : KernelComponent (rootCharHom a)} (hcls : L154Cls S 3 a i)
    (hA1 : ¬ (1 ≤ compRank (componentRoots (rootCharHom a) i) ∧
      (componentRoots (rootCharHom a) i).ncard = compRank (componentRoots (rootCharHom a) i) *
        (compRank (componentRoots (rootCharHom a) i) + 1)))
    (hE6 : ¬ L154E6Class a i) : L154ExactClass S i := by
  have hℓp : ringChar L ≠ 3 := by rw [ringChar.eq L 2]; norm_num
  have hpL : ((3 : ℕ) : L) ≠ 0 := natCast_ne_zero_of_ringChar_ne hcls.prime hℓp
  have hTp : rootDiagUnit Tag.E8 a ^ 3 = 1 := rootDiagUnit_pow_eq_one_of_forall hcls.pow
  rcases l154_shape_E8 S hcls.prime hpL hTp i hA1 with hD | hE
  · by_cases hinner : twistInner (componentRoots (rootCharHom a) i)
        ((S.ρ : (Fin Tag.E8.rank → ℤ) → _)^[componentOrbitLength S.ρ
          (componentRoots (rootCharHom a) i)])
    · exact l154td4_exact_dInner_E8 S hcls.prime hpL hcls.torus hTp i hD.1 hD.2 hinner
    · by_cases h5 : 5 ≤ compRank (componentRoots (rootCharHom a) i)
      · exact l154td4_exact_twoD hcls.prime S hcls.torus hcls.pow hcls.ne_one i h5 hD.2 hinner
      · have h4 : compRank (componentRoots (rootCharHom a) i) = 4 := by
          have := hD.1
          omega
        exact (CFSG.StandardType.ExcThreeAtTwo.not_d4Shape_of_three_E8 S hpL hTp i
          ⟨h4, by rw [hD.2, h4]⟩).elim
  · have hr : compRank (componentRoots (rootCharHom a) i) ≤ 8 := compRank_le_rank _
    have h6' := hE.1
    by_cases h6 : compRank (componentRoots (rootCharHom a) i) = 6
    · exact (hE6 ⟨h6, by rw [hE.2, h6]; rfl⟩).elim
    by_cases h7 : compRank (componentRoots (rootCharHom a) i) = 7
    · have hn : (componentRoots (rootCharHom a) i).ncard = 126 := by rw [hE.2, h7]; rfl
      by_cases hinner : twistInner (componentRoots (rootCharHom a) i)
          ((S.ρ : (Fin Tag.E8.rank → ℤ) → _)^[componentOrbitLength S.ρ
            (componentRoots (rootCharHom a) i)])
      · exact l154td4_exact_e7Class S hcls.prime hpL hcls.torus hTp i h7 hn hinner
      · exact (hinner (twistInner_of_shape S hcls.torus i 7 126 h7 hn (by omega) (by omega)
          (by omega) (by omega))).elim
    · have h8 : compRank (componentRoots (rootCharHom a) i) = 8 := by omega
      exact (hcls.ne_one (rootDiagUnit_eq_one_of_ncard i (by rw [hE.2, h8]; decide))).elim

end Dispatch

section Master

variable
  {L : Type} [Field L] [IsAlgClosed L] [CharP L 2] {p₀ : ℕ}

theorem l154td4_exactClass {τ : Tag} (S : LangSetup τ L p₀) {a : Fin τ.rank → Lˣ}
    {i : KernelComponent (rootCharHom a)} (hcls : L154Cls S 3 a i)
    (hexc : compRank (componentRoots (rootCharHom a) i) = 4 →
      twistInner (componentRoots (rootCharHom a) i)
        ((S.ρ : (Fin τ.rank → ℤ) → _)^[2 * componentOrbitLength S.ρ
          (componentRoots (rootCharHom a) i)])) :
    L154ExactClass S i := by
  have hℓp : ringChar L ≠ 3 := by rw [ringChar.eq L 2]; norm_num
  have hpL : ((3 : ℕ) : L) ≠ 0 := natCast_ne_zero_of_ringChar_ne hcls.prime hℓp
  have hTp : rootDiagUnit τ a ^ 3 = 1 := rootDiagUnit_pow_eq_one_of_forall hcls.pow
  by_cases hA1 : 1 ≤ compRank (componentRoots (rootCharHom a) i) ∧
      (componentRoots (rootCharHom a) i).ncard = compRank (componentRoots (rootCharHom a) i) *
        (compRank (componentRoots (rootCharHom a) i) + 1)
  · exact l154td4_exact_typeA S hcls.prime hcls.torus hcls.pow hcls.ne_one i hA1 hcls.qs
  by_cases hE6 : L154E6Class a i
  · exact l154td4_exact_e6Class S hcls.prime hcls.torus hcls.pow hcls.ne_one i hcls.qs hE6
  cases τ with
  | G2 => exact (false_of_g2Class_nonAP hcls.prime S hpL hTp hcls.ne_one i hA1).elim
  | F4 => exact l154td4_exact_f4 S hcls hA1
  | D4 =>
    exact (hcls.ne_one (rootDiagUnit_eq_one_of_ncard i (l154_rootCount_le_of_dShape_D4
      (l154_shape_D4 S hcls.prime hpL hTp i hA1)))).elim
  | E6 => exact l154td4_exactClass_E6 S hcls hA1 hE6 hexc
  | E7 => exact l154td4_exactClass_E7 S hcls hA1 hE6
  | E8 => exact l154td4_exactClass_E8 S hcls hA1 hE6

end Master

section Final

theorem l154td4_class_holds : L154TD4Class := by
  intro τ L _ _ _ p₀ S a i hT hap ha1 hqi hTD
  by_cases hexc : compRank (componentRoots (rootCharHom a) i) = 4 ∧
      ¬ twistInner (componentRoots (rootCharHom a) i)
        ((S.ρ : (Fin τ.rank → ℤ) → _)^[2 * componentOrbitLength S.ρ
          (componentRoots (rootCharHom a) i)])
  · exact hexc
  exfalso
  have hcls : L154Cls S 3 a i := ⟨Nat.prime_three, by norm_num, hT, hap, ha1, hqi⟩
  exact l154td4_false_of_exact hqi (l154td4_exactClass S hcls fun h4 => by
    by_contra hn
    exact hexc ⟨h4, hn⟩) hTD

end Final

end CFSG.LocalAnalysis.GLTheoremA.K155X

end

module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.L154NonCfgE7

public section

namespace CFSG.LocalAnalysis.GLTheoremA.K155X

open CFSG.Blueprint (LieModel classicalTags)
open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.AlgebraicGroups
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.HardMathSupport.Timmesfeld.CrossChar
  CFSG.HardMathSupport.Solomon.Coordinator.LieComp
  CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple CFSG.LieType.Steinberg.Adjoint
  CFSG.RankThree.PartOne.KE CFSG.Timmesfeld
open scoped MatrixGroups Matrix

set_option linter.unusedSectionVars false
set_option maxRecDepth 100000

abbrev L154DShape {τ : Tag} (Ψ : Set (Fin τ.rank → ℤ)) : Prop :=
  4 ≤ compRank Ψ ∧ Ψ.ncard = 2 * compRank Ψ * (compRank Ψ - 1)

abbrev L154EShape {τ : Tag} (Ψ : Set (Fin τ.rank → ℤ)) : Prop :=
  6 ≤ compRank Ψ ∧ Ψ.ncard = eRootCount (compRank Ψ)

section Shapes


variable {L : Type} [Field L] [IsAlgClosed L] {p₀ p : ℕ}

theorem l154_shape_D4 (S : LangSetup Tag.D4 L p₀) (hp : p.Prime) (hpL : (p : L) ≠ 0)
    {a : Fin Tag.D4.rank → Lˣ} (hTp : rootDiagUnit Tag.D4 a ^ p = 1)
    (i : KernelComponent (rootCharHom a))
    (hnonA : ¬ (1 ≤ compRank (componentRoots (rootCharHom a) i) ∧
      (componentRoots (rootCharHom a) i).ncard = compRank (componentRoots (rootCharHom a) i) *
        (compRank (componentRoots (rootCharHom a) i) + 1))) :
    L154DShape (componentRoots (rootCharHom a) i) := by
  obtain ⟨v, μ, x, c, -, hc, -, hlen, -, hrank, hncard⟩ :=
    exists_cand_of_class kacD4 facts_D4 d4_tree d4_adj d4_check d4_lt d4_card S hp hpL hTp i
  have hshape := d4_shape c hc hlen
  rw [← hncard, ← hrank] at hshape
  rcases hshape with hA | hD
  · exact (hnonA hA).elim
  · exact hD

theorem l154_shape_E6 (S : LangSetup Tag.E6 L p₀) (hp : p.Prime) (hpL : (p : L) ≠ 0)
    {a : Fin Tag.E6.rank → Lˣ} (hTp : rootDiagUnit Tag.E6 a ^ p = 1)
    (i : KernelComponent (rootCharHom a))
    (hnonA : ¬ (1 ≤ compRank (componentRoots (rootCharHom a) i) ∧
      (componentRoots (rootCharHom a) i).ncard = compRank (componentRoots (rootCharHom a) i) *
        (compRank (componentRoots (rootCharHom a) i) + 1))) :
    L154DShape (componentRoots (rootCharHom a) i) ∨
      L154EShape (componentRoots (rootCharHom a) i) := by
  obtain ⟨v, μ, x, c, -, hc, -, hlen, -, hrank, hncard⟩ :=
    exists_cand_of_class kacE6 facts_E6 e6_tree e6_adj e6_check e6_lt e6_card S hp hpL hTp i
  have hshape := e6_shape c hc hlen
  rw [← hncard, ← hrank] at hshape
  rcases hshape with hA | hD | hE
  · exact (hnonA hA).elim
  · exact Or.inl hD
  · exact Or.inr hE

theorem l154_shape_E7 (S : LangSetup Tag.E7 L p₀) (hp : p.Prime) (hpL : (p : L) ≠ 0)
    {a : Fin Tag.E7.rank → Lˣ} (hTp : rootDiagUnit Tag.E7 a ^ p = 1)
    (i : KernelComponent (rootCharHom a))
    (hnonA : ¬ (1 ≤ compRank (componentRoots (rootCharHom a) i) ∧
      (componentRoots (rootCharHom a) i).ncard = compRank (componentRoots (rootCharHom a) i) *
        (compRank (componentRoots (rootCharHom a) i) + 1))) :
    L154DShape (componentRoots (rootCharHom a) i) ∨
      L154EShape (componentRoots (rootCharHom a) i) := by
  obtain ⟨v, μ, x, c, -, hc, -, hlen, -, hrank, hncard⟩ :=
    exists_cand_of_class kacE7 facts_E7 e7_tree e7_adj e7_check e7_lt e7_card S hp hpL hTp i
  have hshape := e7_shape c hc hlen
  rw [← hncard, ← hrank] at hshape
  rcases hshape with hA | hD | hE
  · exact (hnonA hA).elim
  · exact Or.inl hD
  · exact Or.inr hE

theorem l154_shape_E8 (S : LangSetup Tag.E8 L p₀) (hp : p.Prime) (hpL : (p : L) ≠ 0)
    {a : Fin Tag.E8.rank → Lˣ} (hTp : rootDiagUnit Tag.E8 a ^ p = 1)
    (i : KernelComponent (rootCharHom a))
    (hnonA : ¬ (1 ≤ compRank (componentRoots (rootCharHom a) i) ∧
      (componentRoots (rootCharHom a) i).ncard = compRank (componentRoots (rootCharHom a) i) *
        (compRank (componentRoots (rootCharHom a) i) + 1))) :
    L154DShape (componentRoots (rootCharHom a) i) ∨
      L154EShape (componentRoots (rootCharHom a) i) := by
  obtain ⟨v, μ, x, c, -, hc, -, hlen, -, hrank, hncard⟩ :=
    exists_cand_of_class kacE8 facts_E8 e8_tree e8_adj e8_check e8_lt e8_card S hp hpL hTp i
  have hshape := e8_shape c hc hlen
  rw [← hncard, ← hrank] at hshape
  rcases hshape with hA | hD | hE
  · exact (hnonA hA).elim
  · exact Or.inl hD
  · exact Or.inr hE

end Shapes

section Master


theorem l154_outerD_model (hR4 : L154Rank4Models) {τ : Tag} {L : Type} [Field L] [IsAlgClosed L]
    [CharP L 2] {p₀ p : ℕ} (S : LangSetup τ L p₀) {a : Fin τ.rank → Lˣ}
    {i : KernelComponent (rootCharHom a)} (hcls : L154Cls S p a i)
    (hD : L154DShape (componentRoots (rootCharHom a) i))
    (hout : ¬ twistInner (componentRoots (rootCharHom a) i)
      ((S.ρ : (Fin τ.rank → ℤ) → _)^[componentOrbitLength S.ρ
        (componentRoots (rootCharHom a) i)])) :
    L154ClassModel S i := by
  by_cases h5 : 5 ≤ compRank (componentRoots (rootCharHom a) i)
  · exact l154_classModel_of_twoD hcls.prime S hcls.torus hcls.pow hcls.ne_one i h5 hD.2 hout
  · have h4 : compRank (componentRoots (rootCharHom a) i) = 4 := by
      have := hD.1
      omega
    exact hR4 τ L p₀ S p a i hcls hout h4 (by rw [hD.2, h4])

theorem l154_rootCount_le_of_dShape_D4 {Ψ : Set (Fin Tag.D4.rank → ℤ)} (hD : L154DShape Ψ) :
    Tag.D4.rootCount ≤ Ψ.ncard := by
  have hr : compRank Ψ ≤ 4 := compRank_le_rank Ψ
  obtain ⟨h4, hn⟩ := hD
  have h : compRank Ψ = 4 := by omega
  rw [hn, h]
  decide

theorem l154_cls_aux {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] {p₀ p : ℕ}
    {S : LangSetup τ L p₀} {a : Fin τ.rank → Lˣ} {i : KernelComponent (rootCharHom a)}
    (hcls : L154Cls S p a i) : ((p : ℕ) : L) ≠ 0 ∧ rootDiagUnit τ a ^ p = 1 :=
  ⟨natCast_ne_zero_of_ringChar_ne hcls.prime
    (ringChar_ne_of_pow_eq_one hcls.prime hcls.pow hcls.ne_one),
    rootDiagUnit_pow_eq_one_of_forall hcls.pow⟩

variable {L : Type} [Field L] [IsAlgClosed L] [CharP L 2] {p₀ p : ℕ}

theorem l154_models_G2 (S : LangSetup Tag.G2 L p₀) {a : Fin Tag.G2.rank → Lˣ}
    {i : KernelComponent (rootCharHom a)} (hcls : L154Cls S p a i)
    (hA1 : ¬ (1 ≤ compRank (componentRoots (rootCharHom a) i) ∧
      (componentRoots (rootCharHom a) i).ncard = compRank (componentRoots (rootCharHom a) i) *
        (compRank (componentRoots (rootCharHom a) i) + 1))) :
    L154ClassModel S i :=
  (false_of_g2Class_nonAP hcls.prime S (l154_cls_aux hcls).1 (l154_cls_aux hcls).2 hcls.ne_one i
    hA1).elim

theorem l154_models_F4 (hF4 : L154F4Models) (S : LangSetup Tag.F4 L p₀)
    {a : Fin Tag.F4.rank → Lˣ} {i : KernelComponent (rootCharHom a)}
    (hcls : L154Cls S p a i)
    (hA1 : ¬ (1 ≤ compRank (componentRoots (rootCharHom a) i) ∧
      (componentRoots (rootCharHom a) i).ncard = compRank (componentRoots (rootCharHom a) i) *
        (compRank (componentRoots (rootCharHom a) i) + 1))) :
    L154ClassModel S i := by
  obtain ⟨hpL, hTp⟩ := l154_cls_aux hcls
  have hp2' : p % 2 = 1 := (hcls.prime.eq_two_or_odd).resolve_left hcls.ne_two
  have hcases := f4_nonA_casesP hcls.prime hp2' S hpL hTp hcls.ne_one i hA1
  by_cases hinner : twistInner (componentRoots (rootCharHom a) i)
      ((S.ρ : (Fin Tag.F4.rank → ℤ) → _)^[componentOrbitLength S.ρ
        (componentRoots (rootCharHom a) i)])
  · rcases hcases with ⟨hr, hn⟩ | ⟨v, J, -, -, hr, hn⟩
    · exact hF4 L p₀ S p a i hcls hinner (Or.inl ⟨hr, hn⟩)
    · exact hF4 L p₀ S p a i hcls hinner (Or.inr ⟨hr, hn⟩)
  · exfalso
    rcases hcases with ⟨hr, hn⟩ | ⟨v, J, -, -, hr, hn⟩
    · exact hinner (twistInner_of_shape S hcls.torus i 2 8 hr hn (by omega) (by omega) (by omega)
        (by omega))
    · exact hinner (twistInner_of_shape S hcls.torus i 3 18 hr hn (by omega) (by omega) (by omega)
        (by omega))

theorem l154_models_D4 (S : LangSetup Tag.D4 L p₀) {a : Fin Tag.D4.rank → Lˣ}
    {i : KernelComponent (rootCharHom a)} (hcls : L154Cls S p a i)
    (hA1 : ¬ (1 ≤ compRank (componentRoots (rootCharHom a) i) ∧
      (componentRoots (rootCharHom a) i).ncard = compRank (componentRoots (rootCharHom a) i) *
        (compRank (componentRoots (rootCharHom a) i) + 1))) :
    L154ClassModel S i := by
  obtain ⟨hpL, hTp⟩ := l154_cls_aux hcls
  have hD := l154_shape_D4 S hcls.prime hpL hTp i hA1
  exact (hcls.ne_one (rootDiagUnit_eq_one_of_ncard i
    (l154_rootCount_le_of_dShape_D4 hD))).elim

theorem l154_models_E6 (hR4 : L154Rank4Models) (S : LangSetup Tag.E6 L p₀)
    {a : Fin Tag.E6.rank → Lˣ} {i : KernelComponent (rootCharHom a)}
    (hcls : L154Cls S p a i)
    (hA1 : ¬ (1 ≤ compRank (componentRoots (rootCharHom a) i) ∧
      (componentRoots (rootCharHom a) i).ncard = compRank (componentRoots (rootCharHom a) i) *
        (compRank (componentRoots (rootCharHom a) i) + 1)))
    (hE6 : ¬ L154E6Class a i) : L154ClassModel S i := by
  obtain ⟨hpL, hTp⟩ := l154_cls_aux hcls
  have h2 : ringChar L = 2 := ringChar.eq L 2
  rcases l154_shape_E6 S hcls.prime hpL hTp i hA1 with hD | hE
  · by_cases hinner : twistInner (componentRoots (rootCharHom a) i)
        ((S.ρ : (Fin Tag.E6.rank → ℤ) → _)^[componentOrbitLength S.ρ
          (componentRoots (rootCharHom a) i)])
    · obtain ⟨n, e, hmodel⟩ :=
        l154_model_of_dClass_E6 S hcls.prime hpL hcls.torus hTp i hD.1 hD.2 hinner
      exact l154_nonCfgModel_of_statedClassical h2 (by simp [classicalTags])
        (by simp [L154GoodModel]) hmodel
    · exact l154_outerD_model hR4 S hcls hD hinner
  · exfalso
    have hr : compRank (componentRoots (rootCharHom a) i) ≤ 6 := compRank_le_rank _
    have h6 : compRank (componentRoots (rootCharHom a) i) = 6 := by
      have := hE.1
      omega
    exact hE6 ⟨h6, by rw [hE.2, h6]; rfl⟩

theorem l154_models_E7 (hR4 : L154Rank4Models) (S : LangSetup Tag.E7 L p₀)
    {a : Fin Tag.E7.rank → Lˣ} {i : KernelComponent (rootCharHom a)}
    (hcls : L154Cls S p a i)
    (hA1 : ¬ (1 ≤ compRank (componentRoots (rootCharHom a) i) ∧
      (componentRoots (rootCharHom a) i).ncard = compRank (componentRoots (rootCharHom a) i) *
        (compRank (componentRoots (rootCharHom a) i) + 1)))
    (hE6 : ¬ L154E6Class a i) : L154ClassModel S i := by
  obtain ⟨hpL, hTp⟩ := l154_cls_aux hcls
  have h2 : ringChar L = 2 := ringChar.eq L 2
  rcases l154_shape_E7 S hcls.prime hpL hTp i hA1 with hD | hE
  · by_cases hinner : twistInner (componentRoots (rootCharHom a) i)
        ((S.ρ : (Fin Tag.E7.rank → ℤ) → _)^[componentOrbitLength S.ρ
          (componentRoots (rootCharHom a) i)])
    · obtain ⟨n, e, hmodel⟩ :=
        l154_model_of_dClass_E7 S hcls.prime hpL hcls.torus hTp i hD.1 hD.2 hinner
      exact l154_nonCfgModel_of_statedClassical h2 (by simp [classicalTags])
        (by simp [L154GoodModel]) hmodel
    · exact l154_outerD_model hR4 S hcls hD hinner
  · exfalso
    have hr : compRank (componentRoots (rootCharHom a) i) ≤ 7 := compRank_le_rank _
    by_cases h6 : compRank (componentRoots (rootCharHom a) i) = 6
    · exact hE6 ⟨h6, by rw [hE.2, h6]; rfl⟩
    · have h7 : compRank (componentRoots (rootCharHom a) i) = 7 := by
        have := hE.1
        omega
      exact hcls.ne_one (rootDiagUnit_eq_one_of_ncard i (by rw [hE.2, h7]; decide))

theorem l154_models_E8 (hR4 : L154Rank4Models) (S : LangSetup Tag.E8 L p₀)
    {a : Fin Tag.E8.rank → Lˣ} {i : KernelComponent (rootCharHom a)}
    (hcls : L154Cls S p a i)
    (hA1 : ¬ (1 ≤ compRank (componentRoots (rootCharHom a) i) ∧
      (componentRoots (rootCharHom a) i).ncard = compRank (componentRoots (rootCharHom a) i) *
        (compRank (componentRoots (rootCharHom a) i) + 1)))
    (hE6 : ¬ L154E6Class a i) : L154ClassModel S i := by
  obtain ⟨hpL, hTp⟩ := l154_cls_aux hcls
  have h2 : ringChar L = 2 := ringChar.eq L 2
  rcases l154_shape_E8 S hcls.prime hpL hTp i hA1 with hD | hE
  · by_cases hinner : twistInner (componentRoots (rootCharHom a) i)
        ((S.ρ : (Fin Tag.E8.rank → ℤ) → _)^[componentOrbitLength S.ρ
          (componentRoots (rootCharHom a) i)])
    · obtain ⟨n, e, hmodel⟩ :=
        l154_model_of_dClass_E8 S hcls.prime hpL hcls.torus hTp i hD.1 hD.2 hinner
      exact l154_nonCfgModel_of_statedClassical h2 (by simp [classicalTags])
        (by simp [L154GoodModel]) hmodel
    · exact l154_outerD_model hR4 S hcls hD hinner
  · have hr : compRank (componentRoots (rootCharHom a) i) ≤ 8 := compRank_le_rank _
    have h6' := hE.1
    by_cases h6 : compRank (componentRoots (rootCharHom a) i) = 6
    · exact (hE6 ⟨h6, by rw [hE.2, h6]; rfl⟩).elim
    by_cases h7 : compRank (componentRoots (rootCharHom a) i) = 7
    · have hn : (componentRoots (rootCharHom a) i).ncard = 126 := by rw [hE.2, h7]; rfl
      by_cases hinner : twistInner (componentRoots (rootCharHom a) i)
          ((S.ρ : (Fin Tag.E8.rank → ℤ) → _)^[componentOrbitLength S.ρ
            (componentRoots (rootCharHom a) i)])
      · exact l154E7Models_holds L p₀ S p a i hcls hinner h7 hn
      · exact (hinner (twistInner_of_shape S hcls.torus i 7 126 h7 hn (by omega) (by omega)
          (by omega) (by omega))).elim
    · have h8 : compRank (componentRoots (rootCharHom a) i) = 8 := by omega
      exact (hcls.ne_one (rootDiagUnit_eq_one_of_ncard i (by rw [hE.2, h8]; decide))).elim

theorem l154NonCfgModels_of_residuals (hF4 : L154F4Models) (hR4 : L154Rank4Models) :
    L154NonCfgModels := by
  intro τ L _ _ _ p₀ S p a i hcls hA hE6
  by_cases hA1 : 1 ≤ compRank (componentRoots (rootCharHom a) i) ∧
      (componentRoots (rootCharHom a) i).ncard = compRank (componentRoots (rootCharHom a) i) *
        (compRank (componentRoots (rootCharHom a) i) + 1)
  · have hr1 : compRank (componentRoots (rootCharHom a) i) = 1 := by
      by_contra h
      exact hA ⟨by have := hA1.1; omega, hA1.2⟩
    exact l154_classModel_of_rankOne S hcls.torus i hr1 (by rw [hA1.2, hr1]) hcls.qs
  · cases τ with
    | G2 => exact l154_models_G2 S hcls hA1
    | F4 => exact l154_models_F4 hF4 S hcls hA1
    | D4 => exact l154_models_D4 S hcls hA1
    | E6 => exact l154_models_E6 hR4 S hcls hA1 hE6
    | E7 => exact l154_models_E7 hR4 S hcls hA1 hE6
    | E8 => exact l154_models_E8 hR4 S hcls hA1 hE6

end Master

end CFSG.LocalAnalysis.GLTheoremA.K155X

end

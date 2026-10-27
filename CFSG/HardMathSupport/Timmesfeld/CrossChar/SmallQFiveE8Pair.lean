module

public import CFSG.HardMathSupport.Timmesfeld.CrossChar.SmallQFiveE8Step
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcInnerE8FourFiveQ2Pair
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcInnerFivePairRigid

public section

namespace CFSG.HardMathSupport.Timmesfeld.CrossChar.SmallQ5

open CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Steinberg.Adjoint CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.RankThree.PartOne.KE CFSG.RankThree.Lattice CFSG.LieType.SeitzGeneration
  CFSG.RankThree.Classical CFSG.RankThree.Chevalley CFSG.HardMathSupport.Timmesfeld.Torality
  CFSG.HardMathSupport.Timmesfeld.CrossChar.SmallQ3 CFSG.HardMathSupport.Timmesfeld.CrossChar
open scoped Matrix MatrixGroups

set_option linter.unusedSectionVars false


theorem isSimpleGroup_SL2_charTwo {F : Type} [Field F] [Finite F] [CharP F 2]
    (h4 : 4 ≤ Nat.card F) : IsSimpleGroup (Matrix.SpecialLinearGroup (Fin 2) F) := by
  have hPSL : IsSimpleGroup (Matrix.ProjectiveSpecialLinearGroup (Fin 2) F) :=
    Matrix.ProjectiveSpecialLinearGroup.rank_two_simple h4
  have hcenter : Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) F) = ⊥ := by
    rw [Subgroup.eq_bot_iff_forall]
    intro X hX
    exact sl2_eq_one_of_central_charTwo fun Z => (Subgroup.mem_center_iff.1 hX Z).symm
  have e : Matrix.ProjectiveSpecialLinearGroup (Fin 2) F ≃*
      Matrix.SpecialLinearGroup (Fin 2) F :=
    (QuotientGroup.quotientMulEquivOfEq hcenter).trans QuotientGroup.quotientBot
  haveI := hPSL
  exact e.symm.isSimpleGroup

section Pair

variable {L : Type} [Field L] [IsAlgClosed L] [CharP L 2]

theorem iterateFrobenius_comp_two (c : L) :
    ((iterateFrobenius L 2 1).comp (iterateFrobenius L 2 1)) c = c ^ 4 := by
  simp only [RingHom.comp_apply, iterateFrobenius_two_one, ← pow_mul]

theorem map_map_frobenius (A : SL2 L) :
    Matrix.SpecialLinearGroup.map (iterateFrobenius L 2 1)
        (Matrix.SpecialLinearGroup.map (iterateFrobenius L 2 1) A) =
      Matrix.SpecialLinearGroup.map ((iterateFrobenius L 2 1).comp (iterateFrobenius L 2 1)) A :=
  Subtype.ext (by
    simp only [Matrix.SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply, Matrix.map_map]
    rfl)

theorem swap_map_sq_conj' {K₂ : Type} [Field K₂] [Algebra K₂ L]
    (hK : ∀ c : L, c ∈ Set.range (algebraMap K₂ L) ↔ c ^ 4 = c) {ζ : Lˣ} (h5 : ζ ^ 5 = 1)
    (h1 : ζ ≠ 1) {A : SL2 L}
    (hA : A ∈ (Matrix.SpecialLinearGroup.map (algebraMap K₂ L)).range.map
      (conjSL (Pmat h5 h1))) :
    conjSL swapGL (Matrix.SpecialLinearGroup.map
      ((iterateFrobenius L 2 1).comp (iterateFrobenius L 2 1)) A) = A := by
  obtain ⟨_, ⟨B, rfl⟩, rfl⟩ := hA
  have hC : Matrix.SpecialLinearGroup.map ((iterateFrobenius L 2 1).comp (iterateFrobenius L 2 1))
      (Matrix.SpecialLinearGroup.map (algebraMap K₂ L) B) =
      Matrix.SpecialLinearGroup.map (algebraMap K₂ L) B := by
    apply Subtype.ext
    ext i j
    have hx : ∀ x : K₂, ((iterateFrobenius L 2 1).comp (iterateFrobenius L 2 1))
        (algebraMap K₂ L x) = algebraMap K₂ L x := fun x => by
      rw [iterateFrobenius_comp_two]
      exact (hK _).1 ⟨x, rfl⟩
    simp only [Matrix.SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply, Matrix.map_apply,
      hx]
  rw [CFSG.RankThree.QuadraticSL2.map_conjSL, hC, ← conjSL_mul,
    swap_mul_glMap_Pmat h5 h1 (iterateFrobenius L 2 1) iterateFrobenius_two_one]

theorem mem_conj_range_of_swap_fixed {K₂ : Type} [Field K₂] [Algebra K₂ L]
    (hK : ∀ c : L, c ∈ Set.range (algebraMap K₂ L) ↔ c ^ 4 = c) {ζ : Lˣ} (h5 : ζ ^ 5 = 1)
    (h1 : ζ ≠ 1) {A : SL2 L}
    (hA : conjSL swapGL (Matrix.SpecialLinearGroup.map
      ((iterateFrobenius L 2 1).comp (iterateFrobenius L 2 1)) A) = A) :
    A ∈ (Matrix.SpecialLinearGroup.map (algebraMap K₂ L)).range.map (conjSL (Pmat h5 h1)) := by
  set F2 := (iterateFrobenius L 2 1).comp (iterateFrobenius L 2 1) with hF2
  set P := Pmat h5 h1 with hP
  have hswap : swapGL * Matrix.GeneralLinearGroup.map F2 P = P :=
    swap_mul_glMap_Pmat h5 h1 (iterateFrobenius L 2 1) iterateFrobenius_two_one
  have hglP : Matrix.GeneralLinearGroup.map F2 P = swapGL * P := by
    have : Matrix.GeneralLinearGroup.map F2 P = swapGL⁻¹ * P := by
      rw [eq_inv_mul_iff_mul_eq]
      exact hswap
    rw [this, swapGL_inv]
  have hmapA : Matrix.SpecialLinearGroup.map F2 A = conjSL swapGL A := by
    have h2 := congrArg (conjSL swapGL) hA
    rw [← conjSL_mul, swapGL_mul_swapGL, conjSL_one] at h2
    exact h2
  set X : SL2 L := conjSL P⁻¹ A with hX
  have hXfix : Matrix.SpecialLinearGroup.map F2 X = X := by
    rw [hX, CFSG.RankThree.QuadraticSL2.map_conjSL, hmapA, map_inv, hglP, ← conjSL_mul]
    have : (swapGL * P)⁻¹ * swapGL = P⁻¹ := by
      rw [mul_inv_rev, swapGL_inv, mul_assoc, swapGL_mul_swapGL, mul_one]
    rw [this]
  have hF2c : ∀ c : L, F2 c = c ^ 4 := fun c => iterateFrobenius_comp_two c
  have hentry : ∀ i j, ((X : Matrix (Fin 2) (Fin 2) L) i j) ^ 4 =
      (X : Matrix (Fin 2) (Fin 2) L) i j := by
    intro i j
    have h := congrArg (fun Y : SL2 L => (Y : Matrix (Fin 2) (Fin 2) L) i j) hXfix
    simpa [Matrix.SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply, Matrix.map_apply,
      hF2c] using h
  choose b hb using fun i j => (hK _).2 (hentry i j)
  let B : Matrix (Fin 2) (Fin 2) K₂ := Matrix.of b
  have hBmap : (algebraMap K₂ L).mapMatrix B = (X : Matrix (Fin 2) (Fin 2) L) := by
    ext i j
    simp [B, hb]
  have hdetB : B.det = 1 := by
    apply (algebraMap K₂ L).injective
    rw [RingHom.map_det, hBmap, map_one]
    exact X.2
  let B' : Matrix.SpecialLinearGroup (Fin 2) K₂ := ⟨B, hdetB⟩
  have hmapB : Matrix.SpecialLinearGroup.map (algebraMap K₂ L) B' = X :=
    Subtype.ext hBmap
  refine ⟨X, ⟨B', hmapB⟩, ?_⟩
  rw [hX, ← conjSL_mul, mul_inv_cancel, conjSL_one]

theorem stepHom_pairElt {α : Fin Tag.E8.rank → ℤ} (hα : IsRoot Tag.E8 α) {A : SL2 L}
    (hA : conjSL swapGL (Matrix.SpecialLinearGroup.map
      ((iterateFrobenius L 2 1).comp (iterateFrobenius L 2 1)) A) = A) :
    stepHom L (pairElt (iterateFrobenius L 2 1) α (e8PhiFourWeyl • α) 1 A) =
      pairElt (iterateFrobenius L 2 1) α (e8PhiFourWeyl • α) 1 A := by
  rw [pairElt, conjSL_diagUnitOne_one, map_mul, stepHom_rootSL2 hα, stepHom_rootSL2_second hα,
    map_map_frobenius, hA]
  exact (commute_rootSL2_pair hα _ _).eq.symm

theorem fixed_of_mem_Lsp {α : Fin Tag.E8.rank → ℤ} (hα : IsRoot Tag.E8 α) {g : ModGL Tag.E8 L}
    (hg : g ∈ Lsp L α (e8PhiFourWeyl • α)) (hgW : stepHom L g = g) :
    ∃ A : SL2 L, conjSL swapGL (Matrix.SpecialLinearGroup.map
        ((iterateFrobenius L 2 1).comp (iterateFrobenius L 2 1)) A) = A ∧
      g = pairElt (iterateFrobenius L 2 1) α (e8PhiFourWeyl • α) 1 A := by
  have hβ : IsRoot Tag.E8 (e8PhiFourWeyl • α) := (isRoot_smul_iff _).2 hα
  obtain ⟨A, B, rfl⟩ := exists_pair_of_mem_Lsp hα hg
  rw [map_mul, stepHom_rootSL2 hα, stepHom_rootSL2_second hα] at hgW
  set X₁ := conjSL swapGL (Matrix.SpecialLinearGroup.map (iterateFrobenius L 2 1) B) with hX₁
  set Y := Matrix.SpecialLinearGroup.map (iterateFrobenius L 2 1) A with hY
  rw [(commute_rootSL2_pair hα X₁ Y).eq.symm] at hgW
  have h1 : rootSL2 Tag.E8 L α (A⁻¹ * X₁) =
      rootSL2 Tag.E8 L (e8PhiFourWeyl • α) (B * Y⁻¹) := by
    rw [map_mul, map_mul, map_inv, map_inv]
    calc (rootSL2 Tag.E8 L α A)⁻¹ * rootSL2 Tag.E8 L α X₁ =
          (rootSL2 Tag.E8 L α A)⁻¹ * (rootSL2 Tag.E8 L α X₁ *
            rootSL2 Tag.E8 L (e8PhiFourWeyl • α) Y) *
            (rootSL2 Tag.E8 L (e8PhiFourWeyl • α) Y)⁻¹ := by group
      _ = (rootSL2 Tag.E8 L α A)⁻¹ * (rootSL2 Tag.E8 L α A *
            rootSL2 Tag.E8 L (e8PhiFourWeyl • α) B) *
            (rootSL2 Tag.E8 L (e8PhiFourWeyl • α) Y)⁻¹ := by rw [hgW]
      _ = rootSL2 Tag.E8 L (e8PhiFourWeyl • α) B *
            (rootSL2 Tag.E8 L (e8PhiFourWeyl • α) Y)⁻¹ := by group
  have hA1 : A⁻¹ * X₁ = 1 := eq_one_of_rootSL2_eq hα h1
  have hAX : A = X₁ := inv_mul_eq_one.1 hA1
  have h2 : rootSL2 Tag.E8 L (e8PhiFourWeyl • α) (B * Y⁻¹) = 1 := by
    rw [← h1, hA1, map_one]
  have hB : B * Y⁻¹ = 1 :=
    rootSL2_injective_of_field (τ := Tag.E8) (K := L) _ (h2.trans (map_one _).symm)
  have hBA : B = Y := mul_inv_eq_one.1 hB
  refine ⟨A, ?_, ?_⟩
  · rw [← map_map_frobenius, ← hY, ← hBA]
    exact hAX.symm
  · rw [pairElt, conjSL_diagUnitOne_one, ← hY, ← hBA]

theorem rootSpan_le_Lsp_left {α : Fin Tag.E8.rank → ℤ} :
    rootSpan Tag.E8 L {α, -α} ≤ Lsp L α (e8PhiFourWeyl • α) :=
  biSup_mono fun γ hγ => by
    rcases Set.mem_insert_iff.1 hγ with h | h
    · rw [h]
      exact Set.mem_insert _ _
    · rw [Set.mem_singleton_iff.1 h]
      exact Set.mem_insert_of_mem _ (Set.mem_insert _ _)

theorem rootSpan_le_Lsp_right {α : Fin Tag.E8.rank → ℤ} :
    rootSpan Tag.E8 L {e8PhiFourWeyl • α, -(e8PhiFourWeyl • α)} ≤
      Lsp L α (e8PhiFourWeyl • α) :=
  biSup_mono fun γ hγ => by
    rcases Set.mem_insert_iff.1 hγ with h | h
    · rw [h]
      exact Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ (Set.mem_insert _ _))
    · rw [Set.mem_singleton_iff.1 h]
      exact Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _
        (Set.mem_insert_of_mem _ (Set.mem_singleton _)))

theorem canonicalRep_mem_sup_Lsp {α : Fin Tag.E8.rank → ℤ} (hα : IsRoot Tag.E8 α)
    {u : WeylGroup Tag.E8}
    (hu : u = 1 ∨ u = rootReflection α ∨ u = rootReflection (e8PhiFourWeyl • α) ∨
      u = rootReflection α * rootReflection (e8PhiFourWeyl • α)) :
    canonicalRep (coxeterSystem Tag.E8) L u ∈
      torusGroup Tag.E8 L ⊔ Lsp L α (e8PhiFourWeyl • α) := by
  have hβ : IsRoot Tag.E8 (e8PhiFourWeyl • α) := (isRoot_smul_iff _).2 hα
  have h1 : canonicalRep (coxeterSystem Tag.E8) L (rootReflection α) ∈
      torusGroup Tag.E8 L ⊔ Lsp L α (e8PhiFourWeyl • α) :=
    sup_le_sup_left rootSpan_le_Lsp_left _ (canonicalRep_rootReflection_mem hα)
  have h2 : canonicalRep (coxeterSystem Tag.E8) L (rootReflection (e8PhiFourWeyl • α)) ∈
      torusGroup Tag.E8 L ⊔ Lsp L α (e8PhiFourWeyl • α) :=
    sup_le_sup_left rootSpan_le_Lsp_right _ (canonicalRep_rootReflection_mem hβ)
  rcases hu with h | h | h | h
  · rw [h, canonicalRep_one]
    exact one_mem _
  · rw [h]
    exact h1
  · rw [h]
    exact h2
  · rw [h, CFSG.RankThree.PartOne.Q1327T.canonicalRep_mul_charTwo]
    exact mul_mem h1 h2

end Pair

end CFSG.HardMathSupport.Timmesfeld.CrossChar.SmallQ5

end

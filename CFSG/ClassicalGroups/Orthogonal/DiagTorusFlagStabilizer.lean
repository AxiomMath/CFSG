module

public import CFSG.ClassicalGroups.Orthogonal.DiagonalTorusRankOddMinus
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalSplitSylow
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalTailModelBorel

public section

namespace CFSG.ClassicalGroups.Orthogonal

open CFSG.Open CFSG.LieType.Universal.Spin QuadraticMap
open Matrix
open scoped commutatorElement

variable {m : ℕ} {F : Type} [Field F] {b c : F}

theorem minusDiagGen_mem_statedOmega_fin (t : Fˣ) (j : Fin (m - 1))
    {q : ℕ} (hodd : Odd q) (ht : orderOf t = q) :
    diagGLMinusHom m F (Pi.mulSingle j t) ∈
      StatedOmega (StatedQuadMinus m F b c) := by
  rw [statedOmega_eq_comap (coe_quadMinus m F b c), Subgroup.mem_comap,
    MulEquiv.coe_toMonoidHom]
  set d : Fin (m - 1) ⊕ Fin (m - 1) ⊕ Fin 2 → Fˣ := minusDiagHom m F (Pi.mulSingle j t)
    with hddef
  have hdiag : diagGLMinusHom m F (Pi.mulSingle j t) = TauCeti.diagGL d := rfl
  rw [hdiag]
  have horth : ∀ k, k ≠ Sum.inl j → k ≠ Sum.inr (Sum.inl j) →
      polar (quadMinus m F b c) (Pi.single (Sum.inl j) 1) (Pi.single k 1) = 0 ∧
        polar (quadMinus m F b c) (Pi.single (Sum.inr (Sum.inl j)) 1) (Pi.single k 1) = 0 := by
    intro k h1 h2
    rcases k with j' | j' | u
    · constructor
      · rw [polar_quadMinus_single_inl]; simp
      · rw [polar_quadMinus_single_inl]
        simp [show j ≠ j' from fun h => h1 (by rw [h])]
    · constructor
      · rw [polar_quadMinus_single_inr_inl]
        simp [show j ≠ j' from fun h => h2 (by rw [h])]
      · rw [polar_quadMinus_single_inr_inl]; simp
    · fin_cases u
      · constructor <;>
          simp [polar_quadMinus_single_inr_inr_zero, polar_quadMinus_single_inr_inr_one]
      · constructor <;>
          simp [polar_quadMinus_single_inr_inr_zero, polar_quadMinus_single_inr_inr_one]
  have hstep := reflect_mul_reflect_eq_diagGL (Q := quadMinus m F b c) (e := Sum.inl j)
    (f := Sum.inr (Sum.inl j)) (by simp) t d (by simp [hddef]) (by simp [hddef]) (by
      intro k h1 h2
      rcases k with j' | j' | u
      · rw [hddef, minusDiagHom_inl,
          Pi.mulSingle_eq_of_ne (show j' ≠ j from fun h => h1 (by rw [h]))]
      · rw [hddef, minusDiagHom_inr_inl,
          Pi.mulSingle_eq_of_ne (show j' ≠ j from fun h => h2 (by rw [h]))]
        simp
      · rw [hddef]
        simp) (quadMinus_single_inl j) (quadMinus_single_inr j)
    (by rw [polar_quadMinus_single_inr_inl]; simp) horth
  rw [← hstep]
  refine mem_of_odd_pow_of_sq_mem (N :=
      ⁅TauCeti.QuadraticMap.orthogonalGroup (quadMinus m F b c),
        TauCeti.QuadraticMap.orthogonalGroup (quadMinus m F b c)⁆) ?_ hodd ?_
  · intro x hx
    subst hx
    have hsq : (reflect (quadMinus m F b c) (Pi.single (Sum.inl j) 1 +
          Pi.single (Sum.inr (Sum.inl j)) 1) *
          reflect (quadMinus m F b c) (Pi.single (Sum.inl j) 1 +
            (t : F) • Pi.single (Sum.inr (Sum.inl j)) 1)) ^ 2 =
        ⁅reflect (quadMinus m F b c) (Pi.single (Sum.inl j) 1 +
            Pi.single (Sum.inr (Sum.inl j)) 1),
          reflect (quadMinus m F b c) (Pi.single (Sum.inl j) 1 +
            (t : F) • Pi.single (Sum.inr (Sum.inl j)) 1)⁆ := by
      rw [pow_two, commutatorElement_def, reflect_inv, reflect_inv]
      group
    rw [hsq]
    exact Subgroup.commutator_mem_commutator
      (reflect_mem_orthogonalGroup (quadMinus m F b c) _)
      (reflect_mem_orthogonalGroup (quadMinus m F b c) _)
  · rw [hstep, ← hdiag, ← map_pow (toLinEquiv (Fin (m - 1) ⊕ Fin (m - 1) ⊕ Fin 2) F),
      ← map_pow (diagGLMinusHom m F), ← Pi.mulSingle_pow, ← ht, pow_orderOf_eq_one,
      Pi.mulSingle_one]
    simp

theorem diagGen_mem_statedOmega_fin (hm : 4 ≤ m) (h2 : (2 : F) = 0) (t : Fˣ) (j : Fin m)
    {q : ℕ} (hodd : Odd q) (ht : orderOf t = q) :
    diagGLPlusHom m F (Pi.mulSingle j t) ∈ StatedOmega (StatedQuadPlus m F) := by
  rw [mem_statedOmega_iff_mem_elementaryGroup (coe_quadPlus m F)
    (commutator_orthogonalGroup_quadPlus (K := F) (n := m) (by omega))]
  refine mem_elementaryGroup_quadPlus_of_odd_pow h2 (by omega) ?_ hodd ?_
  · rw [TauCeti.QuadraticMap.mem_orthogonalGroup_iff]
    intro v
    rw [toLinEquiv_apply]
    exact quadPlus_mulVec_diagGLPlus _ v
  · rw [← map_pow (toLinEquiv (Fin m ⊕ Fin m) F), ← map_pow (diagGLPlusHom m F),
      ← Pi.mulSingle_pow, ← ht, pow_orderOf_eq_one, Pi.mulSingle_one]
    simp

section Minus

open CFSG.LocalAnalysis.ComponentInitial.OrthogonalTail
open CFSG.ComponentClassification.CatalogueBOrthogonalPointPlusBorel

theorem diagTorusMinus_subgroupOf_le_statedDerivedFlagStabilizer (hm : 4 ≤ m) :
    (diagTorusMinus m F).subgroupOf (StatedOmega (StatedQuadMinus m F b c)) ≤
      statedDerivedFlagStabilizer (StatedQuadMinus m F b c)
        (tailModelFlag (m - 1) F (Fin 2)) := by
  classical
  intro g hg
  rw [statedDerivedFlagStabilizer, Subgroup.mem_iInf]
  intro i
  rw [mem_statedDerivedSubspaceStabilizer]
  rw [Subgroup.mem_subgroupOf] at hg
  obtain ⟨d, hd⟩ := hg
  rw [← hd, tailModelFlag, Submodule.map_span]
  change Submodule.span F ((fun x =>
      toLinEquiv (Fin (m - 1) ⊕ Fin (m - 1) ⊕ Fin 2) F (diagGLMinusHom m F d) x) ''
      ((fun j : Fin (m - 1) =>
        (Pi.single (Sum.inl j) (1 : F) : Fin (m - 1) ⊕ Fin (m - 1) ⊕ Fin 2 → F)) ''
        {j | (j : ℕ) < i + 1})) =
    Submodule.span F ((fun j : Fin (m - 1) =>
      (Pi.single (Sum.inl j) (1 : F) : Fin (m - 1) ⊕ Fin (m - 1) ⊕ Fin 2 → F)) ''
      {j | (j : ℕ) < i + 1})
  have hset : (fun x => toLinEquiv (Fin (m - 1) ⊕ Fin (m - 1) ⊕ Fin 2) F
        (diagGLMinusHom m F d) x) ''
      ((fun j : Fin (m - 1) =>
        (Pi.single (Sum.inl j) (1 : F) : Fin (m - 1) ⊕ Fin (m - 1) ⊕ Fin 2 → F)) ''
        {j | (j : ℕ) < i + 1}) =
      ((fun j : Fin (m - 1) => (d j : F) •
        (Pi.single (Sum.inl j) (1 : F) : Fin (m - 1) ⊕ Fin (m - 1) ⊕ Fin 2 → F)) ''
        {j | (j : ℕ) < i + 1}) := by
    ext v
    constructor
    · rintro ⟨w, ⟨j, hj, rfl⟩, rfl⟩
      exact ⟨j, hj, (diagGL_toLinEquiv_single (minusDiagHom m F d) (Sum.inl j)).symm⟩
    · rintro ⟨j, hj, rfl⟩
      exact ⟨_, ⟨j, hj, rfl⟩, diagGL_toLinEquiv_single (minusDiagHom m F d) (Sum.inl j)⟩
  rw [hset]
  apply le_antisymm
  · refine Submodule.span_le.mpr ?_
    rintro v ⟨j, hj, rfl⟩
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, hj, rfl⟩)
  · refine Submodule.span_le.mpr ?_
    rintro v ⟨j, hj, rfl⟩
    have hmem : (d j : F) • (Pi.single (Sum.inl j) (1 : F) :
        Fin (m - 1) ⊕ Fin (m - 1) ⊕ Fin 2 → F) ∈
        Submodule.span F ((fun j : Fin (m - 1) => (d j : F) •
          (Pi.single (Sum.inl j) (1 : F) : Fin (m - 1) ⊕ Fin (m - 1) ⊕ Fin 2 → F)) ''
          {j | (j : ℕ) < i + 1}) :=
      Submodule.subset_span ⟨j, hj, rfl⟩
    have hsm := Submodule.smul_mem _ ((d j)⁻¹ : F) hmem
    simpa [smul_smul, Units.smul_def] using hsm

end Minus

section Plus

open CFSG.LocalAnalysis.ComponentInitial.OrthogonalSplit
open CFSG.ComponentClassification.CatalogueBOrthogonalPointPlusBorel

theorem diagTorusOrth_le_statedDerivedFlagStabilizer (hm : 4 ≤ m) :
    diagTorusOrth m F ≤
      statedDerivedFlagStabilizer (StatedQuadPlus m F) (stdFlag m F) := by
  classical
  intro g hg
  rw [statedDerivedFlagStabilizer, Subgroup.mem_iInf]
  intro i
  rw [mem_statedDerivedSubspaceStabilizer]
  rw [diagTorusOrth, Subgroup.mem_subgroupOf] at hg
  obtain ⟨d, hd⟩ := hg
  rw [← hd]
  change Submodule.map (toLinEquiv (Fin m ⊕ Fin m) F (diagGLPlusHom m F d)).toLinearMap
      (flag m F ((i : ℕ) + 1)) = flag m F ((i : ℕ) + 1)
  rw [flag, Submodule.map_span]
  change Submodule.span F ((fun x =>
      toLinEquiv (Fin m ⊕ Fin m) F (diagGLPlusHom m F d) x) ''
      ((fun j : Fin m => (Pi.single (Sum.inl j) (1 : F) : Fin m ⊕ Fin m → F)) ''
        {j | (j : ℕ) < (i : ℕ) + 1})) =
    Submodule.span F ((fun j : Fin m =>
      (Pi.single (Sum.inl j) (1 : F) : Fin m ⊕ Fin m → F)) '' {j | (j : ℕ) < (i : ℕ) + 1})
  have hset : (fun x => toLinEquiv (Fin m ⊕ Fin m) F (diagGLPlusHom m F d) x) ''
      ((fun j : Fin m => (Pi.single (Sum.inl j) (1 : F) : Fin m ⊕ Fin m → F)) ''
        {j | (j : ℕ) < (i : ℕ) + 1}) =
      ((fun j : Fin m => (d j : F) •
        (Pi.single (Sum.inl j) (1 : F) : Fin m ⊕ Fin m → F)) ''
        {j | (j : ℕ) < (i : ℕ) + 1}) := by
    ext v
    constructor
    · rintro ⟨w, ⟨j, hj, rfl⟩, rfl⟩
      exact ⟨j, hj, (diagGL_toLinEquiv_single (pairedDiagHom m F d) (Sum.inl j)).symm⟩
    · rintro ⟨j, hj, rfl⟩
      exact ⟨_, ⟨j, hj, rfl⟩, diagGL_toLinEquiv_single (pairedDiagHom m F d) (Sum.inl j)⟩
  rw [hset]
  apply le_antisymm
  · refine Submodule.span_le.mpr ?_
    rintro v ⟨j, hj, rfl⟩
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, hj, rfl⟩)
  · refine Submodule.span_le.mpr ?_
    rintro v ⟨j, hj, rfl⟩
    have hmem : (d j : F) • (Pi.single (Sum.inl j) (1 : F) : Fin m ⊕ Fin m → F) ∈
        Submodule.span F ((fun j : Fin m => (d j : F) •
          (Pi.single (Sum.inl j) (1 : F) : Fin m ⊕ Fin m → F)) ''
          {j | (j : ℕ) < (i : ℕ) + 1}) :=
      Submodule.subset_span ⟨j, hj, rfl⟩
    have hsm := Submodule.smul_mem _ ((d j)⁻¹ : F) hmem
    simpa [smul_smul, Units.smul_def] using hsm

end Plus

end CFSG.ClassicalGroups.Orthogonal

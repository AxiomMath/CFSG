module

public import CFSG.LieType.Chevalley.C2E6FourthResidueWeyl
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalTailMaxBorel

public noncomputable section

namespace CFSG.LieType.Chevalley.C2E6Std.FourthResidue

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley.C2E6Overlap
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.OrthogonalSplit
  CFSG.LocalAnalysis.ComponentInitial.OrthogonalTail CFSG.LieType.Universal.Spin
  CFSG.ClassicalGroups.Orthogonal
open scoped Pointwise

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

theorem baseFlag_eq_span (k : Fin 3) :
    baseFlag k = Submodule.span (ZMod 2)
      ((fun j : Fin 3 => hypVec (ZMod 2) (Fin 2 → ZMod 2) (.inl j)) '' {j | j ≤ k}) := by
  rw [baseFlag_apply, tailFlag]
  congr 2
  ext j
  simp only [Set.mem_ofPred_eq, Fin.le_iff_val_le_val]
  omega

theorem mem_stdLeviBorel_iff_baseFlag
    (l : stdLevi fourthJ) :
    (l : ModGL Tag.E6 K) ∈ stdLeviBorel fourthJ ↔
      ∀ k : Fin 3, (baseFlag k).map (rhoMinus l : V0 →ₗ[ZMod 2] V0) = baseFlag k := by
  rw [mem_stdLeviBorel_iff, mem_tailBorel, and_iff_right (rhoMinus_mem_elementaryGroup l)]
  constructor
  · intro h k
    exact h (k + 1) (by omega) (by omega)
  · intro h i hi1 hi3
    have := h ⟨i - 1, by omega⟩
    rwa [baseFlag_apply, show (⟨i - 1, by omega⟩ : Fin 3).val + 1 = i by simp; omega] at this

@[expose] def panelStab (d : Fin 3) : Subgroup (V0 ≃ₗ[ZMod 2] V0) :=
  orthElementaryGroup Qminus ⊓
    ⨅ k ∈ {k : Fin 3 | k ≠ d}, MulAction.stabilizer (V0 ≃ₗ[ZMod 2] V0) (baseFlag k)

theorem mem_panelStab {d : Fin 3} {g : V0 ≃ₗ[ZMod 2] V0} :
    g ∈ panelStab d ↔ g ∈ orthElementaryGroup Qminus ∧
      ∀ k, k ≠ d → (baseFlag k).map (g : V0 →ₗ[ZMod 2] V0) = baseFlag k := by
  simp only [panelStab, Subgroup.mem_inf, Subgroup.mem_iInf, Set.mem_ofPred_eq,
    Submodule.mem_stabilizer_submodule_iff_map_eq]
  rfl

theorem tailBorel_le_panelStab (d : Fin 3) : tailBorel 3 qBin ≤ panelStab d :=
  fun _ hg => mem_panelStab.2 ⟨tailBorel_le hg,
    fun k _ => (mem_tailBorel.1 hg).2 (k + 1) (by omega) (by omega)⟩

theorem natLevi_mem_panelStab
    (d : Fin 3) : rhoMinus (natLevi d) ∈ panelStab d :=
  mem_panelStab.2 ⟨rhoMinus_mem_elementaryGroup _, fun _ hk => map_baseFlag_natLevi hk⟩

theorem tailWeylElt_mem_panelStab {d j : Fin 3}
    (hj : tailWeylElt 3 qBin a₀ j ∈ panelStab d) : j = d := by
  by_contra hjd
  have h := (mem_panelStab.1 hj).2 j hjd
  have h2 := (tailWeylElt_smul_tailFlag (r := 3) qBin_anisotropic a₀_ne_zero j j).1
    (by rw [Submodule.pointwise_smul_def]; exact h)
  exact h2 rfl

theorem panelStab_eq_closure
    (d : Fin 3) :
    panelStab d = Subgroup.closure
      ((tailBorel 3 qBin : Set (V0 ≃ₗ[ZMod 2] V0)) ∪ {rhoMinus (natLevi d)}) := by
  set M' := Subgroup.closure
    ((tailBorel 3 qBin : Set (V0 ≃ₗ[ZMod 2] V0)) ∪ {rhoMinus (natLevi d)}) with hM'
  have hPE : panelStab d ≤ orthElementaryGroup Qminus := inf_le_left
  have hM'P : M' ≤ panelStab d := (Subgroup.closure_le _).2
    (Set.union_subset (tailBorel_le_panelStab d)
      (Set.singleton_subset_iff.2 (natLevi_mem_panelStab d)))
  have hBM' : tailBorel 3 qBin ≤ M' := fun g hg => Subgroup.subset_closure (Or.inl hg)
  have hmax := (orthogonal_geometry_tail_maximal_Borel_overgroups (r := 3)
    qBin_anisotropic a₀_ne_zero).1
  have hnd : tailWeylElt 3 qBin a₀ d ∈ M' := by
    by_contra hnd
    have hempty : {j | tailWeylElt 3 qBin a₀ j ∈ M'} = ∅ := by
      ext j
      simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
      intro hj
      rw [tailWeylElt_mem_panelStab (hM'P hj)] at hj
      exact hnd hj
    have e := hmax M' (hM'P.trans hPE) hBM'
    rw [hempty, Set.image_empty, Set.union_empty, Subgroup.closure_eq] at e
    have hn : rhoMinus (natLevi d) ∈ tailBorel 3 qBin := by
      rw [← e]
      exact Subgroup.subset_closure (Or.inr rfl)
    exact map_baseFlag_natLevi_ne d ((mem_tailBorel.1 hn).2 (d + 1) (by omega) (by omega))
  refine le_antisymm ?_ hM'P
  rw [hmax (panelStab d) hPE (tailBorel_le_panelStab d)]
  refine (Subgroup.closure_le _).2 (Set.union_subset hBM' ?_)
  rintro _ ⟨j, hj, rfl⟩
  rw [tailWeylElt_mem_panelStab hj]
  exact hnd

theorem mem_leviParabolic_iff
    (d : Fin 3) (l : stdLevi fourthJ) :
    (l : ModGL Tag.E6 K) ∈ leviParabolic fourthJ {d.castSucc} ↔ rhoMinus l ∈ panelStab d := by
  constructor
  · intro hl
    let T : Subgroup (ModGL Tag.E6 K) :=
      ((panelStab d).comap rhoMinus).map (stdLevi fourthJ).subtype
    have hle : leviParabolic fourthJ {d.castSucc} ≤ T := by
      refine (Subgroup.closure_le _).2 ?_
      rintro x (hx | ⟨j, hj, rfl⟩)
      · exact ⟨⟨x, stdLeviBorel_le_stdLevi two_mem_fourthJ hx⟩,
          tailBorel_le_panelStab d (rhoMinus_mem_tailBorel_of_mem hx), rfl⟩
      · rw [Set.mem_singleton_iff] at hj
        subst hj
        exact ⟨natLevi d, natLevi_mem_panelStab d, rfl⟩
    obtain ⟨l', hl', e⟩ := hle hl
    rw [← Subtype.ext e]
    exact hl'
  · intro h
    rw [panelStab_eq_closure] at h
    let S : Subgroup (stdLevi fourthJ) :=
      (leviParabolic fourthJ {d.castSucc}).comap (stdLevi fourthJ).subtype
    have hle : Subgroup.closure
        ((tailBorel 3 qBin : Set (V0 ≃ₗ[ZMod 2] V0)) ∪ {rhoMinus (natLevi d)}) ≤
          S.map rhoMinus := by
      refine (Subgroup.closure_le _).2 (Set.union_subset ?_ ?_)
      · intro b hb
        obtain ⟨l', rfl⟩ : b ∈ rhoMinus.range := range_rhoMinus ▸ tailBorel_le hb
        exact ⟨l', Subgroup.subset_closure (Or.inl ((mem_stdLeviBorel_iff l').2 hb)), rfl⟩
      · rw [Set.singleton_subset_iff]
        exact ⟨natLevi d, Subgroup.subset_closure (Or.inr ⟨d.castSucc, rfl, rfl⟩), rfl⟩
    obtain ⟨l', hl', e⟩ := hle h
    rw [← rhoMinus_injective e]
    exact hl'

theorem map_inv_mul_eq_iff (g h : V0 ≃ₗ[ZMod 2] V0) (W : Submodule (ZMod 2) V0) :
    W.map ((g⁻¹ * h : V0 ≃ₗ[ZMod 2] V0) : V0 →ₗ[ZMod 2] V0) = W ↔
      W.map (g : V0 →ₗ[ZMod 2] V0) = W.map (h : V0 →ₗ[ZMod 2] V0) := by
  have e : W.map ((g⁻¹ * h : V0 ≃ₗ[ZMod 2] V0) : V0 →ₗ[ZMod 2] V0) =
      (W.map (h : V0 →ₗ[ZMod 2] V0)).map (g.symm : V0 →ₗ[ZMod 2] V0) := by
    rw [← Submodule.map_comp]
    rfl
  rw [e, Submodule.map_symm_eq_iff, eq_comm]

theorem mem_nativeParabolic_singleton_iff
    (d : Fin 3) (x y : nativeParabolic fourthJ) :
    ((x⁻¹ * y : nativeParabolic fourthJ) : ModGL Tag.E6 K) ∈ nativeParabolic {d.castSucc} ↔
      ∀ k, k ≠ d → (residueFlag (QuotientGroup.mk x) : Fin 3 → Submodule (ZMod 2) V0) k =
        (residueFlag (QuotientGroup.mk y) : Fin 3 → Submodule (ZMod 2) V0) k := by
  rw [adjacent_iff two_mem_fourthJ (Set.singleton_subset_iff.mpr (castSucc_mem_fourthJ d)),
    mem_leviParabolic_iff, mem_panelStab, residueFlag_mk, residueFlag_mk,
    and_iff_right (rhoMinus_mem_elementaryGroup _), map_mul, map_inv]
  simp only [leviFlag_apply]
  exact forall₂_congr fun k _ => map_inv_mul_eq_iff _ _ _

end CFSG.LieType.Chevalley.C2E6Std.FourthResidue

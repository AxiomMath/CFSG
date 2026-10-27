module

public import CFSG.LieType.Chevalley.C2E6A5CubeModel
import all CFSG.Fischer.F4
public import CFSG.LocalAnalysis.ComponentInitial.LinearFlagOrder

public noncomputable section

namespace CFSG.LieType.Chevalley.C2E6Std

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley.C2E6Overlap
  CFSG.LieType.Chevalley.ExteriorCube exteriorPower Set Matrix
  CFSG.LocalAnalysis.ComponentInitial

theorem cubeEnd_diagonal_wedgeBasis (d : Fin 6 → K) (I : powersetCard (Fin 6) 3) :
    cubeEnd (diagonal d) (wedgeBasis I) = (∏ i ∈ I.val, d i) • wedgeBasis (R := K) I := by
  rw [cubeEnd_apply, wedgeBasis, map_apply_ιMulti_family, exteriorPower.ιMulti_family,
    exteriorPower.ιMulti_family]
  have h2 : ((Matrix.toLin' (diagonal d) ∘ fun i : Fin 6 => (Pi.single i 1 : Fin 6 → K)) ∘
      enum I) =
        fun k => d (enum I k) • ((fun i : Fin 6 => (Pi.single i 1 : Fin 6 → K)) ∘ enum I) k := by
    funext k
    ext r
    simp only [Function.comp_apply, Matrix.toLin'_apply, Matrix.mulVec_single_one, Pi.smul_apply,
      smul_eq_mul]
    by_cases hr : r = enum I k
    · subst hr
      simp [Matrix.col_apply]
    · simp [Matrix.col_apply, diagonal_apply_ne _ hr, Pi.single_eq_of_ne hr]
  rw [h2, AlternatingMap.map_smul_univ]
  congr 1
  exact Finset.prod_bij (fun k _ => enum I k) (fun k _ => enum_mem I k)
    (fun _ _ _ _ h => (enum I).injective h)
    (fun i hi => let ⟨k, hk⟩ := exists_enum_eq hi; ⟨k, Finset.mem_univ _, hk⟩) (fun _ _ => rfl)

@[expose] def hEntries (t : Fin 5) (s : Kˣ) (i : Fin 6) : K :=
  if i = t.castSucc then (s : K) else if i = t.succ then ((s⁻¹ : Kˣ) : K) else 1

theorem prod_hEntries : ∀ (t : Fin 5) (s : Kˣ), ∏ i, hEntries t s i = 1 := by
  decide +kernel

@[expose] def hDiag (t : Fin 5) (s : Kˣ) : SpecialLinearGroup (Fin 6) K :=
  ⟨diagonal (hEntries t s), by rw [det_diagonal, prod_hEntries]⟩

theorem prod_hEntries_subsetA : ∀ (j : Fin 20) (t : Fin 5) (s : Kˣ),
    ∏ i ∈ subsetA j, hEntries t s i = ((s ^ subsetPattern (subsetA j) t : Kˣ) : K) := by
  decide +kernel

theorem torusElt_mem_groupA
    (t : Fin 5) (s : Kˣ) : torusElt Tag.E6 K (jA t) s ∈ groupA :=
  subsystemTorus_le_subsystemGroup (τ := Tag.E6) (K := K) (A := setA)
    (Subgroup.subset_closure ⟨jA t, jA_mem_setA t, s, rfl⟩)

theorem psiA_torusElt
    (t : Fin 5) (s : Kˣ) :
    psiA ⟨torusElt Tag.E6 K (jA t) s, torusElt_mem_groupA t s⟩ = cubeHom (hDiag t s) := by
  refine Units.ext (((Pi.basisFun K (Fin 6)).exteriorPower 3).ext fun I => ?_)
  obtain ⟨j, rfl⟩ := eA.surjective I
  rw [← wedgeBasis_eq_basis, psiA_apply, coe_cubeHom, ← phiA_vecA, LinearEquiv.symm_apply_apply]
  have h1 : restrictEndA ⟨torusElt Tag.E6 K (jA t) s, torusElt_mem_groupA t s⟩
      ⟨vecA j, vecA_mem j⟩ =
        ((s ^ subsetPattern (subsetA j) t : Kˣ) : K) • ⟨vecA j, vecA_mem j⟩ := by
    apply Subtype.ext
    rw [restrictEndA_apply, SetLike.val_smul]
    change (torusElt Tag.E6 K (jA t) s : Module.End K (RootModule Tag.E6 K)) (vecA j) = _
    rw [torusElt_rootVec _ _ (isRoot_rootA j)]
    congr 3
    exact weight_rootA j t
  rw [h1, map_smul, phiA_vecA]
  have h2 := cubeEnd_diagonal_wedgeBasis (hEntries t s) (eA j)
  rw [eA_val, prod_hEntries_subsetA] at h2
  exact h2.symm

@[expose] def diagGL : Subgroup (GL (Fin 6) K) :=
  (Units.map (Matrix.diagonalRingHom (Fin 6) K).toMonoidHom).range

@[expose] def diagSL : Subgroup (SpecialLinearGroup (Fin 6) K) :=
  diagGL.comap SpecialLinearGroup.toGL

theorem mem_diagSL {g : SpecialLinearGroup (Fin 6) K} :
    g ∈ diagSL ↔ ∃ d : Fin 6 → K, (g : Matrix (Fin 6) (Fin 6) K) = diagonal d := by
  constructor
  · rintro ⟨u, hu⟩
    exact ⟨(u : Fin 6 → K), (congrArg Units.val hu).symm⟩
  · rintro ⟨d, hd⟩
    have hdet : ∏ i, d i = 1 := by rw [← det_diagonal, ← hd]; exact g.2
    have hne : ∀ i, d i ≠ 0 := fun i h0 => by
      have := Finset.prod_eq_zero (Finset.mem_univ i) h0
      rw [hdet] at this
      exact one_ne_zero this
    refine ⟨⟨d, fun i => (d i)⁻¹, funext fun i => mul_inv_cancel₀ (hne i),
      funext fun i => inv_mul_cancel₀ (hne i)⟩, Units.ext ?_⟩
    exact hd.symm

theorem hDiag_mem_diagSL (t : Fin 5) (s : Kˣ) : hDiag t s ∈ diagSL :=
  mem_diagSL.mpr ⟨_, rfl⟩

theorem coe_hDiag (t : Fin 5) (s : Kˣ) :
    (hDiag t s : Matrix (Fin 6) (Fin 6) K) = diagonal (hEntries t s) := rfl

theorem hEntries_telescope : ∀ u : Fin 6 → Kˣ, ∏ i, u i = 1 → ∀ i, (u i : K) =
    hEntries 0 (u 0) i * hEntries 1 (u 0 * u 1) i * hEntries 2 (u 0 * u 1 * u 2) i *
      hEntries 3 (u 0 * u 1 * u 2 * u 3) i * hEntries 4 (u 0 * u 1 * u 2 * u 3 * u 4) i := by
  decide +kernel

theorem diagSL_le_closure :
    diagSL ≤ Subgroup.closure {g | ∃ (t : Fin 5) (s : Kˣ), g = hDiag t s} := by
  intro g hg
  obtain ⟨d, hd⟩ := mem_diagSL.mp hg
  have hdet : ∏ i, d i = 1 := by rw [← det_diagonal, ← hd]; exact g.2
  have hne : ∀ i, d i ≠ 0 := fun i h0 => by
    have := Finset.prod_eq_zero (Finset.mem_univ i) h0
    rw [hdet] at this
    exact one_ne_zero this
  set u : Fin 6 → Kˣ := fun i => Units.mk0 (d i) (hne i)
  have hprod : ∏ i, u i = 1 := Units.ext (by
    rw [Units.coe_prod]
    exact hdet)
  have hg' : g = hDiag 0 (u 0) * hDiag 1 (u 0 * u 1) * hDiag 2 (u 0 * u 1 * u 2) *
      hDiag 3 (u 0 * u 1 * u 2 * u 3) * hDiag 4 (u 0 * u 1 * u 2 * u 3 * u 4) := by
    apply Subtype.ext
    change (g : Matrix (Fin 6) (Fin 6) K) = (hDiag 0 (u 0) : Matrix (Fin 6) (Fin 6) K) *
      hDiag 1 (u 0 * u 1) * hDiag 2 (u 0 * u 1 * u 2) * hDiag 3 (u 0 * u 1 * u 2 * u 3) *
        hDiag 4 (u 0 * u 1 * u 2 * u 3 * u 4)
    rw [coe_hDiag, coe_hDiag, coe_hDiag, coe_hDiag, coe_hDiag, diagonal_mul_diagonal,
      diagonal_mul_diagonal, diagonal_mul_diagonal, diagonal_mul_diagonal, hd]
    congr 1
    funext i
    exact hEntries_telescope u hprod i
  rw [hg']
  refine mul_mem (mul_mem (mul_mem (mul_mem ?_ ?_) ?_) ?_) ?_ <;>
    exact Subgroup.subset_closure ⟨_, _, rfl⟩

theorem torusA_le_groupA
    : torusA ≤ groupA :=
  subsystemTorus_le_subsystemGroup (τ := Tag.E6) (K := K) (A := setA)

theorem map_psiA_le_of_closure
    {X : Subgroup (ModGL Tag.E6 K)} {s : Set (ModGL Tag.E6 K)}
    (hX : X = Subgroup.closure s) (hsA : s ⊆ groupA)
    {T : Subgroup (Module.End K (⋀[K]^3 (Fin 6 → K)))ˣ}
    (hs : ∀ g (hg : g ∈ s), psiA ⟨g, hsA hg⟩ ∈ T) : (X.subgroupOf groupA).map psiA ≤ T := by
  rw [Subgroup.map_le_iff_le_comap]
  intro x hx
  have hle : X ≤ (T.comap psiA).map groupA.subtype := by
    rw [hX, Subgroup.closure_le]
    intro g hg
    exact ⟨⟨g, hsA hg⟩, hs g hg, rfl⟩
  obtain ⟨y, hy, hyx⟩ := hle hx
  rw [show x = y from Subtype.ext hyx.symm]
  exact hy

theorem map_psiA_torusA
    : (torusA.subgroupOf groupA).map psiA = diagSL.map cubeHom := by
  apply le_antisymm
  · refine map_psiA_le_of_closure rfl (fun g hg => ?_) ?_
    · obtain ⟨i, hi, t, rfl⟩ := hg
      exact torusA_le_groupA (Subgroup.subset_closure ⟨i, hi, t, rfl⟩)
    · rintro g ⟨i, hi, s, rfl⟩
      obtain ⟨t, rfl⟩ := exists_jA_of_mem_setA hi
      rw [psiA_torusElt]
      exact Subgroup.mem_map_of_mem _ (hDiag_mem_diagSL t s)
  · refine (Subgroup.map_mono diagSL_le_closure).trans ?_
    rw [MonoidHom.map_closure, Subgroup.closure_le]
    rintro _ ⟨g, ⟨t, s, rfl⟩, rfl⟩
    refine ⟨⟨torusElt Tag.E6 K (jA t) s, torusElt_mem_groupA t s⟩, ?_, psiA_torusElt t s⟩
    exact Subgroup.subset_closure ⟨jA t, jA_mem_setA t, s, rfl⟩

@[expose] def posA : Fin 15 → Fin Tag.E6.rank → ℤ := (
  ![![0, 0, 0, 0, 0, 1], ![0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 1, 1], ![0, 0, 0, 1, 0, 0],
    ![0, 0, 0, 1, 1, 0], ![0, 0, 0, 1, 1, 1], ![0, 0, 1, 0, 0, 0], ![0, 0, 1, 1, 0, 0],
    ![0, 0, 1, 1, 1, 0], ![0, 0, 1, 1, 1, 1], ![1, 0, 0, 0, 0, 0], ![1, 0, 1, 0, 0, 0],
    ![1, 0, 1, 1, 0, 0], ![1, 0, 1, 1, 1, 0], ![1, 0, 1, 1, 1, 1]] : Fin 15 → Fin 6 → ℤ)

theorem posA_injective : Function.Injective posA := by
  intro i j h
  revert i j
  decide

theorem exists_e6Root_eq_posA : ∀ m : Fin 15, ∃ k : Fin 72, e6Root k = posA m := by
  decide +kernel

theorem posA_one_height : ∀ m : Fin 15, posA m (i6 1) = 0 ∧ 0 < height (posA m) := by
  decide

theorem exists_posA_eq : ∀ k : Fin 72, e6Root k (i6 1) = 0 → 0 < height (e6Root k) →
    ∃ m : Fin 15, posA m = e6Root k := by
  decide +kernel

theorem range_posA
    : Set.range posA = parabolicPosRoots Tag.E6 setA := by
  ext α
  constructor
  · rintro ⟨m, rfl⟩
    obtain ⟨k, hk⟩ := exists_e6Root_eq_posA m
    have hr : IsRoot Tag.E6 (posA m) := hk ▸ isRoot_e6Root k
    exact (mem_parabolicPosRoots_setA hr).mpr (posA_one_height m)
  · intro hα
    have hr : IsRoot Tag.E6 α := hα.1.1
    obtain ⟨h1, hh⟩ := (mem_parabolicPosRoots_setA hr).mp hα
    obtain ⟨k, rfl⟩ := exists_e6Root_eq hr
    exact exists_posA_eq k h1 hh

theorem card_unipotentA :
    Nat.card unipotentA = 4 ^ 15 := by
  have hS : ∀ α ∈ parabolicPosRoots Tag.E6 setA, IsRoot Tag.E6 α ∧ 0 < height α :=
    fun _ hα => hα.2
  have hcl : ∀ α ∈ parabolicPosRoots Tag.E6 setA, ∀ β ∈ parabolicPosRoots Tag.E6 setA,
      ∀ a b : ℕ, 1 ≤ a → 1 ≤ b → IsRoot Tag.E6 (a • α + b • β) →
        a • α + b • β ∈ parabolicPosRoots Tag.E6 setA := by
    intro α hα β hβ a b ha hb hr
    refine ⟨⟨hr, fun i hi => ?_⟩, hr, ?_⟩
    · simp only [Pi.add_apply, Pi.smul_apply, hα.1.2 i hi, hβ.1.2 i hi, smul_zero, add_zero]
    · have e : height (a • α + b • β) = a * height α + b * height β := by
        simp only [height, Pi.add_apply, Pi.mul_apply, Pi.natCast_apply, nsmul_eq_mul,
          Finset.sum_add_distrib, Finset.mul_sum]
      have h1 : (0 : ℤ) < a * height α := mul_pos (by exact_mod_cast ha) hα.2.2
      have h2 : (0 : ℤ) < b * height β := mul_pos (by exact_mod_cast hb) hβ.2.2
      rw [e]
      linarith
  have hbij := (positive_root_collection Tag.E6 K).1 _ hS hcl posA posA_injective range_posA
  calc Nat.card unipotentA = Nat.card (Set.univ : Set (Fin 15 → K)) :=
        (Nat.card_congr hbij.equiv).symm
    _ = 4 ^ 15 := by rw [Nat.card_univ, Nat.card_fun, Nat.card_eq_fintype_card, card_K,
        Nat.card_eq_fintype_card, Fintype.card_fin]

theorem unipotentA_le_groupA :
    unipotentA ≤ groupA :=
  parabolicLeviUnipotent_le_subsystemGroup (τ := Tag.E6) (K := K) (A := setA)

theorem xUnit_mem_unipotentA
    (t : Fin 5) (c : K) : xUnit Tag.E6 K (jA t) c ∈ unipotentA := by
  rw [← pinnedX_single]
  refine (le_iSup₂_of_le (Pi.single (jA t) 1) ?_ le_rfl :
    rootSubgroup Tag.E6 K (Pi.single (jA t) 1) ≤ unipotentA) (Subgroup.subset_closure ⟨c, rfl⟩)
  exact mem_parabolicPosRoots_of (single_mem_parabolicRoots (jA_mem_setA t))
    (by rw [height, Finset.sum_pi_single']; simp)

theorem cubeHom_injOn_unitriangular :
    Set.InjOn (cubeHom (K := K)) (LinearFlag.unitriangular 6 K) := by
  intro u hu u' hu' h
  rw [cubeHom_eq_cubeHom_iff] at h
  have hmem : u⁻¹ * u' ∈ LinearFlag.unitriangular 6 K ⊓ LinearFlag.scalars 6 K :=
    ⟨(LinearFlag.unitriangular 6 K).mul_mem ((LinearFlag.unitriangular 6 K).inv_mem hu) hu', h⟩
  rw [LinearFlag.unitriangular_inf_scalars] at hmem
  rw [← inv_mul_eq_one]
  exact hmem

theorem card_map_unitriangular :
    Nat.card ((LinearFlag.unitriangular 6 K).map (cubeHom (K := K))) = 4 ^ 15 := by
  rw [← SetLike.coe_sort_coe, Subgroup.coe_map,
    Nat.card_image_of_injOn cubeHom_injOn_unitriangular, SetLike.coe_sort_coe,
    LinearFlag.card_unitriangular, Nat.card_eq_fintype_card, card_K]

theorem card_unipotentA_subgroupOf
    : Nat.card (unipotentA.subgroupOf groupA) = 4 ^ 15 := by
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe unipotentA_le_groupA).toEquiv,
    card_unipotentA]

@[expose] def psiAOnto
    (H : Subgroup groupA) : H → H.map psiA :=
  fun x => ⟨psiA x, Subgroup.mem_map_of_mem psiA x.2⟩

theorem psiAOnto_surjective
    (H : Subgroup groupA) : Function.Surjective (psiAOnto H) := by
  rintro ⟨y, x, hx, rfl⟩
  exact ⟨⟨x, hx⟩, rfl⟩

theorem psiA_le_unitriangular_map :
    (LinearFlag.unitriangular 6 K).map cubeHom ≤ (unipotentA.subgroupOf groupA).map psiA := by
  refine (Subgroup.map_mono unitriangular_le_closure_upAdjSet).trans ?_
  rw [MonoidHom.map_closure, Subgroup.closure_le]
  rintro _ ⟨g, ⟨t, c, rfl⟩, rfl⟩
  exact ⟨⟨xUnit Tag.E6 K (jA t) c, xUnit_mem_groupA t c⟩, xUnit_mem_unipotentA t c,
    psiA_xUnit t c⟩

theorem map_psiA_unipotentA :
    (unipotentA.subgroupOf groupA).map psiA = (LinearFlag.unitriangular 6 K).map cubeHom := by
  have hfinH : Finite (unipotentA.subgroupOf groupA) :=
    Nat.finite_of_card_ne_zero (by rw [card_unipotentA_subgroupOf]; positivity)
  have hfin : Finite ((unipotentA.subgroupOf groupA).map psiA) :=
    Finite.of_surjective _ (psiAOnto_surjective _)
  have hcard : Nat.card ((unipotentA.subgroupOf groupA).map psiA) ≤ 4 ^ 15 := by
    rw [← card_unipotentA_subgroupOf]
    exact Nat.card_le_card_of_surjective _ (psiAOnto_surjective _)
  exact (Subgroup.eq_of_le_of_card_ge psiA_le_unitriangular_map
    (hcard.trans card_map_unitriangular.ge)).symm

theorem psiA_injOn_unipotentA
    : Set.InjOn psiA (unipotentA.subgroupOf groupA) := by
  have hfinH : Finite (unipotentA.subgroupOf groupA) :=
    Nat.finite_of_card_ne_zero (by rw [card_unipotentA_subgroupOf]; positivity)
  have hbij := (psiAOnto_surjective (unipotentA.subgroupOf groupA)).bijective_of_nat_card_le (by
    rw [map_psiA_unipotentA, card_map_unitriangular, card_unipotentA_subgroupOf])
  intro x hx y hy hxy
  have := hbij.1 (a₁ := ⟨x, hx⟩) (a₂ := ⟨y, hy⟩) (Subtype.ext hxy)
  exact congrArg Subtype.val this

end CFSG.LieType.Chevalley.C2E6Std

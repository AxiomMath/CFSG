module

public import CFSG.LieType.Chevalley.E6A5CubeModel
public import CFSG.LieType.Chevalley.C2E6A5CubeImages

public noncomputable section

namespace CFSG.LieType.Chevalley.E6A5Cube

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley.ExteriorCube exteriorPower
  Set Matrix CFSG.LocalAnalysis.ComponentInitial
open CFSG.LieType.Chevalley.C2E6Std (setA jA rootA subsetA eA subsetPattern posA posA_injective
  range_posA i6 e6Root isRoot_rootA exists_jA_of_mem_setA)

variable {K : Type} [Field K]

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

theorem hEntries_eq_mul (t : Fin 5) (s : Kˣ) (i : Fin 6) :
    hEntries t s i = (if i = t.castSucc then (s : K) else 1) *
      (if i = t.succ then ((s⁻¹ : Kˣ) : K) else 1) := by
  have hne : t.castSucc ≠ t.succ := (Fin.castSucc_lt_succ (i := t)).ne
  by_cases h1 : i = t.castSucc
  · have h2 : i ≠ t.succ := h1 ▸ hne
    simp [hEntries, h1, hne]
  · by_cases h2 : i = t.succ
    · have hne' : t.succ ≠ t.castSucc := hne.symm
      simp [hEntries, h1, h2, hne']
    · simp [hEntries, h1, h2]

theorem prod_hEntries_finset (t : Fin 5) (s : Kˣ) (I : Finset (Fin 6)) :
    ∏ i ∈ I, hEntries t s i = ((s ^ subsetPattern I t : Kˣ) : K) := by
  simp only [hEntries_eq_mul, Finset.prod_mul_distrib]
  rw [Finset.prod_ite_eq' I t.castSucc (fun _ => (s : K)),
    Finset.prod_ite_eq' I t.succ (fun _ => ((s⁻¹ : Kˣ) : K))]
  by_cases ha : t.castSucc ∈ I <;> by_cases hb : t.succ ∈ I <;>
    simp [subsetPattern, ha, hb, _root_.zpow_sub]

theorem prod_hEntries (t : Fin 5) (s : Kˣ) : ∏ i, hEntries t s i = 1 := by
  have := prod_hEntries_finset t s Finset.univ
  rw [this]
  simp [subsetPattern]

variable (K) in
@[expose] def hDiag (t : Fin 5) (s : Kˣ) : SpecialLinearGroup (Fin 6) K :=
  ⟨diagonal (hEntries t s), by rw [det_diagonal, prod_hEntries]⟩

theorem torusElt_mem_groupA
    (t : Fin 5) (s : Kˣ) : torusElt Tag.E6 K (jA t) s ∈ groupA K :=
  subsystemTorus_le_subsystemGroup (τ := Tag.E6) (K := K) (A := setA)
    (Subgroup.subset_closure ⟨jA t, jA_mem_setA t, s, rfl⟩)

theorem psiA_torusElt
    (t : Fin 5) (s : Kˣ) :
    psiA K ⟨torusElt Tag.E6 K (jA t) s, torusElt_mem_groupA t s⟩ = cubeHom (hDiag K t s) := by
  refine Units.ext (((Pi.basisFun K (Fin 6)).exteriorPower 3).ext fun I => ?_)
  obtain ⟨j, rfl⟩ := eA.surjective I
  rw [← wedgeBasis_eq_basis, psiA_apply, coe_cubeHom, ← phiA_vecA, LinearEquiv.symm_apply_apply]
  have h1 : restrictEndA K ⟨torusElt Tag.E6 K (jA t) s, torusElt_mem_groupA t s⟩
      ⟨vecA K j, vecA_mem j⟩ =
        ((s ^ subsetPattern (subsetA j) t : Kˣ) : K) • ⟨vecA K j, vecA_mem j⟩ := by
    apply Subtype.ext
    rw [restrictEndA_apply, SetLike.val_smul]
    change (torusElt Tag.E6 K (jA t) s : Module.End K (RootModule Tag.E6 K)) (vecA K j) = _
    rw [torusElt_rootVec _ _ (isRoot_rootA j)]
    congr 3
    exact C2E6Std.weight_rootA j t
  rw [h1, map_smul, phiA_vecA]
  have h2 := cubeEnd_diagonal_wedgeBasis (hEntries t s) (eA j)
  rw [C2E6Std.eA_val, prod_hEntries_finset] at h2
  exact h2.symm

@[expose] def diagGL : Subgroup (GL (Fin 6) K) :=
  (Units.map (Matrix.diagonalRingHom (Fin 6) K).toMonoidHom).range

variable (K) in
@[expose] def diagSL : Subgroup (SpecialLinearGroup (Fin 6) K) :=
  (diagGL (K := K)).comap SpecialLinearGroup.toGL

theorem mem_diagSL {g : SpecialLinearGroup (Fin 6) K} :
    g ∈ diagSL K ↔ ∃ d : Fin 6 → K, (g : Matrix (Fin 6) (Fin 6) K) = diagonal d := by
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

theorem hDiag_mem_diagSL (t : Fin 5) (s : Kˣ) : hDiag K t s ∈ diagSL K :=
  mem_diagSL.mpr ⟨_, rfl⟩

variable (K) in
abbrev torusA :
    Subgroup (ModGL Tag.E6 K) :=
  subsystemTorus Tag.E6 K setA

variable (K) in
abbrev unipotentA :
    Subgroup (ModGL Tag.E6 K) :=
  parabolicLeviUnipotent Tag.E6 K setA

theorem torusA_le_groupA :
    torusA K ≤ groupA K :=
  subsystemTorus_le_subsystemGroup (τ := Tag.E6) (K := K) (A := setA)

theorem map_psiA_le_of_closure
    {X : Subgroup (ModGL Tag.E6 K)} {s : Set (ModGL Tag.E6 K)}
    (hX : X = Subgroup.closure s) (hsA : s ⊆ groupA K)
    {T : Subgroup (Module.End K (⋀[K]^3 (Fin 6 → K)))ˣ}
    (hs : ∀ g (hg : g ∈ s), psiA K ⟨g, hsA hg⟩ ∈ T) :
    (X.subgroupOf (groupA K)).map (psiA K) ≤ T := by
  rw [Subgroup.map_le_iff_le_comap]
  intro x hx
  have hle : X ≤ (T.comap (psiA K)).map (groupA K).subtype := by
    rw [hX, Subgroup.closure_le]
    intro g hg
    exact ⟨⟨g, hsA hg⟩, hs g hg, rfl⟩
  obtain ⟨y, hy, hyx⟩ := hle hx
  rw [show x = y from Subtype.ext hyx.symm]
  exact hy

theorem map_psiA_torusA_le :
    ((torusA K).subgroupOf (groupA K)).map (psiA K) ≤ (diagSL K).map cubeHom := by
  refine map_psiA_le_of_closure rfl (fun g hg => ?_) ?_
  · obtain ⟨i, hi, t, rfl⟩ := hg
    exact torusA_le_groupA (Subgroup.subset_closure ⟨i, hi, t, rfl⟩)
  · rintro g ⟨i, hi, s, rfl⟩
    obtain ⟨t, rfl⟩ := exists_jA_of_mem_setA hi
    rw [psiA_torusElt]
    exact Subgroup.mem_map_of_mem _ (hDiag_mem_diagSL t s)

theorem card_unipotentA [Finite K] :
    Nat.card (unipotentA K) = Nat.card K ^ 15 := by
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
  calc Nat.card (unipotentA K) = Nat.card (Set.univ : Set (Fin 15 → K)) :=
        (Nat.card_congr hbij.equiv).symm
    _ = Nat.card K ^ 15 := by
      rw [Nat.card_univ, Nat.card_fun, Nat.card_eq_fintype_card (α := Fin 15), Fintype.card_fin]

theorem unipotentA_le_groupA :
    unipotentA K ≤ groupA K :=
  parabolicLeviUnipotent_le_subsystemGroup (τ := Tag.E6) (K := K) (A := setA)

theorem xUnit_mem_unipotentA
    (t : Fin 5) (c : K) : xUnit Tag.E6 K (jA t) c ∈ unipotentA K := by
  rw [← pinnedX_single]
  refine (le_iSup₂_of_le (Pi.single (jA t) 1) ?_ le_rfl :
    rootSubgroup Tag.E6 K (Pi.single (jA t) 1) ≤ unipotentA K) (Subgroup.subset_closure ⟨c, rfl⟩)
  exact mem_parabolicPosRoots_of (single_mem_parabolicRoots (jA_mem_setA t))
    (by rw [height, Finset.sum_pi_single']; simp)

theorem unitriangular_le_closure_upAdjSet :
    LinearFlag.unitriangular 6 K ≤ Subgroup.closure (upAdjSet K) := by
  refine (LinearCover.unitriangular_le_closure_rootElt (K := K) (n := 6)).trans
    ((Subgroup.closure_le _).2 ?_)
  rintro _ ⟨i, j, a, hij, rfl⟩
  rw [LinearCover.rootElt_of_ne hij.ne]
  exact upper_mem_closure_upAdjSet (j.val - i.val - 1) hij (by omega) a

theorem cubeHom_injOn_unitriangular :
    Set.InjOn (cubeHom (K := K)) (LinearFlag.unitriangular 6 K) := by
  intro u hu u' hu' h
  have h1 : cubeHom (u⁻¹ * u') = 1 := by rw [map_mul, map_inv, h, inv_mul_cancel]
  obtain ⟨l, -, hl⟩ := (cubeHom_eq_one_iff _).1 h1
  have hm : u⁻¹ * u' ∈ LinearFlag.unitriangular 6 K := mul_mem (inv_mem hu) hu'
  have hl1 : l = 1 := by
    have := (LinearFlag.mem_unitriangular.mp hm).2 0
    rw [hl] at this
    simpa using this
  rw [hl1, one_smul] at hl
  exact inv_mul_eq_one.1 (Subtype.ext hl)

theorem card_map_unitriangular [Finite K] :
    Nat.card ((LinearFlag.unitriangular 6 K).map (cubeHom (K := K))) = Nat.card K ^ 15 := by
  rw [← SetLike.coe_sort_coe, Subgroup.coe_map,
    Nat.card_image_of_injOn cubeHom_injOn_unitriangular, SetLike.coe_sort_coe,
    LinearFlag.card_unitriangular]

theorem card_unipotentA_subgroupOf [Finite K] :
    Nat.card ((unipotentA K).subgroupOf (groupA K)) = Nat.card K ^ 15 := by
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe unipotentA_le_groupA).toEquiv,
    card_unipotentA]

@[expose] def psiAOnto
    (H : Subgroup (groupA K)) : H → H.map (psiA K) :=
  fun x => ⟨psiA K x, Subgroup.mem_map_of_mem (psiA K) x.2⟩

theorem psiAOnto_surjective
    (H : Subgroup (groupA K)) : Function.Surjective (psiAOnto H) := by
  rintro ⟨y, x, hx, rfl⟩
  exact ⟨⟨x, hx⟩, rfl⟩

theorem psiA_le_unitriangular_map :
    (LinearFlag.unitriangular 6 K).map cubeHom ≤ ((unipotentA K).subgroupOf (groupA K)).map (psiA K) := by
  refine (Subgroup.map_mono unitriangular_le_closure_upAdjSet).trans ?_
  rw [MonoidHom.map_closure, Subgroup.closure_le]
  rintro _ ⟨g, ⟨t, c, rfl⟩, rfl⟩
  exact ⟨⟨xUnit Tag.E6 K (jA t) c, xUnit_mem_groupA t c⟩, xUnit_mem_unipotentA t c,
    psiA_xUnit t c⟩

theorem map_psiA_unipotentA [Finite K] :
    ((unipotentA K).subgroupOf (groupA K)).map (psiA K) =
      (LinearFlag.unitriangular 6 K).map cubeHom := by
  have hfinH : Finite ((unipotentA K).subgroupOf (groupA K)) :=
    Nat.finite_of_card_ne_zero (by
      rw [card_unipotentA_subgroupOf]
      have := Nat.card_pos (α := K)
      positivity)
  have hfin : Finite (((unipotentA K).subgroupOf (groupA K)).map (psiA K)) :=
    Finite.of_surjective _ (psiAOnto_surjective _)
  have hcard : Nat.card (((unipotentA K).subgroupOf (groupA K)).map (psiA K)) ≤ Nat.card K ^ 15 := by
    rw [← card_unipotentA_subgroupOf]
    exact Nat.card_le_card_of_surjective _ (psiAOnto_surjective _)
  exact (Subgroup.eq_of_le_of_card_ge psiA_le_unitriangular_map
    (hcard.trans card_map_unitriangular.ge)).symm

theorem psiA_injOn_unipotentA [Finite K] :
    Set.InjOn (psiA K) ((unipotentA K).subgroupOf (groupA K)) := by
  have hfinH : Finite ((unipotentA K).subgroupOf (groupA K)) :=
    Nat.finite_of_card_ne_zero (by
      rw [card_unipotentA_subgroupOf]
      have := Nat.card_pos (α := K)
      positivity)
  have hbij := (psiAOnto_surjective ((unipotentA K).subgroupOf (groupA K))).bijective_of_nat_card_le
    (by rw [map_psiA_unipotentA, card_map_unitriangular, card_unipotentA_subgroupOf])
  intro x hx y hy hxy
  have := hbij.1 (a₁ := ⟨x, hx⟩) (a₂ := ⟨y, hy⟩) (Subtype.ext hxy)
  exact congrArg Subtype.val this

end CFSG.LieType.Chevalley.E6A5Cube

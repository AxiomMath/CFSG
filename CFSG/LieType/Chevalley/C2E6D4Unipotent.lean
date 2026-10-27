module

public import CFSG.LieType.Chevalley.C2E6D4Model
public import CFSG.LieType.Chevalley.C2E6RootRestrictionTorus
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalSplitGeometryPositive

public noncomputable section

namespace CFSG.LieType.Chevalley.C2E6Std

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley.C2E6Overlap
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.OrthogonalSplit
  CFSG.LieType.Universal.Spin

@[expose] def posD : Fin 12 → Fin Tag.E6.rank → ℤ := (
  ![![0, 0, 0, 0, 1, 0], ![0, 0, 0, 1, 0, 0], ![0, 0, 0, 1, 1, 0], ![0, 0, 1, 0, 0, 0],
    ![0, 0, 1, 1, 0, 0], ![0, 0, 1, 1, 1, 0], ![0, 1, 0, 0, 0, 0], ![0, 1, 0, 1, 0, 0],
    ![0, 1, 0, 1, 1, 0], ![0, 1, 1, 1, 0, 0], ![0, 1, 1, 1, 1, 0], ![0, 1, 1, 2, 1, 0]] :
    Fin 12 → Fin 6 → ℤ)

theorem posD_injective : Function.Injective posD := by
  intro i j h
  revert i j
  decide

theorem exists_e6Root_eq_posD : ∀ m : Fin 12, ∃ k : Fin 72, e6Root k = posD m := by
  decide +kernel

theorem posD_zero_five_height : ∀ m : Fin 12,
    (posD m (i6 0) = 0 ∧ posD m (i6 5) = 0) ∧ 0 < height (posD m) := by
  decide

theorem exists_posD_eq : ∀ k : Fin 72, e6Root k (i6 0) = 0 → e6Root k (i6 5) = 0 →
    0 < height (e6Root k) → ∃ m : Fin 12, posD m = e6Root k := by
  decide +kernel

theorem range_posD
    : Set.range posD = parabolicPosRoots Tag.E6 setD := by
  ext α
  constructor
  · rintro ⟨m, rfl⟩
    obtain ⟨k, hk⟩ := exists_e6Root_eq_posD m
    have hr : IsRoot Tag.E6 (posD m) := hk ▸ isRoot_e6Root k
    exact (mem_parabolicPosRoots_setD hr).mpr (posD_zero_five_height m)
  · intro hα
    have hr : IsRoot Tag.E6 α := hα.1.1
    obtain ⟨⟨h0, h5⟩, hh⟩ := (mem_parabolicPosRoots_setD hr).mp hα
    obtain ⟨k, rfl⟩ := exists_e6Root_eq hr
    exact exists_posD_eq k h0 h5 hh

theorem card_unipotentD :
    Nat.card unipotentD = 4 ^ 12 := by
  have hS : ∀ α ∈ parabolicPosRoots Tag.E6 setD, IsRoot Tag.E6 α ∧ 0 < height α :=
    fun _ hα => hα.2
  have hcl : ∀ α ∈ parabolicPosRoots Tag.E6 setD, ∀ β ∈ parabolicPosRoots Tag.E6 setD,
      ∀ a b : ℕ, 1 ≤ a → 1 ≤ b → IsRoot Tag.E6 (a • α + b • β) →
        a • α + b • β ∈ parabolicPosRoots Tag.E6 setD := by
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
  have hbij := (positive_root_collection Tag.E6 K).1 _ hS hcl posD posD_injective range_posD
  calc Nat.card unipotentD = Nat.card (Set.univ : Set (Fin 12 → K)) :=
        (Nat.card_congr hbij.equiv).symm
    _ = 4 ^ 12 := by rw [Nat.card_univ, Nat.card_fun, Nat.card_eq_fintype_card, card_K,
        Nat.card_eq_fintype_card, Fintype.card_fin]

theorem unipotentD_le_groupD :
    unipotentD ≤ groupD :=
  parabolicLeviUnipotent_le_subsystemGroup (τ := Tag.E6) (K := K) (A := setD)

theorem xUnit_mem_unipotentD
    (k : Fin 4) (c : K) : xUnit Tag.E6 K (jD k) c ∈ unipotentD := by
  rw [← pinnedX_single]
  refine (le_iSup₂_of_le (Pi.single (jD k) 1) ?_ le_rfl :
    rootSubgroup Tag.E6 K (Pi.single (jD k) 1) ≤ unipotentD) (Subgroup.subset_closure ⟨c, rfl⟩)
  exact mem_parabolicPosRoots_of (single_mem_parabolicRoots (jD_mem_setD k))
    (by rw [height, Finset.sum_pi_single']; simp)

theorem card_unipotent_four : Nat.card (unipotent 4 K) = 4 ^ 12 := by
  rw [unipotent_eq_posUnip, card_posUnip, Nat.card_eq_fintype_card, card_K]

theorem card_unipotentD_subgroupOf
    : Nat.card (unipotentD.subgroupOf groupD) = 4 ^ 12 := by
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe unipotentD_le_groupD).toEquiv,
    card_unipotentD]

@[expose] def psiDOnto
    (H : Subgroup groupD) : H → H.map psiD :=
  fun x => ⟨psiD x, Subgroup.mem_map_of_mem psiD x.2⟩

theorem psiDOnto_surjective
    (H : Subgroup groupD) : Function.Surjective (psiDOnto H) := by
  rintro ⟨y, x, hx, rfl⟩
  exact ⟨⟨x, hx⟩, rfl⟩

theorem unipotent_le_map_psiD
    : unipotent 4 K ≤ (unipotentD.subgroupOf groupD).map psiD :=
  unipotent_le_of fun k c =>
    ⟨⟨xUnit Tag.E6 K (jD k) c, xUnit_mem_groupD k c⟩, xUnit_mem_unipotentD k c, psiD_xUnit k c⟩

theorem map_psiD_unipotentD
    : (unipotentD.subgroupOf groupD).map psiD = unipotent 4 K := by
  have hfinH : Finite (unipotentD.subgroupOf groupD) :=
    Nat.finite_of_card_ne_zero (by rw [card_unipotentD_subgroupOf]; positivity)
  have hfin : Finite ((unipotentD.subgroupOf groupD).map psiD) :=
    Finite.of_surjective _ (psiDOnto_surjective _)
  have hcard : Nat.card ((unipotentD.subgroupOf groupD).map psiD) ≤ 4 ^ 12 := by
    rw [← card_unipotentD_subgroupOf]
    exact Nat.card_le_card_of_surjective _ (psiDOnto_surjective _)
  exact (Subgroup.eq_of_le_of_card_ge unipotent_le_map_psiD
    (hcard.trans card_unipotent_four.ge)).symm

theorem psiD_injOn_unipotentD
    : Set.InjOn psiD (unipotentD.subgroupOf groupD) := by
  have hfinH : Finite (unipotentD.subgroupOf groupD) :=
    Nat.finite_of_card_ne_zero (by rw [card_unipotentD_subgroupOf]; positivity)
  have hbij := (psiDOnto_surjective (unipotentD.subgroupOf groupD)).bijective_of_nat_card_le (by
    rw [map_psiD_unipotentD, card_unipotent_four, card_unipotentD_subgroupOf])
  intro x hx y hy hxy
  have := hbij.1 (a₁ := ⟨x, hx⟩) (a₂ := ⟨y, hy⟩) (Subtype.ext hxy)
  exact congrArg Subtype.val this

end CFSG.LieType.Chevalley.C2E6Std

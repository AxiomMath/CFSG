module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10R165ExcE8Four2

public section

namespace CFSG.LocalAnalysis.GLTheoremA.Y10F.ExcE8Spin

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.LieType.SeitzGeneration.ExcHigh CFSG.ClassicalInvolution.RouteD.Exotic
  CFSG.HardMathSupport.Lang.AnisoE8 CFSG.HardMathSupport.Timmesfeld.CrossChar

variable {K : Type} [Field K]

@[expose] def e8D4LeviSimple (j : Fin 4) : Fin (Tag.rank .E8) → ℤ :=
  e8D4Root (Fin.castAdd 4 j)

@[expose] def e8D4PerpSimple (j : Fin 4) : Fin (Tag.rank .E8) → ℤ :=
  e8D4Root (Fin.natAdd 4 j)

@[expose] def e8D4PerpRoots : Set (Fin (Tag.rank .E8) → ℤ) :=
  {α | IsRoot .E8 α ∧ ∀ j : Fin 4, iform (e8D4LeviSimple j) α = 0}

@[expose] def e8D4PerpReach (l : List (Fin 4)) (δ : Fin (Tag.rank .E8) → ℤ) :
    Fin (Tag.rank .E8) → ℤ :=
  l.foldr (fun j u => u - iform (e8D4PerpSimple j) u • e8D4PerpSimple j) δ

@[expose] def e8D4PerpTable : List (Fin 4 × List (Fin 4)) :=
  [(0, [1, 3, 2, 1, 0]),
   (0, [3, 2, 1, 0]),
   (0, [3, 1, 0]),
   (0, [2, 1, 0]),
   (0, [1, 0]),
   (0, [0]),
   (1, [3, 2, 1]),
   (1, [3, 1]),
   (3, [3]),
   (1, [2, 1]),
   (2, [2]),
   (1, [1]),
   (1, []),
   (2, []),
   (1, [2]),
   (3, []),
   (1, [3]),
   (1, [3, 2]),
   (0, []),
   (0, [1]),
   (0, [2, 1]),
   (0, [3, 1]),
   (0, [3, 2, 1]),
   (0, [1, 3, 2, 1])]

theorem e8D4PerpTable_spec :
    ∀ β ∈ rootFinset .E8, (∀ j : Fin 4, iform (e8D4LeviSimple j) β = 0) →
      ∃ e ∈ e8D4PerpTable, e8D4PerpReach e.2 (e8D4PerpSimple e.1) = β := by
  decide +kernel

section Roots


private theorem rootSubgroup_perpSimple_pair_le (j : Fin 4) :
    rootSubgroup Tag.E8 K (e8D4PerpSimple j) ⊔
        rootSubgroup Tag.E8 K (-(e8D4PerpSimple j)) ≤
      (e8D4Perp K).map (adjointGroup Tag.E8 K).subtype := by
  have hpair : rootPairE8 K (e8D4PerpSimple j) ≤ e8D4Perp K := by
    rw [e8D4Perp_eq]
    exact le_iSup (fun i : Fin 4 => rootPairE8 K (e8D4Root (Fin.natAdd 4 i))) j
  refine sup_le (ExcE8Four.rootSubgroup_le_map_of_rootPair_le (e8D4Root_isRoot _) hpair) ?_
  exact ExcE8Four.rootSubgroup_le_map_of_rootPair_le (IsRoot.neg (e8D4Root_isRoot _))
    (by rw [ExcE8Four.rootPairE8_neg]; exact hpair)

private theorem rootSubgroup_perpReach_le (l : List (Fin 4))
    {δ : Fin (Tag.rank .E8) → ℤ} (hδ : IsRoot .E8 δ)
    (h : rootSubgroup Tag.E8 K δ ≤ (e8D4Perp K).map (adjointGroup Tag.E8 K).subtype) :
    IsRoot .E8 (e8D4PerpReach l δ) ∧
      rootSubgroup Tag.E8 K (e8D4PerpReach l δ) ≤
        (e8D4Perp K).map (adjointGroup Tag.E8 K).subtype := by
  induction l with
  | nil => exact ⟨hδ, h⟩
  | cons j l ih =>
    obtain ⟨hr, hle⟩ := ih
    have hstep : e8D4PerpReach (j :: l) δ =
        e8D4PerpReach l δ -
          iform (e8D4PerpSimple j) (e8D4PerpReach l δ) • e8D4PerpSimple j := rfl
    rw [hstep]
    refine ⟨?_, ExcE8Four.rootSubgroup_reflect_le_of_rootPair_le (e8D4Root_isRoot _)
      (rootSubgroup_perpSimple_pair_le j) hr hle⟩
    change IsRoot .E8 (e8D4PerpReach l δ -
      iform (e8D4Root (Fin.natAdd 4 j)) (e8D4PerpReach l δ) • e8D4Root (Fin.natAdd 4 j))
    rw [← rootReflection_smul_SL (τ := Tag.E8) (fun ε hε => iform_self_of_isRoot_E8Fr hε)
      (e8D4Root_isRoot (Fin.natAdd 4 j))]
    exact IsRoot.smul hr _

theorem rootSpan_e8D4PerpRoots_le :
    rootSpan Tag.E8 K e8D4PerpRoots ≤
      (e8D4Perp K).map (adjointGroup Tag.E8 K).subtype := by
  refine iSup₂_le fun β hβ => ?_
  obtain ⟨e, -, he⟩ := e8D4PerpTable_spec β (mem_rootFinset.2 hβ.1) hβ.2
  have hstart : IsRoot .E8 (e8D4PerpSimple e.1) := e8D4Root_isRoot _
  rw [← he]
  exact (rootSubgroup_perpReach_le e.2 hstart
    (le_sup_left.trans (rootSubgroup_perpSimple_pair_le e.1))).2

theorem e8D4Perp_le_rootSpan_e8D4PerpRoots :
    (e8D4Perp K).map (adjointGroup Tag.E8 K).subtype ≤
      rootSpan Tag.E8 K e8D4PerpRoots := by
  rw [e8D4Perp_eq, Subgroup.map_iSup]
  refine iSup_le fun j => ?_
  simp only [rootPairE8, Subgroup.map_sup]
  refine sup_le ?_ ?_
  · rintro x ⟨z, hz, rfl⟩
    have hmem : (z : ModGL Tag.E8 K) ∈ rootSubgroup Tag.E8 K (e8D4PerpSimple j) := by
      have h2 : z ∈ (rootSubgroup Tag.E8 K (e8D4PerpSimple j)).subgroupOf
          (adjointGroup Tag.E8 K) := by
        rw [subgroupOf_rootSubgroup_eq_rootGroup (rootOperatorFamily .E8)
          (show IsRoot .E8 (e8D4PerpSimple j) from e8D4Root_isRoot _)]
        exact hz
      exact Subgroup.mem_subgroupOf.1 h2
    refine rootSubgroup_le_rootSpan ?_ hmem
    rw [e8D4PerpRoots]
    exact ⟨e8D4Root_isRoot _,
      fun i => (e8D4Root_facts i j).2.2.1⟩
  · rintro x ⟨z, hz, rfl⟩
    have hmem : (z : ModGL Tag.E8 K) ∈ rootSubgroup Tag.E8 K (-(e8D4PerpSimple j)) := by
      have h2 : z ∈ (rootSubgroup Tag.E8 K (-(e8D4PerpSimple j))).subgroupOf
          (adjointGroup Tag.E8 K) := by
        rw [subgroupOf_rootSubgroup_eq_rootGroup (rootOperatorFamily .E8)
          (show IsRoot .E8 (-(e8D4PerpSimple j)) from
            IsRoot.neg (e8D4Root_isRoot _))]
        exact hz
      exact Subgroup.mem_subgroupOf.1 h2
    refine rootSubgroup_le_rootSpan ?_ hmem
    rw [e8D4PerpRoots]
    refine ⟨IsRoot.neg (e8D4Root_isRoot _), fun i => ?_⟩
    have hzero : iform (e8D4LeviSimple i) (e8D4PerpSimple j) = 0 := by
      simpa only [e8D4LeviSimple, e8D4PerpSimple] using (e8D4Root_facts i j).2.2.1
    rw [iform_neg_right, hzero, neg_zero]

theorem rootSpan_e8D4PerpRoots_eq :
    rootSpan Tag.E8 K e8D4PerpRoots =
      (e8D4Perp K).map (adjointGroup Tag.E8 K).subtype :=
  le_antisymm rootSpan_e8D4PerpRoots_le e8D4Perp_le_rootSpan_e8D4PerpRoots

end Roots

end CFSG.LocalAnalysis.GLTheoremA.Y10F.ExcE8Spin

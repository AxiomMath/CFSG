module

public import CFSG.LieType.SeitzGeneration.ExcHigh.E8FrameTorus
public import CFSG.LieType.SeitzGeneration.ExcHigh.E8Four
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.PlanesToralWeylFive
public import CFSG.ClassicalInvolution.RouteD.ExoticTwinProofExcLayerAdj
public import CFSG.RankThree.Chevalley.SteinbergBIWE8CertsBase
public import CFSG.Sporadic.Schreier.J4SSylowBase

public noncomputable section

set_option linter.unusedSectionVars false

namespace CFSG.LieType.SeitzGeneration.ExcHigh

open CFSG CFSG.LieType CFSG.LieType.Chevalley CFSG.Blueprint.Chevalley
  CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.LieType.AlgebraicGroups
  CFSG.LieType.Steinberg.Adjoint CFSG.ClassicalInvolution.RouteD.Exotic
  CFSG.HardMathSupport.Lang.AnisoE8

@[expose] def d4d4CharAdd : (Fin Tag.E8.rank → ℤ) →+ (Fin 2 → ZMod 2) where
  toFun v s := ((v (![0, 5] s) : ℤ) : ZMod 2)
  map_zero' := by ext s; simp
  map_add' u v := by ext s; simp

@[expose] def d4d4Char :
    Multiplicative (Fin Tag.E8.rank → ℤ) →* Multiplicative (Fin 2 → ZMod 2) :=
  AddMonoidHom.toMultiplicative d4d4CharAdd

theorem d4d4Char_eq_one_iff (α : Fin Tag.E8.rank → ℤ) :
    d4d4Char (Multiplicative.ofAdd α) = 1 ↔ α 0 % 2 = 0 ∧ α 5 % 2 = 0 := by
  have h : d4d4Char (Multiplicative.ofAdd α) = Multiplicative.ofAdd (d4d4CharAdd α) := rfl
  have hz : ∀ n : ℤ, ((n : ℤ) : ZMod 2) = 0 ↔ n % 2 = 0 := fun n => by
    rw [ZMod.intCast_zmod_eq_zero_iff_dvd]
    push_cast
    omega
  rw [h, ← ofAdd_zero, Multiplicative.ofAdd.injective.eq_iff, funext_iff]
  simp only [Pi.zero_apply, d4d4CharAdd, AddMonoidHom.coe_mk, ZeroHom.coe_mk, hz]
  constructor
  · intro h
    exact ⟨h 0, h 1⟩
  · rintro ⟨h0, h1⟩ s
    fin_cases s
    · exact h0
    · exact h1

@[expose] def d4d4WRoot : Fin 8 → (Fin Tag.E8.rank → ℤ) :=
  ![![0, 1, 0, 1, 1, 0, 0, 0], ![0, 0, 1, 1, 0, 0, 0, 0], ![0, 1, 0, 1, 0, 0, 0, 0],
    ![0, 0, 0, 1, 0, 0, 0, 0], ![0, 1, 1, 2, 2, 2, 2, 1], ![2, 2, 3, 4, 3, 2, 1, 1],
    ![0, 0, 0, 0, 0, 0, 1, 0], ![2, 3, 4, 6, 5, 4, 3, 1]]

theorem d4d4WRoot_isRoot : ∀ i, IsRoot .E8 (d4d4WRoot i) := by
  intro i
  rw [RootCertificate.isRoot_iff (Tag.rootCertificate_check .E8)]
  revert i
  decide +kernel

theorem d4d4WRoot_coord_even : ∀ i : Fin 8,
    d4d4WRoot i 0 % 2 = 0 ∧ d4d4WRoot i 5 % 2 = 0 := by
  decide +kernel

theorem d4d4WRoot_mem_kernelRoots (i : Fin 8) : d4d4WRoot i ∈ kernelRoots d4d4Char :=
  ⟨d4d4WRoot_isRoot i, (d4d4Char_eq_one_iff _).2 (d4d4WRoot_coord_even i)⟩

@[expose] def d4d4W : WeylGroup Tag.E8 :=
  ((List.finRange 8).map fun i => rootReflection (d4d4WRoot i)).prod

theorem d4d4W_smul_foldr (l : List (Fin 8)) (v : Fin Tag.E8.rank → ℤ) :
    (l.map fun i => rootReflection (d4d4WRoot i)).prod • v =
      l.foldr (fun i u => u - iform (d4d4WRoot i) u • d4d4WRoot i) v := by
  induction l with
  | nil => simp
  | cons a l ih =>
    rw [List.map_cons, List.prod_cons, mul_smul, ih, List.foldr_cons,
      rootReflection_smul_SL (τ := Tag.E8) (fun γ hγ => iform_self_of_isRoot_E8Fr hγ)
        (d4d4WRoot_isRoot a)]

theorem d4d4W_fold_fold_single : ∀ k : Fin Tag.E8.rank,
    (List.finRange 8).foldr (fun i u => u - iform (d4d4WRoot i) u • d4d4WRoot i)
      ((List.finRange 8).foldr (fun i u => u - iform (d4d4WRoot i) u • d4d4WRoot i)
        (Pi.single k 1 : Fin Tag.E8.rank → ℤ)) = -Pi.single k 1 := by
  decide +kernel

theorem d4d4W_mul_self : d4d4W * d4d4W = CFSG.RankThree.Chevalley.WeylE8.z :=
  ext_single fun k => by
    rw [mul_smul, d4d4W, d4d4W_smul_foldr, d4d4W_smul_foldr, d4d4W_fold_fold_single,
      CFSG.RankThree.Chevalley.WeylE8.z_smul]

theorem d4d4W_smul_smul (u : Fin Tag.E8.rank → ℤ) : d4d4W • (d4d4W • u) = -u := by
  rw [← mul_smul, d4d4W_mul_self, CFSG.RankThree.Chevalley.WeylE8.z_smul]

theorem d4d4W_mem_closure :
    d4d4W ∈ Subgroup.closure ((fun α => rootReflection α) '' kernelRoots d4d4Char) := by
  unfold d4d4W
  refine Subgroup.list_prod_mem _ fun x hx => ?_
  obtain ⟨i, -, rfl⟩ := List.mem_map.1 hx
  exact Subgroup.subset_closure ⟨d4d4WRoot i, d4d4WRoot_mem_kernelRoots i, rfl⟩

@[expose] def d4d4Reach (l : List (Fin 8)) (δ : Fin Tag.E8.rank → ℤ) : Fin Tag.E8.rank → ℤ :=
  l.foldr (fun j u => u - iform (e8D4Root j) u • e8D4Root j) δ

@[expose] def d4d4Start (i : Fin 8) (b : Bool) : Fin Tag.E8.rank → ℤ :=
  if b then e8D4Root i else -e8D4Root i

@[expose] def d4d4Table : List ((Fin Tag.E8.rank → ℤ) × Fin 8 × Bool × List (Fin 8)) :=
  [(![-2, -3, -4, -6, -5, -4, -3, -2], 4, false, [5, 7, 6, 5]),
    (![-2, -3, -4, -6, -5, -4, -3, -1], 4, false, [7, 6, 5]),
    (![-2, -3, -4, -6, -5, -4, -2, -1], 4, false, [7, 5]),
    (![-2, -2, -3, -4, -3, -2, -2, -1], 4, false, [6, 5]),
    (![-2, -2, -3, -4, -3, -2, -1, -1], 4, false, [5]),
    (![-2, -2, -3, -4, -3, -2, -1, 0], 4, false, []),
    (![0, -1, -1, -2, -2, -2, -2, -1], 5, false, [7, 6]),
    (![0, -1, -1, -2, -2, -2, -1, -1], 5, false, [7]),
    (![0, -1, -1, -2, -2, -2, -1, 0], 7, false, []),
    (![0, -1, -1, -2, -1, 0, 0, 0], 0, false, [1, 3, 2, 1]),
    (![0, -1, -1, -1, -1, 0, 0, 0], 0, false, [3, 2, 1]),
    (![0, -1, -1, -1, 0, 0, 0, 0], 1, false, [3, 2]),
    (![0, -1, 0, -1, -1, 0, 0, 0], 0, false, [3, 1]),
    (![0, -1, 0, -1, 0, 0, 0, 0], 1, false, [3]),
    (![0, -1, 0, 0, 0, 0, 0, 0], 3, false, []),
    (![0, 0, -1, -1, -1, 0, 0, 0], 0, false, [2, 1]),
    (![0, 0, -1, -1, 0, 0, 0, 0], 1, false, [2]),
    (![0, 0, -1, 0, 0, 0, 0, 0], 2, false, []),
    (![0, 0, 0, -1, -1, 0, 0, 0], 0, false, [1]),
    (![0, 0, 0, -1, 0, 0, 0, 0], 1, false, []),
    (![0, 0, 0, 0, -1, 0, 0, 0], 0, false, []),
    (![0, 0, 0, 0, 0, 0, -1, -1], 5, false, [6]),
    (![0, 0, 0, 0, 0, 0, -1, 0], 6, false, []),
    (![0, 0, 0, 0, 0, 0, 0, -1], 5, false, []),
    (![0, 0, 0, 0, 0, 0, 0, 1], 5, true, []),
    (![0, 0, 0, 0, 0, 0, 1, 0], 6, true, []),
    (![0, 0, 0, 0, 0, 0, 1, 1], 5, true, [6]),
    (![0, 0, 0, 0, 1, 0, 0, 0], 0, true, []),
    (![0, 0, 0, 1, 0, 0, 0, 0], 1, true, []),
    (![0, 0, 0, 1, 1, 0, 0, 0], 0, true, [1]),
    (![0, 0, 1, 0, 0, 0, 0, 0], 2, true, []),
    (![0, 0, 1, 1, 0, 0, 0, 0], 1, true, [2]),
    (![0, 0, 1, 1, 1, 0, 0, 0], 0, true, [2, 1]),
    (![0, 1, 0, 0, 0, 0, 0, 0], 3, true, []),
    (![0, 1, 0, 1, 0, 0, 0, 0], 1, true, [3]),
    (![0, 1, 0, 1, 1, 0, 0, 0], 0, true, [3, 1]),
    (![0, 1, 1, 1, 0, 0, 0, 0], 1, true, [3, 2]),
    (![0, 1, 1, 1, 1, 0, 0, 0], 0, true, [3, 2, 1]),
    (![0, 1, 1, 2, 1, 0, 0, 0], 0, true, [1, 3, 2, 1]),
    (![0, 1, 1, 2, 2, 2, 1, 0], 7, true, []),
    (![0, 1, 1, 2, 2, 2, 1, 1], 5, true, [7]),
    (![0, 1, 1, 2, 2, 2, 2, 1], 5, true, [7, 6]),
    (![2, 2, 3, 4, 3, 2, 1, 0], 4, true, []),
    (![2, 2, 3, 4, 3, 2, 1, 1], 4, true, [5]),
    (![2, 2, 3, 4, 3, 2, 2, 1], 4, true, [6, 5]),
    (![2, 3, 4, 6, 5, 4, 2, 1], 4, true, [7, 5]),
    (![2, 3, 4, 6, 5, 4, 3, 1], 4, true, [7, 6, 5]),
    (![2, 3, 4, 6, 5, 4, 3, 2], 4, true, [5, 7, 6, 5])]

theorem d4d4Table_spec : ∀ β ∈ rootFinset .E8, β 0 % 2 = 0 → β 5 % 2 = 0 →
    ∃ e ∈ d4d4Table, e.1 = β ∧ d4d4Reach e.2.2.2 (d4d4Start e.2.1 e.2.2.1) = β := by
  decide +kernel

section RootGroups

variable {K : Type} [Field K]

theorem rootSubgroup_d4d4Start_le (i : Fin 8) (b : Bool) :
    rootSubgroup Tag.E8 K (d4d4Start i b) ≤
      (e8D4Group K).map (adjointGroup Tag.E8 K).subtype := by
  have hroot : IsRoot .E8 (d4d4Start i b) := by
    unfold d4d4Start
    split_ifs
    · exact e8D4Root_isRoot i
    · exact IsRoot.neg (e8D4Root_isRoot i)
  intro x hx
  have hxA : x ∈ adjointGroup Tag.E8 K := rootSubgroup_le_adjointGroup _ hx
  refine ⟨⟨x, hxA⟩, ?_, rfl⟩
  have hmem : (⟨x, hxA⟩ : adjointGroup Tag.E8 K) ∈
      (rootSubgroup Tag.E8 K (d4d4Start i b)).subgroupOf (adjointGroup Tag.E8 K) :=
    Subgroup.mem_subgroupOf.2 hx
  rw [subgroupOf_rootSubgroup_eq_rootGroup (rootOperatorFamily .E8) hroot] at hmem
  have hpair : rootGroup (rootOperatorFamily .E8) K (d4d4Start i b) ≤
      rootPairE8 K (e8D4Root i) := by
    unfold d4d4Start
    split_ifs
    · exact le_sup_left
    · exact le_sup_right
  exact (le_iSup (fun j => rootPairE8 K (e8D4Root j)) i) (hpair hmem)

theorem rootSubgroup_reflect_le {δ : Fin Tag.E8.rank → ℤ} (hδ : IsRoot .E8 δ) (j : Fin 8)
    (h : rootSubgroup Tag.E8 K δ ≤ (e8D4Group K).map (adjointGroup Tag.E8 K).subtype) :
    rootSubgroup Tag.E8 K (δ - iform (e8D4Root j) δ • e8D4Root j) ≤
      (e8D4Group K).map (adjointGroup Tag.E8 K).subtype := by
  set D := (e8D4Group K).map (adjointGroup Tag.E8 K).subtype
  have hγ := e8D4Root_isRoot j
  set s := rootReflection (e8D4Root j) with hs
  have hsδ : s • δ = δ - iform (e8D4Root j) δ • e8D4Root j :=
    rootReflection_smul_SL (τ := Tag.E8) (fun γ hγ => iform_self_of_isRoot_E8Fr hγ) hγ δ
  rw [← hsδ]
  obtain ⟨hnU, hnN, hnM⟩ := rootWeylOne_spec (K := K) hγ
  set n := rootWeylOne Tag.E8 K (e8D4Root j)
  have hnD : n ∈ D := by
    have h0 := rootSubgroup_d4d4Start_le (K := K) j true
    have h1 := rootSubgroup_d4d4Start_le (K := K) j false
    simp only [d4d4Start, if_true, Bool.false_eq_true, if_false] at h0 h1
    exact (sup_le h0 h1) hnU
  intro x hx
  have hconj := conj_mem_rootSpan_of_mapsRootLines (inv_mem hnN) hnM.inv
    (S := {s • δ}) (fun α hα => by rw [Set.mem_singleton_iff.1 hα]; exact IsRoot.smul hδ s)
    (rootSubgroup_le_rootSpan (Set.mem_singleton _) hx)
  rw [Set.image_singleton, inv_smul_smul, inv_inv] at hconj
  have hle : rootSpan Tag.E8 K {δ} ≤ D :=
    iSup₂_le fun β hβ => by rw [Set.mem_singleton_iff.1 hβ]; exact h
  have hx' : x = n * (n⁻¹ * x * n) * n⁻¹ := by group
  rw [hx']
  exact mul_mem (mul_mem hnD (hle hconj)) (inv_mem hnD)

theorem rootSubgroup_d4d4Reach_le (l : List (Fin 8)) {δ : Fin Tag.E8.rank → ℤ}
    (hδ : IsRoot .E8 δ)
    (h : rootSubgroup Tag.E8 K δ ≤ (e8D4Group K).map (adjointGroup Tag.E8 K).subtype) :
    IsRoot .E8 (d4d4Reach l δ) ∧ rootSubgroup Tag.E8 K (d4d4Reach l δ) ≤
      (e8D4Group K).map (adjointGroup Tag.E8 K).subtype := by
  induction l with
  | nil => exact ⟨hδ, h⟩
  | cons j l ih =>
    obtain ⟨hr, hle⟩ := ih
    have hstep : d4d4Reach (j :: l) δ =
        d4d4Reach l δ - iform (e8D4Root j) (d4d4Reach l δ) • e8D4Root j := rfl
    rw [hstep]
    refine ⟨?_, rootSubgroup_reflect_le hr j hle⟩
    rw [← rootReflection_smul_SL (τ := Tag.E8) (fun γ hγ => iform_self_of_isRoot_E8Fr hγ)
      (e8D4Root_isRoot j)]
    exact IsRoot.smul hr _

theorem rootSpan_kernelRoots_le_e8D4Group :
    rootSpan Tag.E8 K (kernelRoots d4d4Char) ≤
      (e8D4Group K).map (adjointGroup Tag.E8 K).subtype := by
  refine iSup₂_le fun β hβ => ?_
  obtain ⟨h0, h5⟩ := (d4d4Char_eq_one_iff β).1 hβ.2
  obtain ⟨e, -, -, he2⟩ := d4d4Table_spec β (mem_rootFinset.2 hβ.1) h0 h5
  have hstart : IsRoot .E8 (d4d4Start e.2.1 e.2.2.1) := by
    unfold d4d4Start
    split_ifs
    · exact e8D4Root_isRoot _
    · exact IsRoot.neg (e8D4Root_isRoot _)
  rw [← he2]
  exact (rootSubgroup_d4d4Reach_le e.2.2.2 hstart (rootSubgroup_d4d4Start_le _ _)).2

theorem mem_e8D4Group_of_mem_rootSpan {x : adjointGroup Tag.E8 K}
    (hx : (x : ModGL Tag.E8 K) ∈ rootSpan Tag.E8 K (kernelRoots d4d4Char)) :
    x ∈ e8D4Group K := by
  obtain ⟨y, hy, hyx⟩ := rootSpan_kernelRoots_le_e8D4Group hx
  have : y = x := Subtype.ext hyx
  rwa [this] at hy

end RootGroups

end CFSG.LieType.SeitzGeneration.ExcHigh

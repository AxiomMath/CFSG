module

public import CFSG.LieType.AlgebraicGroups.E6GraphCentralizerLangWords
public import CFSG.LieType.AlgebraicGroups.ToralCentralizerComponent
public import CFSG.LieType.AlgebraicGroups.ExactAffineRealization
public import CFSG.LieType.Chevalley.LangAdjointDiagonalLift
public import CFSG.LieType.Chevalley.GraphFixedD4TorusWords
public import CFSG.LieType.Chevalley.E6ToralGraphInvolution
import CFSG.LieType.AlgebraicGroups.ConvolutionPoints

public noncomputable section

namespace CFSG.LieType.AlgebraicGroups

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley WithConv

open scoped CFSG.ConvolutionPoints

theorem IsPointClosed.isPointConstructible {k : Type} [Field k] {A : Type} [CommRing A]
    [Algebra k A] [Algebra.FiniteType k A] {S : Set (A →ₐ[k] k)} (h : IsPointClosed k S) :
    IsPointConstructible k S := by
  obtain ⟨Z, hZ, rfl⟩ := h
  have : IsNoetherianRing A := Algebra.FiniteType.isNoetherianRing k A
  refine ⟨Z, ?_, rfl⟩
  rw [← Topology.isConstructible_compl]
  exact (TopologicalSpace.NoetherianSpace.isCompact Zᶜ).isConstructible hZ.isOpen_compl

section Centralizer

variable {τ : Tag} {k : Type} [Field k]

variable (τ k) in
abbrev graphCentralizer (A : ModGL τ k) : Subgroup (ModGL τ k) :=
  adjointGroup τ k ⊓ Subgroup.centralizer {A}

theorem mem_centralizer_singleton_iff_conj_eq {A g : ModGL τ k} :
    g ∈ Subgroup.centralizer {A} ↔ A * g * A⁻¹ = g := by
  rw [Subgroup.mem_centralizer_singleton_iff, mul_inv_eq_iff_eq_mul, eq_comm]

theorem transportPoints_graphCentralizer (A : ModGL τ k) :
    transportPoints (modGLPoint τ k) (graphCentralizer τ k A) =
      groupPoints τ k ∩ {y | y.comp (innerCo (modGLPoint τ k A)) = y} := by
  ext y
  rw [Set.mem_inter_iff, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨g, hg, rfl⟩
    obtain ⟨hgG, hgc⟩ := Subgroup.mem_inf.1 hg
    rw [mem_centralizer_singleton_iff_conj_eq] at hgc
    refine ⟨by rwa [groupPoints, Set.mem_ofPred_eq, toConv_ofConv, MulEquiv.symm_apply_apply], ?_⟩
    have h := point_comp_innerCo (modGLPoint τ k g) (modGLPoint τ k A)
    rw [← map_inv, ← map_mul, ← map_mul, hgc] at h
    exact congrArg ofConv h
  · rintro ⟨hG, hc⟩
    refine ⟨(modGLPoint τ k).symm (toConv y), Subgroup.mem_inf.2 ⟨hG, ?_⟩, ?_⟩
    · rw [mem_centralizer_singleton_iff_conj_eq]
      have h := point_comp_innerCo (toConv y) (modGLPoint τ k A)
      rw [ofConv_toConv, hc] at h
      apply (modGLPoint τ k).injective
      rw [map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply]
      exact h.symm
    · simp only [MulEquiv.apply_symm_apply, ofConv_toConv]

variable [IsAlgClosed k]

theorem isPointClosed_graphCentralizer
    (A : ModGL τ k) :
    IsPointClosed k (transportPoints (modGLPoint τ k) (graphCentralizer τ k A)) := by
  rw [transportPoints_graphCentralizer]
  exact (exceptional_Lang_exact_affine_group_realization k τ).1.1.inter
    (isPointClosed_setOf_comp_eq _)

theorem graphCentralizer_realization
    (A : ModGL τ k)
    (hirr : IsPointIrreducible k (transportPoints (modGLPoint τ k) (graphCentralizer τ k A))) :
    IsConnectedAlgebraicSubgroup k ((graphCentralizer τ k A).map (modGLPoint τ k).toMonoidHom) ∧
      subgroupIdeal (adjointPointSubgroup τ k) ≤
        subgroupIdeal ((graphCentralizer τ k A).map (modGLPoint τ k).toMonoidHom) ∧
      Algebra.Smooth k (GLCoord k (Label τ) ⧸
        subgroupIdeal ((graphCentralizer τ k A).map (modGLPoint τ k).toMonoidHom)) ∧
      ∃ eZ : WithConv ((GLCoord k (Label τ) ⧸
          subgroupIdeal ((graphCentralizer τ k A).map (modGLPoint τ k).toMonoidHom)) →ₐ[k] k) ≃*
            graphCentralizer τ k A, ∀ φ,
        ((eZ φ : graphCentralizer τ k A) : ModGL τ k) =
          (modGLPoint τ k).symm (toConv (φ.ofConv.comp (Ideal.Quotient.mkₐ k _))) := by
  obtain ⟨-, hZ, he⟩ := isConnectedAlgebraicSubgroup_map (modGLPoint τ k) _
    (isPointClosed_graphCentralizer A).isPointConstructible hirr
  have hZG : (graphCentralizer τ k A).map (modGLPoint τ k).toMonoidHom ≤
      adjointPointSubgroup τ k := Subgroup.map_mono inf_le_left
  refine ⟨hZ, fun f hf => mem_pointsIdeal.2 fun y hy => mem_pointsIdeal.1 hf y (hZG hy),
    hZ.smooth.1, he⟩

end Centralizer

section Torus

@[expose] def e6Fold : Fin 6 → Fin 4 :=
  ![0, 1, 2, 3, 2, 0]

@[expose] def e6Unfold : Fin 4 → Fin 6 :=
  ![0, 1, 2, 3]

theorem e6Fold_perm_symm (l : Fin TwistTag.E6.tag.rank) :
    e6Fold (TwistTag.E6.perm.symm l) = e6Fold l := by
  have h : ∀ l : Fin 6, e6Fold ((Equiv.swap (0 : Fin 6) 5 * Equiv.swap 2 4).symm l) =
      e6Fold l := by decide
  exact h l

theorem e6Unfold_e6Fold (l : Fin TwistTag.E6.tag.rank) :
    e6Unfold (e6Fold l) = l ∨ e6Unfold (e6Fold l) = TwistTag.E6.perm.symm l := by
  have h : ∀ l : Fin 6, e6Unfold (e6Fold l) = l ∨
      e6Unfold (e6Fold l) = (Equiv.swap (0 : Fin 6) 5 * Equiv.swap 2 4).symm l := by decide
  exact h l

theorem e6Fold_e6Unfold (i : Fin 4) : e6Fold (e6Unfold i) = i := by
  revert i
  decide

variable {k : Type} [Field k]

theorem rootDiagUnit_commute_iff
    (c a : Fin TwistTag.E6.tag.rank → kˣ) :
    rootDiagUnit TwistTag.E6.tag a * (rootDiagUnit TwistTag.E6.tag c * diagramMap TwistTag.E6 k) =
        (rootDiagUnit TwistTag.E6.tag c * diagramMap TwistTag.E6 k) *
          rootDiagUnit TwistTag.E6.tag a ↔
      (fun i => a (TwistTag.E6.perm.symm i)) = a := by
  rw [mul_assoc, diagramMap_mul_rootDiagUnit, ← mul_assoc, ← mul_assoc, ← rootDiagUnit_mul,
    ← rootDiagUnit_mul, mul_left_inj, rootDiagUnit_injective.eq_iff, mul_comm, mul_right_inj,
    eq_comm]

variable (R : Type) [CommRing R]

@[expose] def e6FixedTorusParam (s : Fin 4 → Rˣ) (j : Fin TwistTag.E6.tag.rank) : Rˣ :=
  ∏ i, s (e6Fold i) ^ TwistTag.E6.tag.cartan.adjugate i j

@[expose] def e6FixedTorusWord (s : Fin 4 → Rˣ) : List (Letter TwistTag.E6.tag × R) :=
  ((List.finRange TwistTag.E6.tag.rank).map fun j =>
    torusWord TwistTag.E6.tag R j (e6FixedTorusParam R s j)).flatten

variable {R}

theorem mapWord_e6FixedTorusWord {S : Type} [CommRing S] (f : R →+* S) (s : Fin 4 → Rˣ) :
    mapWord f (e6FixedTorusWord R s) =
      e6FixedTorusWord S fun i => Units.map f.toMonoidHom (s i) := by
  simp only [e6FixedTorusWord, mapWord_flatten, List.map_map, Function.comp_def, mapWord_torusWord]
  congr 2
  funext j
  congr 1
  simp [e6FixedTorusParam, map_prod, map_zpow]

theorem wordUnit_e6FixedTorusWord
    (s : Fin 4 → kˣ) :
    wordUnit TwistTag.E6.tag k (e6FixedTorusWord k s) =
      rootDiagUnit TwistTag.E6.tag fun l => s (e6Fold l) ^ (3 : ℤ) := by
  rw [e6FixedTorusWord, wordUnit_flatten, List.map_map]
  have h : (wordUnit TwistTag.E6.tag k ∘ fun j =>
      torusWord TwistTag.E6.tag k j (e6FixedTorusParam k s j)) =
      fun j => torusElt TwistTag.E6.tag k j (e6FixedTorusParam k s j) := by
    funext j
    exact wordUnit_torusWord j _
  rw [h, list_prod_torusElt_eq_rootDiagUnit]
  have h3 := cartanChar_prod_zpow_eq_smul (τ := TwistTag.E6.tag) (K := k)
    (Matrix.adjugate_mul TwistTag.E6.tag.cartan) fun i => s (e6Fold i)
  rw [show TwistTag.E6.tag.cartan.det = 3 from det_cartan_E6] at h3
  exact congrArg (rootDiagUnit TwistTag.E6.tag) h3

variable [IsAlgClosed k]

omit [IsAlgClosed k] in
theorem wordUnit_e6FixedTorusCurve
    (z : TorusAffine k 4 0 →ₐ[k] k) :
    wordUnit TwistTag.E6.tag k (mapWord (z : TorusAffine k 4 0 →+* k)
        (e6FixedTorusWord _ (torusUnit k 4 0))) =
      rootDiagUnit TwistTag.E6.tag fun l =>
        Units.map (z : TorusAffine k 4 0 →+* k).toMonoidHom (torusUnit k 4 0 (e6Fold l)) ^
          (3 : ℤ) := by
  rw [mapWord_e6FixedTorusWord, wordUnit_e6FixedTorusWord]

variable (k) in
@[expose] def e6FixedTorusCurve
    : WordCurve TwistTag.E6.tag k :=
  WordCurve.ofWord (TorusAffine k 4 0) (e6FixedTorusWord _ (torusUnit k 4 0))
    (torusAffinePoint (fun _ => 1) Fin.elim0) (by
      rw [wordUnit_e6FixedTorusCurve]
      simp only [units_map_torusUnit, one_zpow]
      exact rootDiagUnit_one)

theorem values_e6FixedTorusCurve_eq_range :
    (e6FixedTorusCurve k).values = Set.range fun s : Fin 4 → kˣ =>
      rootDiagUnit TwistTag.E6.tag fun l => s (e6Fold l) ^ (3 : ℤ) := by
  rw [e6FixedTorusCurve, WordCurve.values_ofWord]
  ext g
  constructor
  · rintro ⟨z, rfl⟩
    exact ⟨fun i => Units.map (z : TorusAffine k 4 0 →+* k).toMonoidHom (torusUnit k 4 0 i),
      (wordUnit_e6FixedTorusCurve z).symm⟩
  · rintro ⟨t, rfl⟩
    refine ⟨torusAffinePoint t Fin.elim0, (wordUnit_e6FixedTorusCurve _).trans ?_⟩
    simp only [units_map_torusUnit]

theorem values_e6FixedTorusCurve
    (c : Fin TwistTag.E6.tag.rank → kˣ) :
    (e6FixedTorusCurve k).values = ((torusGroup TwistTag.E6.tag k ⊓
      graphCentralizer TwistTag.E6.tag k
        (rootDiagUnit TwistTag.E6.tag c * diagramMap TwistTag.E6 k) :
        Subgroup (ModGL TwistTag.E6.tag k)) : Set (ModGL TwistTag.E6.tag k)) := by
  rw [values_e6FixedTorusCurve_eq_range]
  ext g
  constructor
  · rintro ⟨s, rfl⟩
    have hmem : rootDiagUnit TwistTag.E6.tag (fun l => s (e6Fold l) ^ (3 : ℤ)) ∈
        torusGroup TwistTag.E6.tag k := by
      rw [← wordUnit_e6FixedTorusWord, e6FixedTorusWord, wordUnit_flatten, List.map_map]
      refine Subgroup.list_prod_mem _ fun x hx => ?_
      obtain ⟨j, -, rfl⟩ := List.mem_map.1 hx
      rw [Function.comp_apply, wordUnit_torusWord]
      exact Subgroup.subset_closure ⟨(j, _), rfl⟩
    refine Subgroup.mem_inf.2 ⟨hmem, Subgroup.mem_inf.2
      ⟨(exceptional_Lang_adjoint_diagonal_lift TwistTag.E6.tag k
        (fun l => s (e6Fold l) ^ (3 : ℤ))).1, ?_⟩⟩
    rw [Subgroup.mem_centralizer_singleton_iff, rootDiagUnit_commute_iff]
    funext i
    exact congrArg (fun j => s j ^ (3 : ℤ)) (e6Fold_perm_symm i)
  · intro hg
    rw [SetLike.mem_coe, Subgroup.mem_inf, Subgroup.mem_inf] at hg
    obtain ⟨hgT, -, hgc⟩ := hg
    have hT : torusGroup TwistTag.E6.tag k ≤ (rootDiagUnitHom TwistTag.E6.tag k).range := by
      refine (Subgroup.closure_le _).2 ?_
      rintro _ ⟨⟨i, u⟩, rfl⟩
      exact ⟨_, (torusElt_eq_rootDiagUnit i u).symm⟩
    obtain ⟨a, rfl⟩ := hT hgT
    change rootDiagUnit TwistTag.E6.tag a ∈ Subgroup.centralizer _ at hgc
    rw [Subgroup.mem_centralizer_singleton_iff] at hgc
    have ha := (rootDiagUnit_commute_iff c a).1 hgc
    have hroot : ∀ i : Fin 4, ∃ u : kˣ, u ^ (3 : ℤ) = a (e6Unfold i) := by
      intro i
      obtain ⟨z, hz⟩ := IsAlgClosed.exists_pow_nat_eq (a (e6Unfold i) : k) (n := 3)
        (by norm_num)
      have hz0 : z ≠ 0 := by
        rintro rfl
        rw [zero_pow (by norm_num)] at hz
        exact (a (e6Unfold i)).ne_zero hz.symm
      exact ⟨Units.mk0 z hz0, Units.ext (by
        rw [zpow_ofNat, Units.val_pow_eq_pow_val, Units.val_mk0, hz])⟩
    choose u hu using hroot
    refine ⟨u, ?_⟩
    change rootDiagUnit TwistTag.E6.tag _ = rootDiagUnit TwistTag.E6.tag a
    congr 1
    funext l
    rw [hu]
    rcases e6Unfold_e6Fold l with h | h
    · rw [h]
    · rw [h]
      exact congrFun ha l

end Torus

end CFSG.LieType.AlgebraicGroups

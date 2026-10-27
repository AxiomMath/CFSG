module

public import CFSG.LieType.AlgebraicGroups.E6GraphCentralizerLang
import CFSG.LieType.AlgebraicGroups.ConvolutionPoints

public noncomputable section

namespace CFSG.LieType.AlgebraicGroups

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  WithConv

open scoped CFSG.ConvolutionPoints

section Params

@[expose] def d4FoldedCartanInv :
    Matrix (Fin TwistTag.D4.foldedTag.rank) (Fin TwistTag.D4.foldedTag.rank) ℤ :=
  !![2, 1; 3, 2]

theorem d4FoldedCartan_mul_inv : TwistTag.D4.foldedTag.cartan * d4FoldedCartanInv = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

theorem d4_cartan_orbit_sum_folded (a b : Fin TwistTag.D4.foldedTag.rank) :
    ∑ j ∈ Finset.univ.filter (fun j => TwistTag.D4.orbitIndex j = b),
      TwistTag.D4.tag.cartan j (TwistTag.D4.orbitMin a) = TwistTag.D4.foldedTag.cartan a b := by
  fin_cases a <;> fin_cases b <;> decide

theorem orbitIndex_perm_symm_d4 (i : Fin TwistTag.D4.tag.rank) :
    TwistTag.D4.orbitIndex (TwistTag.D4.perm.symm i) = TwistTag.D4.orbitIndex i := by
  simpa using (TwistTag.orbitIndex_perm TwistTag.D4 (TwistTag.D4.perm.symm i)).symm

@[expose] def d4FoldedTorusParam {R : Type} [CommRing R] (s : Fin TwistTag.D4.foldedTag.rank → Rˣ)
    (b : Fin TwistTag.D4.foldedTag.rank) : Rˣ :=
  ∏ c, s c ^ d4FoldedCartanInv b c

variable {K : Type} [Field K]

theorem cartanChar_d4FoldedTorusParam (s : Fin TwistTag.D4.foldedTag.rank → Kˣ)
    (a : Fin TwistTag.D4.foldedTag.rank) :
    cartanChar (fun i => d4FoldedTorusParam s (TwistTag.D4.orbitIndex i))
      (TwistTag.D4.orbitMin a) = s a := by
  unfold cartanChar
  rw [← Finset.prod_fiberwise Finset.univ TwistTag.D4.orbitIndex]
  have h : ∀ c : Fin TwistTag.D4.foldedTag.rank,
      ∏ j ∈ Finset.univ.filter (fun j => TwistTag.D4.orbitIndex j = c),
        d4FoldedTorusParam s (TwistTag.D4.orbitIndex j) ^
          TwistTag.D4.tag.cartan j (TwistTag.D4.orbitMin a) =
      d4FoldedTorusParam s c ^ TwistTag.D4.foldedTag.cartan a c := fun c => by
    rw [← d4_cartan_orbit_sum_folded a c, ← prod_zpow_eq_zpow_sum]
    refine Finset.prod_congr rfl fun j hj => ?_
    rw [(Finset.mem_filter.1 hj).2]
  rw [Finset.prod_congr rfl fun c _ => h c]
  exact prod_zpow_prod_zpow_of_mul_eq_one d4FoldedCartan_mul_inv s a

theorem compat_comp_orbitIndex_d4 {α : Type} (f : Fin TwistTag.D4.foldedTag.rank → α)
    (l : Fin TwistTag.D4.tag.rank) :
    f (TwistTag.D4.orbitIndex (TwistTag.D4.perm l)) = f (TwistTag.D4.orbitIndex l) := by
  rw [TwistTag.orbitIndex_perm]

theorem cartanChar_d4FoldedTorusParam_eq (s : Fin TwistTag.D4.foldedTag.rank → Kˣ) :
    cartanChar (fun i => d4FoldedTorusParam s (TwistTag.D4.orbitIndex i)) =
      fun l => s (TwistTag.D4.orbitIndex l) := by
  refine eq_of_compat_of_orbitMin (t := TwistTag.D4) (σ := RingHom.id K)
    (cartanChar_perm (σ := RingHom.id K) fun i =>
      compat_comp_orbitIndex_d4 (d4FoldedTorusParam s) i)
    (fun i => compat_comp_orbitIndex_d4 s i) fun a => ?_
  rw [cartanChar_d4FoldedTorusParam, TwistTag.orbitIndex_orbitMin]

variable (R : Type) [CommRing R]

@[expose] def d4FixedTorusParam (s : Fin TwistTag.D4.foldedTag.rank → Rˣ)
    (j : Fin TwistTag.D4.tag.rank) : Rˣ :=
  d4FoldedTorusParam s (TwistTag.D4.orbitIndex j)

@[expose] def d4FixedTorusWord (s : Fin TwistTag.D4.foldedTag.rank → Rˣ) :
    List (Letter TwistTag.D4.tag × R) :=
  ((List.finRange TwistTag.D4.tag.rank).map fun j =>
    torusWord TwistTag.D4.tag R j (d4FixedTorusParam R s j)).flatten

variable {R}

theorem mapWord_d4FixedTorusWord {S : Type} [CommRing S] (f : R →+* S)
    (s : Fin TwistTag.D4.foldedTag.rank → Rˣ) :
    mapWord f (d4FixedTorusWord R s) =
      d4FixedTorusWord S fun i => Units.map f.toMonoidHom (s i) := by
  simp only [d4FixedTorusWord, mapWord_flatten, List.map_map, Function.comp_def,
    mapWord_torusWord]
  congr 2
  funext j
  congr 1
  simp [d4FixedTorusParam, d4FoldedTorusParam, map_prod, map_zpow]

end Params

section Torus

variable {K : Type} [Field K]

theorem wordUnit_d4FixedTorusWord (s : Fin TwistTag.D4.foldedTag.rank → Kˣ) :
    wordUnit TwistTag.D4.tag K (d4FixedTorusWord K s) =
      rootDiagUnit TwistTag.D4.tag fun l => s (TwistTag.D4.orbitIndex l) := by
  rw [d4FixedTorusWord, wordUnit_flatten, List.map_map]
  have h : (wordUnit TwistTag.D4.tag K ∘ fun j =>
      torusWord TwistTag.D4.tag K j (d4FixedTorusParam K s j)) =
      fun j => torusElt TwistTag.D4.tag K j (d4FixedTorusParam K s j) := by
    funext j
    exact wordUnit_torusWord j _
  rw [h, list_prod_torusElt_eq_rootDiagUnit]
  exact congrArg (rootDiagUnit TwistTag.D4.tag) (cartanChar_d4FoldedTorusParam_eq s)

theorem wordUnit_d4FixedTorusCurve
    (z : TorusAffine K TwistTag.D4.foldedTag.rank 0 →ₐ[K] K) :
    wordUnit TwistTag.D4.tag K (mapWord (z : TorusAffine K TwistTag.D4.foldedTag.rank 0 →+* K)
        (d4FixedTorusWord _ (torusUnit K TwistTag.D4.foldedTag.rank 0))) =
      rootDiagUnit TwistTag.D4.tag fun l =>
        Units.map (z : TorusAffine K TwistTag.D4.foldedTag.rank 0 →+* K).toMonoidHom
          (torusUnit K TwistTag.D4.foldedTag.rank 0 (TwistTag.D4.orbitIndex l)) := by
  rw [mapWord_d4FixedTorusWord, wordUnit_d4FixedTorusWord]

variable (K) in
@[expose] def d4FixedTorusCurve : WordCurve TwistTag.D4.tag K :=
  WordCurve.ofWord (TorusAffine K TwistTag.D4.foldedTag.rank 0)
    (d4FixedTorusWord _ (torusUnit K TwistTag.D4.foldedTag.rank 0))
    (torusAffinePoint (fun _ => 1) Fin.elim0) (by
      rw [wordUnit_d4FixedTorusCurve]
      simp only [units_map_torusUnit]
      exact rootDiagUnit_one)

theorem values_d4FixedTorusCurve_eq_range :
    (d4FixedTorusCurve K).values = Set.range fun s : Fin TwistTag.D4.foldedTag.rank → Kˣ =>
      rootDiagUnit TwistTag.D4.tag fun l => s (TwistTag.D4.orbitIndex l) := by
  rw [d4FixedTorusCurve, WordCurve.values_ofWord]
  ext g
  constructor
  · rintro ⟨z, rfl⟩
    exact ⟨fun i => Units.map (z : TorusAffine K TwistTag.D4.foldedTag.rank 0 →+* K).toMonoidHom
      (torusUnit K TwistTag.D4.foldedTag.rank 0 i), (wordUnit_d4FixedTorusCurve z).symm⟩
  · rintro ⟨t, rfl⟩
    refine ⟨torusAffinePoint t Fin.elim0, (wordUnit_d4FixedTorusCurve _).trans ?_⟩
    simp only [units_map_torusUnit]

theorem values_d4FixedTorusCurve :
    (d4FixedTorusCurve K).values = ((torusGroup TwistTag.D4.tag K ⊓
      graphCentralizer TwistTag.D4.tag K (diagramMap TwistTag.D4 K) :
        Subgroup (ModGL TwistTag.D4.tag K)) : Set (ModGL TwistTag.D4.tag K)) := by
  rw [values_d4FixedTorusCurve_eq_range]
  ext g
  constructor
  · rintro ⟨s, rfl⟩
    have hmem : rootDiagUnit TwistTag.D4.tag (fun l => s (TwistTag.D4.orbitIndex l)) ∈
        torusGroup TwistTag.D4.tag K := by
      rw [← wordUnit_d4FixedTorusWord, d4FixedTorusWord, wordUnit_flatten, List.map_map]
      refine Subgroup.list_prod_mem _ fun x hx => ?_
      obtain ⟨j, -, rfl⟩ := List.mem_map.1 hx
      rw [Function.comp_apply, wordUnit_torusWord]
      exact Subgroup.subset_closure ⟨(j, _), rfl⟩
    have hadj : torusGroup TwistTag.D4.tag K ≤ adjointGroup TwistTag.D4.tag K :=
      (Subgroup.closure_le _).2 fun _ ⟨p, hp⟩ => hp ▸ torusElt_mem_adjointGroup p.1 p.2
    refine Subgroup.mem_inf.2 ⟨hmem, Subgroup.mem_inf.2 ⟨hadj hmem, ?_⟩⟩
    rw [Subgroup.mem_centralizer_singleton_iff, diagramMap_mul_rootDiagUnit]
    simp only [orbitIndex_perm_symm_d4]
  · intro hg
    rw [SetLike.mem_coe, Subgroup.mem_inf, Subgroup.mem_inf] at hg
    obtain ⟨hgT, -, hgc⟩ := hg
    obtain ⟨a, rfl⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup hgT
    rw [Subgroup.mem_centralizer_singleton_iff, diagramMap_mul_rootDiagUnit] at hgc
    have ha := rootDiagUnit_injective (mul_right_cancel hgc)
    have hc : ∀ i, a (TwistTag.D4.perm i) = Units.map (RingHom.id K).toMonoidHom (a i) :=
      fun i => by
        have h1 := congrFun ha (TwistTag.D4.perm i)
        rw [Equiv.symm_apply_apply] at h1
        exact h1
    refine ⟨fun c => a (TwistTag.D4.orbitMin c), ?_⟩
    refine congrArg (rootDiagUnit TwistTag.D4.tag) ?_
    refine eq_of_compat_of_orbitMin (t := TwistTag.D4) (σ := RingHom.id K)
      (fun i => compat_comp_orbitIndex_d4 (fun c => a (TwistTag.D4.orbitMin c)) i) hc fun b => ?_
    simp only [TwistTag.orbitIndex_orbitMin]

end Torus

end CFSG.LieType.AlgebraicGroups

namespace CFSG.LieType.AlgebraicGroups

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  WithConv

open scoped CFSG.ConvolutionPoints

section Connected

variable {k : Type} [Field k] [IsAlgClosed k]

theorem isPointIrreducible_d4DiagramCentralizer :
    IsPointIrreducible k (transportPoints (modGLPoint TwistTag.D4.tag k)
      (graphCentralizer TwistTag.D4.tag k (diagramMap TwistTag.D4 k))) := by
  have hZ := twistedFixedGroup_id_eq (k := k) TwistTag.D4
  let H : Option ({w // w ∈ relWeylTwist TwistTag.D4} × Fin TwistTag.D4.foldedTag.rank) →
      Subgroup (ModGL TwistTag.D4.tag k) := fun o => match o with
    | none => torusGroup TwistTag.D4.tag k ⊓
        graphCentralizer TwistTag.D4.tag k (diagramMap TwistTag.D4 k)
    | some i => rootSpan TwistTag.D4.tag k ((fun j => i.1.1 • (Pi.single j 1 :
        Fin TwistTag.D4.tag.rank → ℤ)) '' ↑(TwistTag.D4.orbit i.2)) ⊓
          twistedFixedGroup TwistTag.D4 k (RingHom.id k)
  let F : Option ({w // w ∈ relWeylTwist TwistTag.D4} × Fin TwistTag.D4.foldedTag.rank) →
      WordCurve TwistTag.D4.tag k := fun o => match o with
    | none => d4FixedTorusCurve k
    | some i => orbitConjCurve k i.1.1 i.2
  have hFH : ∀ o, (F o).values = (H o : Set (ModGL TwistTag.D4.tag k)) := by
    rintro (_ | ⟨⟨w, hw⟩, a⟩)
    · exact values_d4FixedTorusCurve
    · exact values_orbitConjCurve_eq hw a
  have hset := (fixed_root_generated_normal_subgroup TwistTag.D4 k (RingEquiv.refl k)).2.1
  have hgen := (fixed_positive_orbit_collection TwistTag.D4 k (RingEquiv.refl k)).2
  rw [RingEquiv.toRingHom_refl'] at hset hgen
  have hsup : graphCentralizer TwistTag.D4.tag k (diagramMap TwistTag.D4 k) = ⨆ o, H o := by
    refine le_antisymm (fun g hg => ?_) (iSup_le fun o => ?_)
    · rw [← hZ, ← SetLike.mem_coe, hset] at hg
      obtain ⟨h, hh, c, hc, rfl⟩ := Set.mem_mul.1 hg
      refine mul_mem (Subgroup.mem_iSup_of_mem none ?_) ?_
      · obtain ⟨hhT, hhZ⟩ := Subgroup.mem_inf.1 hh
        refine Subgroup.mem_inf.2 ⟨hhT, ?_⟩
        rw [← hZ]
        exact hhZ
      · rw [SetLike.mem_coe, hgen] at hc
        refine (Subgroup.closure_le _).2 ?_ hc
        rintro _ ⟨w, hw, a, c', rfl⟩
        refine Subgroup.mem_iSup_of_mem (some (⟨w, hw⟩, a)) ?_
        obtain ⟨e, he⟩ := (fixed_root_orbit_parametrization TwistTag.D4 k (RingHom.id k)).1 a w hw
        rw [← he c']
        exact (e _).2
    · rcases o with _ | ⟨⟨w, hw⟩, a⟩
      · exact inf_le_right
      · rw [← hZ]
        exact inf_le_right
  rw [hsup]
  exact isPointIrreducible_iSup_wordCurves F H hFH

theorem D4_diagram_centralizer_connected :
    IsConnectedAlgebraicSubgroup k
        ((graphCentralizer TwistTag.D4.tag k (diagramMap TwistTag.D4 k)).map
          (modGLPoint TwistTag.D4.tag k).toMonoidHom) ∧
      subgroupIdeal (adjointPointSubgroup TwistTag.D4.tag k) ≤
        subgroupIdeal ((graphCentralizer TwistTag.D4.tag k (diagramMap TwistTag.D4 k)).map
          (modGLPoint TwistTag.D4.tag k).toMonoidHom) ∧
      Algebra.Smooth k (GLCoord k (Label TwistTag.D4.tag) ⧸
        subgroupIdeal ((graphCentralizer TwistTag.D4.tag k (diagramMap TwistTag.D4 k)).map
          (modGLPoint TwistTag.D4.tag k).toMonoidHom)) ∧
      ∃ eZ : WithConv ((GLCoord k (Label TwistTag.D4.tag) ⧸
          subgroupIdeal ((graphCentralizer TwistTag.D4.tag k (diagramMap TwistTag.D4 k)).map
            (modGLPoint TwistTag.D4.tag k).toMonoidHom)) →ₐ[k] k) ≃*
              graphCentralizer TwistTag.D4.tag k (diagramMap TwistTag.D4 k), ∀ φ,
        ((eZ φ : graphCentralizer TwistTag.D4.tag k (diagramMap TwistTag.D4 k)) :
          ModGL TwistTag.D4.tag k) =
          (modGLPoint TwistTag.D4.tag k).symm
            (toConv (φ.ofConv.comp (Ideal.Quotient.mkₐ k _))) :=
  graphCentralizer_realization _ isPointIrreducible_d4DiagramCentralizer

end Connected

section Frobenius

variable {k : Type} [Field k] [IsAlgClosed k] (p : ℕ) [Fact p.Prime] [CharP k p]

theorem entrywiseFrobGL_mem_graphCentralizer_d4 (e : ℕ) {g : ModGL TwistTag.D4.tag k}
    (hg : g ∈ graphCentralizer TwistTag.D4.tag k (diagramMap TwistTag.D4 k)) :
    entrywiseFrobGL TwistTag.D4.tag k p e g ∈
      graphCentralizer TwistTag.D4.tag k (diagramMap TwistTag.D4 k) := by
  obtain ⟨hgG, hgc⟩ := Subgroup.mem_inf.1 hg
  rw [Subgroup.mem_centralizer_singleton_iff] at hgc
  have hFrP : entrywiseFrobGL TwistTag.D4.tag k p e (diagramMap TwistTag.D4 k) =
      diagramMap TwistTag.D4 k := by
    simpa using entrywiseFrobGL_diagramMap_zpow TwistTag.D4 p e 1
  refine Subgroup.mem_inf.2 ⟨entrywiseFrobGL_mem p e hgG, ?_⟩
  rw [Subgroup.mem_centralizer_singleton_iff]
  have h := congrArg (entrywiseFrobGL TwistTag.D4.tag k p e) hgc
  rwa [map_mul, map_mul, hFrP] at h

end Frobenius

theorem D4_diagram_centralizer_Lang (p : ℕ) [Fact p.Prime] (hp : p ≠ 2) (k : Type) [Field k]
    [IsAlgClosed k] [CharP k p] {e : ℕ} (he : 1 ≤ e) (c : ModGL TwistTag.D4.tag k)
    (hc : c ∈ graphCentralizer TwistTag.D4.tag k (diagramMap TwistTag.D4 k)) :
    ∃ z ∈ graphCentralizer TwistTag.D4.tag k (diagramMap TwistTag.D4 k),
      z⁻¹ * Units.map (entrywiseHom (iterateFrobenius k p e)) z = c := by
  have _ := hp
  obtain ⟨hZ, -, -, -⟩ := D4_diagram_centralizer_connected (k := k)
  obtain ⟨-, -, -, hlang⟩ := exists_frobTwist_restriction p hZ he 1 fun g hg => by
    rw [frobTwistGL_apply, inv_one, one_mul, mul_one]
    exact entrywiseFrobGL_mem_graphCentralizer_d4 p e hg
  obtain ⟨z, hz, hzc⟩ := hlang c hc
  refine ⟨z, hz, ?_⟩
  rw [frobTwistGL_apply, inv_one, one_mul, mul_one] at hzc
  exact hzc

end CFSG.LieType.AlgebraicGroups

module

public import CFSG.LieType.AlgebraicGroups.SupportedNativeLang
public import CFSG.LieType.Chevalley.LangAdjointDiagonalLift
public import CFSG.LieType.Chevalley.GraphFixedD4TorusWords
public import CFSG.LieType.AlgebraicGroups.ConvolutionPoints

public section

open scoped CFSG.ConvolutionPoints

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

namespace CFSG.LieType.AlgebraicGroups

private noncomputable def cocharDomainWord (k : Type) [Field k] (τ : Tag) (lam : Fin τ.rank → ℤ) :
    List (Letter τ × TorusAffine k 1 0) :=
  ((List.finRange τ.rank).map fun j =>
    torusWord τ (TorusAffine k 1 0) j
      ((torusUnit k 1 0 0) ^ (∑ i, lam i * τ.cartan.adjugate i j))).flatten

private noncomputable def cocharTorusWord (k : Type) [Field k] (τ : Tag) (lam : Fin τ.rank → ℤ)
    (v : kˣ) : List (Letter τ × k) :=
  ((List.finRange τ.rank).map fun j =>
    torusWord τ k j (v ^ (∑ i, lam i * τ.cartan.adjugate i j))).flatten

private noncomputable def cocharElt (k : Type) [Field k]
    (z : TorusAffine k 1 0 →ₐ[k] k) : kˣ :=
  Units.map (z : TorusAffine k 1 0 →+* k).toMonoidHom (torusUnit k 1 0 0)

private theorem exists_zpow_eq_of_pos {k : Type} [Field k] [IsAlgClosed k] {d : ℤ}
    (hd : 0 < d) (a : kˣ) : ∃ c : kˣ, c ^ d = a := by
  obtain ⟨z, hz⟩ := IsAlgClosed.exists_pow_nat_eq (a : k) (n := d.toNat) (by omega)
  have hz0 : z ≠ 0 := by
    rintro rfl
    rw [zero_pow (by omega : d.toNat ≠ 0)] at hz
    exact a.ne_zero hz.symm
  refine ⟨Units.mk0 z hz0, Units.ext ?_⟩
  rw [← Int.toNat_of_nonneg hd.le, zpow_natCast, Units.val_pow_eq_pow_val, Units.val_mk0, hz]

private theorem exists_point_torusUnit {k : Type} [Field k] (a : kˣ) :
    ∃ z : TorusAffine k 1 0 →ₐ[k] k, cocharElt k z = a := by
  refine ⟨torusAffinePoint (fun _ : Fin 1 => a) (fun j : Fin 0 => Fin.elim0 j), ?_⟩
  simpa only [cocharElt] using
    units_map_torusUnit (fun _ : Fin 1 => a) (fun j : Fin 0 => Fin.elim0 j) 0

private theorem mapWord_cocharDomainWord {τ : Tag} {k : Type} [Field k]
    (lam : Fin τ.rank → ℤ) (z : TorusAffine k 1 0 →ₐ[k] k) :
    mapWord (z : TorusAffine k 1 0 →+* k) (cocharDomainWord k τ lam) =
      cocharTorusWord k τ lam (cocharElt k z) := by
  rw [cocharDomainWord, cocharTorusWord, mapWord_flatten, List.map_map]
  congr 1
  exact List.map_congr_left fun j _ => by
    simp only [Function.comp_apply, mapWord_torusWord, map_zpow, cocharElt]

private theorem wordUnit_cocharTorusWord {τ : Tag} {k : Type} [Field k]
    (lam : Fin τ.rank → ℤ) (v : kˣ) :
    wordUnit τ k (cocharTorusWord k τ lam v) =
      rootDiagUnit τ fun i => v ^ (τ.cartan.det * lam i) := by
  rw [cocharTorusWord, wordUnit_flatten, List.map_map]
  simp only [Function.comp_def, wordUnit_torusWord]
  rw [list_prod_torusElt_eq_rootDiagUnit]
  have hcartan : cartanChar (fun j => v ^ (∑ i, lam i * τ.cartan.adjugate i j)) =
      fun i => v ^ (τ.cartan.det * lam i) := by
    have harg : (fun j => v ^ (∑ i, lam i * τ.cartan.adjugate i j)) =
        (fun j => ∏ i, (v ^ lam i) ^ τ.cartan.adjugate i j) := by
      funext j
      rw [← Finset.prod_zpow_eq_zpow_sum]
      exact Finset.prod_congr rfl fun i _ => zpow_mul _ _ _
    rw [harg, cartanChar_prod_zpow_eq_smul (Matrix.adjugate_mul _)]
    funext i
    rw [← zpow_mul, mul_comm]
  rw [hcartan]

private theorem point_cocharCurve {τ : Tag} {k : Type} [Field k]
    (lam : Fin τ.rank → ℤ) (z : TorusAffine k 1 0 →ₐ[k] k) :
    z.comp (unitCo k (wordUnit τ (TorusAffine k 1 0) (cocharDomainWord k τ lam))) =
      (modGLPoint τ k (rootDiagUnit τ fun i =>
        (cocharElt k z) ^ (τ.cartan.det * lam i))).ofConv := by
  rw [comp_unitCo_wordUnit, mapWord_cocharDomainWord, wordUnit_cocharTorusWord]

private theorem subset_range_cocharCurve {τ : Tag} {k : Type} [Field k]
    [IsAlgClosed k] (lam : Fin τ.rank → ℤ) :
    SeminaireExp3.ZariskiGL.pt '' (modGLZariski τ k ''
        Set.range (fun c : kˣ => rootDiagUnit τ fun i => c ^ lam i)) ⊆
      Set.range (fun z : TorusAffine k 1 0 →ₐ[k] k =>
        z.comp (unitCo k (wordUnit τ (TorusAffine k 1 0) (cocharDomainWord k τ lam)))) := by
  rintro y ⟨g, hg, rfl⟩
  obtain ⟨g₀, hg₀, rfl⟩ := hg
  obtain ⟨c, rfl⟩ := hg₀
  rw [pt_modGLZariski]
  obtain ⟨c₀, hc₀⟩ := exists_zpow_eq_of_pos (det_cartan_pos τ) c
  obtain ⟨z, hz⟩ := exists_point_torusUnit c₀
  refine ⟨z, ?_⟩
  change z.comp (unitCo k (wordUnit τ (TorusAffine k 1 0)
    (cocharDomainWord k τ lam))) = _
  rw [point_cocharCurve lam z, hz, ← hc₀]
  rw [show (fun i => c₀ ^ (τ.cartan.det * lam i)) =
      fun i => (c₀ ^ τ.cartan.det) ^ lam i by
    funext i
    rw [zpow_mul]]

private theorem subset_range_cocharCurve' {τ : Tag} {k : Type} [Field k]
    (lam : Fin τ.rank → ℤ) :
    Set.range (fun z : TorusAffine k 1 0 →ₐ[k] k =>
        z.comp (unitCo k (wordUnit τ (TorusAffine k 1 0) (cocharDomainWord k τ lam)))) ⊆
      SeminaireExp3.ZariskiGL.pt '' (modGLZariski τ k ''
        Set.range (fun c : kˣ => rootDiagUnit τ fun i => c ^ lam i)) := by
  rintro _ ⟨z, rfl⟩
  change z.comp (unitCo k (wordUnit τ (TorusAffine k 1 0)
    (cocharDomainWord k τ lam))) ∈ _
  rw [point_cocharCurve lam z]
  refine ⟨modGLZariski τ k (rootDiagUnit τ (fun i =>
    ((cocharElt k z) ^ τ.cartan.det) ^ lam i)), ?_, ?_⟩
  · exact ⟨_, ⟨(cocharElt k z) ^ τ.cartan.det, rfl⟩, rfl⟩
  · rw [pt_modGLZariski]
    rw [show (fun i => ((cocharElt k z) ^ τ.cartan.det) ^ lam i) =
        fun i => (cocharElt k z) ^ (τ.cartan.det * lam i) by
      funext i
      rw [zpow_mul]]

private theorem range_cocharCurve {τ : Tag} {k : Type} [Field k]
    [IsAlgClosed k] (lam : Fin τ.rank → ℤ) :
    SeminaireExp3.ZariskiGL.pt '' (modGLZariski τ k ''
        Set.range (fun c : kˣ => rootDiagUnit τ fun i => c ^ lam i)) =
      Set.range (fun z : TorusAffine k 1 0 →ₐ[k] k =>
        z.comp (unitCo k (wordUnit τ (TorusAffine k 1 0) (cocharDomainWord k τ lam)))) :=
  Set.Subset.antisymm (subset_range_cocharCurve lam) (subset_range_cocharCurve' lam)

private theorem one_mem_cocharCurveSet {τ : Tag} {k : Type} [Field k]
    (lam : Fin τ.rank → ℤ) :
    (1 : SeminaireExp3.ZariskiGL (Label τ) k) ∈
      modGLZariski τ k '' Set.range (fun c : kˣ => rootDiagUnit τ fun i => c ^ lam i) := by
  refine ⟨1, ⟨1, ?_⟩, map_one _⟩
  change rootDiagUnit τ (fun i => (1 : kˣ) ^ lam i) = 1
  rw [show (fun i : Fin τ.rank => (1 : kˣ) ^ lam i) = 1 by
    funext i
    simp, rootDiagUnit_one]

private theorem image_generatingSet {τ : Tag} {k : Type} [Field k]
    (Λ : Set (Fin τ.rank → ℤ)) :
    modGLZariski τ k ''
        {g : ModGL τ k | ∃ lam ∈ Λ, ∃ c : kˣ, g = rootDiagUnit τ fun i => c ^ lam i} =
      ⋃ lam : Λ, modGLZariski τ k ''
        Set.range (fun c : kˣ => rootDiagUnit τ fun i => c ^ lam.1 i) := by
  ext y
  constructor
  · intro hy
    obtain ⟨g, hg, hgy⟩ := hy
    obtain ⟨lam, hlam, c, hgc⟩ := hg
    rw [← hgy, hgc]
    exact Set.mem_iUnion.2 ⟨⟨lam, hlam⟩, rootDiagUnit τ (fun i => c ^ lam i),
      ⟨c, rfl⟩, rfl⟩
  · intro hy
    obtain ⟨lam, hmem⟩ := Set.mem_iUnion.1 hy
    obtain ⟨g, hg, hgy⟩ := hmem
    obtain ⟨c, hgc⟩ := hg
    rw [← hgy, ← hgc]
    exact ⟨rootDiagUnit τ (fun i => c ^ lam.1 i), ⟨lam.1, lam.2, c, rfl⟩, rfl⟩

theorem isDomainImage_cocharCurve {τ : Tag} {k : Type} [Field k]
    [IsAlgClosed k]
    (lam : Fin τ.rank → ℤ) :
    SeminaireExp3.IsDomainImage k (SeminaireExp3.ZariskiGL.pt ''
      (modGLZariski τ k '' Set.range fun c : kˣ => rootDiagUnit τ fun i => c ^ lam i)) := by
  exact ⟨TorusAffine k 1 0, inferInstance, inferInstance, inferInstance, inferInstance,
    unitCo k (wordUnit τ (TorusAffine k 1 0) (cocharDomainWord k τ lam)),
    range_cocharCurve lam⟩

theorem isConnectedAlgebraicSubgroup_closure_cocharCurve {τ : Tag} {k : Type} [Field k]
    [IsAlgClosed k] (Λ : Set (Fin τ.rank → ℤ)) :
    IsConnectedAlgebraicSubgroup k ((Subgroup.closure {g : ModGL τ k |
      ∃ lam ∈ Λ, ∃ c : kˣ, g = rootDiagUnit τ fun i => c ^ lam i}).map
        (modGLPoint τ k).toMonoidHom) := by
  let S : Set (ModGL τ k) :=
    {g | ∃ lam ∈ Λ, ∃ c : kˣ, g = rootDiagUnit τ fun i => c ^ lam i}
  let W : Λ → Set (SeminaireExp3.ZariskiGL (Label τ) k) := fun lam =>
    modGLZariski τ k '' Set.range (fun c : kˣ => rootDiagUnit τ fun i => c ^ lam.1 i)
  have hW : ∀ lam : Λ, SeminaireExp3.IsDomainImage k
      (SeminaireExp3.ZariskiGL.pt '' W lam) := fun lam => isDomainImage_cocharCurve lam.1
  have h1 : ∀ lam : Λ, (1 : SeminaireExp3.ZariskiGL (Label τ) k) ∈ W lam :=
    fun lam => one_mem_cocharCurveSet lam.1
  obtain ⟨-, -, a, ha⟩ := SeminaireExp3.ZariskiGL.closure_eq_wordSet W hW h1
  have hS : modGLZariski τ k '' S = ⋃ lam : Λ, W lam := image_generatingSet Λ
  have himg : modGLZariski τ k '' (Subgroup.closure S : Set (ModGL τ k)) =
      SeminaireExp3.ZariskiGL.wordSet W a := by
    rw [← ha, ← hS]
    change (modGLZariski τ k).toMonoidHom '' (Subgroup.closure S : Set (ModGL τ k)) =
      ↑(Subgroup.closure ((modGLZariski τ k).toMonoidHom '' S))
    rw [← MonoidHom.map_closure, Subgroup.coe_map]
  have hdom : SeminaireExp3.IsDomainImage k
      (transportPoints (modGLPoint τ k) (Subgroup.closure S : Set (ModGL τ k))) := by
    rw [transportPoints_eq_image_modGLZariski, himg]
    exact SeminaireExp3.ZariskiGL.isDomainImage_wordSet W hW a
  exact (isConnectedAlgebraicSubgroup_map (modGLPoint τ k) (Subgroup.closure S)
    hdom.isPointConstructible hdom.isPointIrreducible).2.1

end CFSG.LieType.AlgebraicGroups

end

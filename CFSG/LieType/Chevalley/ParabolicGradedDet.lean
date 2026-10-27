module

public import CFSG.LieType.Chevalley.ParabolicRadicalLevi

public noncomputable section

namespace CFSG.LieType.Chevalley

open CFSG.Blueprint.Chevalley

variable {τ : Tag} {K : Type} [Field K]

section Certificates


@[expose] def gradedRoots (τ : Tag) (J : Set (Fin τ.rank)) (d : ℤ) : Finset (Fin τ.rank → ℤ) :=
  (rootFinset τ).filter fun α => parabolicDegree τ J α = d

theorem mem_gradedRoots {J : Set (Fin τ.rank)} {d : ℤ} {α : Fin τ.rank → ℤ} :
    α ∈ gradedRoots τ J d ↔ IsRoot τ α ∧ parabolicDegree τ J α = d := by
  simp [gradedRoots, mem_rootFinset]

@[expose] def gradedWeight (τ : Tag) (J : Set (Fin τ.rank)) (d : ℤ) (i : Fin τ.rank) : ℤ :=
  ∑ α ∈ gradedRoots τ J d, ∑ j, τ.cartan i j * α j

theorem parabolicGraded_eq_span_rootVec {J : Set (Fin τ.rank)} {d : ℤ} (hd : d ≠ 0) :
    parabolicGraded τ K J d =
      Submodule.span K
        (Set.range fun α : {α // α ∈ gradedRoots τ J d} => rootVec τ K α.1) := by
  rw [parabolicGraded]
  have hzero : {x : RootModule τ K | d = 0 ∧ ∃ i, x = hVec τ K i} = ∅ := by
    ext x
    simp [hd]
  rw [hzero, Set.union_empty]
  congr 1
  ext x
  constructor
  · rintro ⟨α, hα, hd', rfl⟩
    exact ⟨⟨α, mem_gradedRoots.2 ⟨hα, hd'⟩⟩, rfl⟩
  · rintro ⟨⟨α, hα⟩, rfl⟩
    exact ⟨α, (mem_gradedRoots.1 hα).1, (mem_gradedRoots.1 hα).2, rfl⟩

theorem linearIndependent_gradedRootVec (τ : Tag) (J : Set (Fin τ.rank)) (d : ℤ) :
    LinearIndependent K (fun α : {α // α ∈ gradedRoots τ J d} => rootVec τ K α.1) := by
  have hinj : Function.Injective
      (fun α : {α // α ∈ gradedRoots τ J d} =>
        (Sum.inr ⟨α.1, (mem_gradedRoots.1 α.2).1⟩ : Label τ)) := by
    intro a b hab
    have h1 : (⟨a.1, (mem_gradedRoots.1 a.2).1⟩ : {v : Fin τ.rank → ℤ // IsRoot τ v}) =
        ⟨b.1, (mem_gradedRoots.1 b.2).1⟩ := Sum.inr_injective hab
    have h2 : a.1 = b.1 := congrArg (fun x : {v : Fin τ.rank → ℤ // IsRoot τ v} => x.1) h1
    exact Subtype.ext h2
  have h := (Finsupp.basisSingleOne (R := K) (ι := Label τ)).linearIndependent.comp _ hinj
  have hfun : (fun α : {α // α ∈ gradedRoots τ J d} => rootVec τ K α.1) =
      fun α => Finsupp.single (Sum.inr ⟨α.1, (mem_gradedRoots.1 α.2).1⟩) 1 := by
    funext α
    exact rootVec_eq_single_of_isRoot _
  rw [hfun]
  exact h

@[expose] def gradedBasis {J : Set (Fin τ.rank)} {d : ℤ} (hd : d ≠ 0) :
    Module.Basis {α // α ∈ gradedRoots τ J d} K (parabolicGraded τ K J d) :=
  (Module.Basis.span (linearIndependent_gradedRootVec τ (K := K) J d)).map
    (LinearEquiv.ofEq _ _ (parabolicGraded_eq_span_rootVec (K := K) hd).symm)

@[simp]
theorem gradedBasis_apply {J : Set (Fin τ.rank)} {d : ℤ} (hd : d ≠ 0)
    (α : {α // α ∈ gradedRoots τ J d}) :
    ((gradedBasis (K := K) hd α : parabolicGraded τ K J d) : RootModule τ K) =
      rootVec τ K α.1 := by
  simp [gradedBasis, Module.Basis.span_apply]

@[expose] def gradedRestrictHom (J : Set (Fin τ.rank)) (d : ℤ) :
    ↥(parabolicLevi τ K J) →* Module.End K (parabolicGraded τ K J d) where
  toFun g :=
    LinearMap.restrict (g : ModGL τ K) fun x hx => parabolicLevi_preserves g.2 d hx
  map_one' := by
    ext x
    simp [LinearMap.restrict_apply]
  map_mul' := by
    intro g h
    ext x
    simp [LinearMap.restrict_apply, Module.End.mul_apply]

theorem coe_gradedRestrictHom (J : Set (Fin τ.rank)) (d : ℤ)
    (g : ↥(parabolicLevi τ K J)) (x : parabolicGraded τ K J d) :
    ((gradedRestrictHom (K := K) J d g x : parabolicGraded τ K J d) : RootModule τ K) =
      ((g : ModGL τ K) : Module.End K (RootModule τ K)) (x : RootModule τ K) := rfl

@[expose] def parabolicGradedDet (J : Set (Fin τ.rank)) (d : ℤ) :
    ↥(parabolicLevi τ K J) →* Kˣ :=
  ((LinearMap.det (M := parabolicGraded τ K J d)).comp (gradedRestrictHom (K := K) J d)).toHomUnits

@[simp]
theorem coe_parabolicGradedDet (J : Set (Fin τ.rank)) (d : ℤ)
    (g : ↥(parabolicLevi τ K J)) :
    ((parabolicGradedDet (K := K) J d g : Kˣ) : K) =
      LinearMap.det (M := parabolicGraded τ K J d) (gradedRestrictHom (K := K) J d g) := rfl

theorem gradedRestrictHom_torusElt {J : Set (Fin τ.rank)} {d : ℤ} (hd : d ≠ 0)
    (i : Fin τ.rank) (u : Kˣ) (α : {α // α ∈ gradedRoots τ J d}) :
    gradedRestrictHom (K := K) J d ⟨torusElt τ K i u, torusGroup_le_parabolicLevi J (torusElt_mem_torusGroup i u)⟩
        (gradedBasis (K := K) hd α) =
      ((u ^ (∑ j, τ.cartan i j * α.1 j) : Kˣ) : K) • gradedBasis (K := K) hd α := by
  refine Subtype.ext ?_
  rw [Submodule.coe_smul, coe_gradedRestrictHom, gradedBasis_apply]
  exact torusElt_rootVec i u (mem_gradedRoots.1 α.2).1

theorem parabolicGradedDet_torusElt {J : Set (Fin τ.rank)} {d : ℤ} (hd : d ≠ 0)
    (i : Fin τ.rank) (u : Kˣ) :
    parabolicGradedDet (K := K) J d ⟨torusElt τ K i u, torusGroup_le_parabolicLevi J (torusElt_mem_torusGroup i u)⟩ =
      u ^ gradedWeight τ J d i := by
  refine Units.ext ?_
  rw [coe_parabolicGradedDet, ← LinearMap.det_toMatrix (gradedBasis (K := K) hd)]
  have hdiag : LinearMap.toMatrix (gradedBasis (K := K) hd) (gradedBasis (K := K) hd)
      (gradedRestrictHom (K := K) J d
        ⟨torusElt τ K i u, torusGroup_le_parabolicLevi J (torusElt_mem_torusGroup i u)⟩) =
      Matrix.diagonal
        (fun α : {α // α ∈ gradedRoots τ J d} =>
          ((u ^ (∑ j, τ.cartan i j * α.1 j) : Kˣ) : K)) := by
    ext α β
    rw [LinearMap.toMatrix_apply, gradedRestrictHom_torusElt hd, map_smul,
      Module.Basis.repr_self, Finsupp.smul_single, Matrix.diagonal_apply]
    by_cases h : α = β
    · subst h; simp
    · simp [h]
  have hprod : (∏ α : {α // α ∈ gradedRoots τ J d},
      u ^ (∑ j, τ.cartan i j * α.1 j)) = u ^ gradedWeight τ J d i := by
    rw [Finset.prod_zpow_eq_zpow_sum]
    congr 1
    simpa [gradedWeight] using
      (Finset.sum_coe_sort (gradedRoots τ J d) (fun α => ∑ j, τ.cartan i j * α j))
  rw [hdiag, Matrix.det_diagonal, ← Units.coe_prod, hprod]


private theorem mul_mul_inv_mul_inv_eq_one (a b : Kˣ) : a * b * a⁻¹ * b⁻¹ = 1 := by
  rw [mul_assoc a b a⁻¹, mul_comm b a⁻¹, ← mul_assoc a a⁻¹ b, mul_inv_cancel, one_mul,
    mul_inv_cancel]

private theorem xUnit_eq_conj_mul_inv {j : Fin τ.rank} (u : Kˣ) (hu : ((u : K)) ^ 2 ≠ 1) (c : K) :
    xUnit τ K j c =
      torusElt τ K j u * xUnit τ K j (c / (((u : K)) ^ 2 - 1)) * (torusElt τ K j u)⁻¹ *
        (xUnit τ K j (c / (((u : K)) ^ 2 - 1)))⁻¹ := by
  have hu' : ((u : K)) ^ 2 - 1 ≠ 0 := sub_ne_zero.2 hu
  rw [torusElt_mul_xUnit_mul_inv, ← xUnit_neg, ← xUnit_add]
  congr 1
  field_simp
  ring

private theorem val_zpow_neg_two_ne_one {u : Kˣ} (hu : ((u : K)) ^ 2 ≠ 1) :
    (((u ^ (-2 : ℤ) : Kˣ) : K)) ≠ 1 := by
  rw [Units.val_zpow_eq_zpow_val, zpow_neg, zpow_ofNat]
  exact inv_ne_one.2 (by simpa using hu)

private theorem yUnit_eq_conj_mul_inv {j : Fin τ.rank} (u : Kˣ) (hu : ((u : K)) ^ 2 ≠ 1) (c : K) :
    yUnit τ K j c =
      torusElt τ K j u * yUnit τ K j (c / ((((u ^ (-2 : ℤ) : Kˣ) : K)) - 1)) *
        (torusElt τ K j u)⁻¹ *
        (yUnit τ K j (c / ((((u ^ (-2 : ℤ) : Kˣ) : K)) - 1)))⁻¹ := by
  have hu' : (((u ^ (-2 : ℤ) : Kˣ) : K)) - 1 ≠ 0 :=
    sub_ne_zero.2 (val_zpow_neg_two_ne_one hu)
  rw [(simple_torus_root_conjugation τ K j j u _).2, Tag.cartan_self, ← yUnit_neg, ← yUnit_add]
  congr 1
  field_simp
  ring

theorem parabolicGradedDet_xUnit_eq_one {J : Set (Fin τ.rank)} (d : ℤ) {j : Fin τ.rank}
    (hj : j ∈ J) (u : Kˣ) (hu : ((u : K)) ^ 2 ≠ 1) (c : K) :
    parabolicGradedDet (K := K) J d ⟨xUnit τ K j c, xUnit_mem_parabolicLevi hj c⟩ = 1 := by
  have heq : (⟨xUnit τ K j c, xUnit_mem_parabolicLevi hj c⟩ : ↥(parabolicLevi τ K J)) =
      ⟨torusElt τ K j u, torusGroup_le_parabolicLevi J (torusElt_mem_torusGroup j u)⟩ *
        ⟨xUnit τ K j (c / (((u : K)) ^ 2 - 1)),
          xUnit_mem_parabolicLevi hj _⟩ *
        ⟨torusElt τ K j u, torusGroup_le_parabolicLevi J (torusElt_mem_torusGroup j u)⟩⁻¹ *
        ⟨xUnit τ K j (c / (((u : K)) ^ 2 - 1)),
          xUnit_mem_parabolicLevi hj _⟩⁻¹ := by
    refine Subtype.ext ?_
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    exact xUnit_eq_conj_mul_inv u hu c
  rw [heq, map_mul, map_mul, map_mul, map_inv, map_inv]
  exact mul_mul_inv_mul_inv_eq_one _ _

theorem parabolicGradedDet_yUnit_eq_one {J : Set (Fin τ.rank)} (d : ℤ) {j : Fin τ.rank}
    (hj : j ∈ J) (u : Kˣ) (hu : ((u : K)) ^ 2 ≠ 1) (c : K) :
    parabolicGradedDet (K := K) J d ⟨yUnit τ K j c, yUnit_mem_parabolicLevi hj c⟩ = 1 := by
  have heq : (⟨yUnit τ K j c, yUnit_mem_parabolicLevi hj c⟩ : ↥(parabolicLevi τ K J)) =
      ⟨torusElt τ K j u, torusGroup_le_parabolicLevi J (torusElt_mem_torusGroup j u)⟩ *
        ⟨yUnit τ K j (c / ((((u ^ (-2 : ℤ) : Kˣ) : K)) - 1)),
          yUnit_mem_parabolicLevi hj _⟩ *
        ⟨torusElt τ K j u, torusGroup_le_parabolicLevi J (torusElt_mem_torusGroup j u)⟩⁻¹ *
        ⟨yUnit τ K j (c / ((((u ^ (-2 : ℤ) : Kˣ) : K)) - 1)),
          yUnit_mem_parabolicLevi hj _⟩⁻¹ := by
    refine Subtype.ext ?_
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    exact yUnit_eq_conj_mul_inv u hu c
  rw [heq, map_mul, map_mul, map_mul, map_inv, map_inv]
  exact mul_mul_inv_mul_inv_eq_one _ _

theorem parabolicGradedDet_eq_one_of_mem_leviGenerators {J : Set (Fin τ.rank)} (d : ℤ) (u : Kˣ)
    (hu : ((u : K)) ^ 2 ≠ 1) (l : ModGL τ K)
    (hl : l ∈ Subgroup.closure
      {g | ∃ j ∈ J, ∃ c : K, g = xUnit τ K j c ∨ g = yUnit τ K j c}) :
    parabolicGradedDet (K := K) J d ⟨l, Subgroup.mem_sup_right hl⟩ = 1 := by
  induction hl using Subgroup.closure_induction'' with
  | mem g hgs =>
    obtain ⟨j, hj, c, rfl | rfl⟩ := hgs
    · exact parabolicGradedDet_xUnit_eq_one d hj u hu c
    · exact parabolicGradedDet_yUnit_eq_one d hj u hu c
  | inv_mem g hgs =>
    obtain ⟨j, hj, c, rfl | rfl⟩ := hgs
    · change parabolicGradedDet (K := K) J d
        ((⟨xUnit τ K j c, xUnit_mem_parabolicLevi hj c⟩ : ↥(parabolicLevi τ K J))⁻¹) = 1
      rw [map_inv, parabolicGradedDet_xUnit_eq_one d hj u hu c, inv_one]
    · change parabolicGradedDet (K := K) J d
        ((⟨yUnit τ K j c, yUnit_mem_parabolicLevi hj c⟩ : ↥(parabolicLevi τ K J))⁻¹) = 1
      rw [map_inv, parabolicGradedDet_yUnit_eq_one d hj u hu c, inv_one]
  | one => exact map_one _
  | mul g h hg hh ihg ihh =>
    have h1 : (⟨g * h, Subgroup.mem_sup_right (Subgroup.mul_mem _ hg hh)⟩ :
        ↥(parabolicLevi τ K J)) =
        (⟨g, Subgroup.mem_sup_right hg⟩ : ↥(parabolicLevi τ K J)) *
          ⟨h, Subgroup.mem_sup_right hh⟩ := Subtype.ext rfl
    rw [h1, map_mul, ihg, ihh, mul_one]

end Certificates

end CFSG.LieType.Chevalley

module

public import CFSG.LieType.Chevalley.RootWeightOptimalParabolic
public import CFSG.LieType.Chevalley.ExactNormalFormE

public noncomputable section

namespace CFSG.LieType.Chevalley

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  RootWeight

section Coordinates

variable {τ : Tag} {K : Type} [Field K] (δ : K ≃+* K)
  [RingHomInvPair δ.toRingHom δ.symm.toRingHom] [RingHomInvPair δ.symm.toRingHom δ.toRingHom]

@[expose] def coordSemilinear : RootModule τ K ≃ₛₗ[δ.toRingHom] RootModule τ K where
  toFun x := Finsupp.mapRange δ.toRingHom δ.toRingHom.map_zero x
  invFun x := Finsupp.mapRange δ.symm.toRingHom δ.symm.toRingHom.map_zero x
  map_add' x y := Finsupp.mapRange_add (map_add δ.toRingHom) x y
  map_smul' c x := by
    ext l
    simp
  left_inv x := by
    ext l
    simp
  right_inv x := by
    ext l
    simp

theorem coordSemilinear_apply (x : RootModule τ K) :
    coordSemilinear (τ := τ) δ x = Finsupp.mapRange δ.toRingHom δ.toRingHom.map_zero x := rfl

theorem coordSemilinear_symm_apply (x : RootModule τ K) :
    (coordSemilinear (τ := τ) δ).symm x =
      Finsupp.mapRange δ.symm.toRingHom δ.symm.toRingHom.map_zero x := rfl

theorem semilinearConj_coordSemilinear (A : Module.End K (RootModule τ K)) :
    semilinearConj (coordSemilinear δ) A = entrywise δ.toRingHom A := by
  refine LinearMap.ext fun x => ?_
  rw [semilinearConj_apply, coordSemilinear_apply, coordSemilinear_symm_apply]
  have h := entrywise_apply_mapRange δ.toRingHom A
    (Finsupp.mapRange δ.symm.toRingHom δ.symm.toRingHom.map_zero x)
  rw [← h]
  congr 1
  ext l
  simp

@[expose] def diagSemilinear (a : Fin τ.rank → Kˣ) :
    RootModule τ K ≃ₛₗ[δ.toRingHom] RootModule τ K :=
  (coordSemilinear δ).trans (rootDiagUnit τ a).toLinearEquiv

theorem diagSemilinear_apply (a : Fin τ.rank → Kˣ) (x : RootModule τ K) :
    diagSemilinear δ a x = rootDiag a (coordSemilinear δ x) := rfl

theorem diagSemilinear_symm_apply (a : Fin τ.rank → Kˣ) (x : RootModule τ K) :
    (diagSemilinear δ a).symm x = (coordSemilinear δ).symm (rootDiag a⁻¹ x) := rfl

theorem semilinearConjUnit_diagSemilinear (a : Fin τ.rank → Kˣ) (g : ModGL τ K) :
    semilinearConjUnit (diagSemilinear δ a) g =
      rootDiagUnit τ a * Units.map (entrywiseHom δ.toRingHom) g * (rootDiagUnit τ a)⁻¹ := by
  refine Units.ext (LinearMap.ext fun x => ?_)
  rw [coe_semilinearConjUnit, semilinearConj_apply, diagSemilinear_apply,
    diagSemilinear_symm_apply]
  have h := congrArg (fun A => A (rootDiag a⁻¹ x)) (semilinearConj_coordSemilinear δ
    (g : Module.End K (RootModule τ K)))
  simp only [semilinearConj_apply] at h
  rw [h]
  rfl

theorem rootDiag_mem_supported (a : Fin τ.rank → Kˣ) {S : Set (Label τ)} {x : RootModule τ K}
    (hx : x ∈ Finsupp.supported K K S) : rootDiag a x ∈ Finsupp.supported K K S := by
  rw [Finsupp.supported_eq_span_single] at hx ⊢
  refine Submodule.span_induction (fun y hy => ?_) (by rw [map_zero]; exact Submodule.zero_mem _)
    (fun y z _ _ hy hz => by rw [map_add]; exact Submodule.add_mem _ hy hz)
    (fun c y _ hy => by rw [map_smul]; exact Submodule.smul_mem _ c hy) hx
  obtain ⟨b, hb, rfl⟩ := hy
  rw [rootDiag_single]
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨b, hb, rfl⟩)

theorem coordSemilinear_mem_supported {S : Set (Label τ)} {x : RootModule τ K}
    (hx : x ∈ Finsupp.supported K K S) :
    coordSemilinear δ x ∈ Finsupp.supported K K S := by
  rw [Finsupp.mem_supported] at hx ⊢
  rw [coordSemilinear_apply]
  exact (Finset.coe_subset.2 Finsupp.support_mapRange).trans hx

theorem coordSemilinear_symm_mem_supported {S : Set (Label τ)} {x : RootModule τ K}
    (hx : x ∈ Finsupp.supported K K S) :
    (coordSemilinear δ).symm x ∈ Finsupp.supported K K S := by
  rw [Finsupp.mem_supported] at hx ⊢
  rw [coordSemilinear_symm_apply]
  exact (Finset.coe_subset.2 Finsupp.support_mapRange).trans hx

theorem map_diagSemilinear_supported (a : Fin τ.rank → Kˣ) (S : Set (Label τ)) :
    (Finsupp.supported K K S).map (diagSemilinear δ a).toLinearMap = Finsupp.supported K K S := by
  refine le_antisymm ?_ fun x hx => ⟨(diagSemilinear δ a).symm x, ?_, ?_⟩
  · rintro _ ⟨x, hx, rfl⟩
    exact rootDiag_mem_supported a (coordSemilinear_mem_supported δ hx)
  · rw [SetLike.mem_coe, diagSemilinear_symm_apply]
    exact coordSemilinear_symm_mem_supported δ (rootDiag_mem_supported a⁻¹ hx)
  · exact (diagSemilinear δ a).apply_symm_apply x

end Coordinates

namespace RootWeightDatum

variable {K : Type} [Field K] (D : RootWeightDatum K)

theorem map_diagSemilinear_weightSpace
    (δ : K ≃+* K)
    [RingHomInvPair δ.toRingHom δ.symm.toRingHom] [RingHomInvPair δ.symm.toRingHom δ.toRingHom]
    (a : Fin D.tag.rank → Kˣ) (χ : D.space) :
    (D.weightSpace χ).map (diagSemilinear δ a).toLinearMap = D.weightSpace χ := by
  rw [D.weightSpace_eq_supported]
  exact map_diagSemilinear_supported δ a _

theorem map_diagSemilinear_filtration
    (δ : K ≃+* K)
    [RingHomInvPair δ.toRingHom δ.symm.toRingHom] [RingHomInvPair δ.symm.toRingHom δ.toRingHom]
    (a : Fin D.tag.rank → Kˣ) (l : D.space) (c : ℝ) :
    (D.filtration l c).map (diagSemilinear δ a).toLinearMap = D.filtration l c := by
  simp only [filtration, weightFiltration, Submodule.map_iSup, map_diagSemilinear_weightSpace]

theorem map_map_units_val (a b : ModGL D.tag K) (X : Submodule K (RootModule D.tag K)) :
    (X.map (a : Module.End K (RootModule D.tag K))).map (b : Module.End K (RootModule D.tag K)) =
      X.map ((b * a : ModGL D.tag K) : Module.End K (RootModule D.tag K)) := by
  rw [Units.val_mul, Module.End.mul_eq_comp, Submodule.map_comp]

theorem exists_conj_radical_invariant
    [Finite K] (p : ℕ) [Fact p.Prime] [CharP K p]
    (R : Set (Fin D.rank) → Subgroup (ModGL D.tag K))
    (hR : ∀ J, D.parabolic J ≤ Subgroup.normalizer (R J : Set (ModGL D.tag K)))
    {Q : Subgroup (ModGL D.tag K)} (hQG : Q ≤ D.group) (hQp : IsPGroup p Q) (hQ : Q ≠ ⊥) :
    ∃ g ∈ D.group, ∃ J : Set (Fin D.rank), J ≠ Set.univ ∧
      ∀ c ∈ D.group, ∀ (δ : K ≃+* K) (a : Fin D.tag.rank → Kˣ),
        (∀ x, rootDiagUnit D.tag a * Units.map (entrywiseHom δ.toRingHom) x *
          (rootDiagUnit D.tag a)⁻¹ ∈ D.group ↔ x ∈ D.group) →
        (∀ x ∈ R J, rootDiagUnit D.tag a * Units.map (entrywiseHom δ.toRingHom) x *
          (rootDiagUnit D.tag a)⁻¹ ∈ R J) →
        (∀ x, x ∈ Q ↔ ∃ q ∈ Q, c * (rootDiagUnit D.tag a *
          Units.map (entrywiseHom δ.toRingHom) q * (rootDiagUnit D.tag a)⁻¹) * c⁻¹ = x) →
        ∀ x ∈ R J, c * (rootDiagUnit D.tag a * Units.map (entrywiseHom δ.toRingHom)
          (g * x * g⁻¹) * (rootDiagUnit D.tag a)⁻¹) * c⁻¹ ∈
            (R J).map (MulAut.conj g).toMonoidHom := by
  obtain ⟨M, -, -, -, F, hF, -, hdom, hgood, hcov⟩ :=
    D.root_p_subgroup_optimal_parabolic_containment p Q hQG hQp hQ
  obtain ⟨g, hg, l, hl, hl1, hgl⟩ := hdom
  obtain ⟨hJ, -, -, -, -⟩ := hgood g hg l hl hl1 hgl
  refine ⟨g, hg, D.face l, hJ, fun c hc δ a hβG hβR hβQ x hx => ?_⟩
  have i1 : RingHomInvPair δ.toRingHom δ.symm.toRingHom := RingHomInvPair.of_ringEquiv δ
  have i2 : RingHomInvPair δ.symm.toRingHom δ.toRingHom := RingHomInvPair.of_ringEquiv_symm δ
  set β : ModGL D.tag K → ModGL D.tag K := fun y => rootDiagUnit D.tag a *
    Units.map (entrywiseHom δ.toRingHom) y * (rootDiagUnit D.tag a)⁻¹ with hβ
  set s := diagSemilinear (τ := D.tag) δ a
  have hsβ : ∀ y, semilinearConjUnit s y = β y := semilinearConjUnit_diagSemilinear δ a
  obtain ⟨-, -, hcov'⟩ := hcov δ.toRingHom δ.symm.toRingHom s
    (fun y => by rw [hsβ]; exact hβG y) (LinearIsometryEquiv.refl ℝ D.space) (by simp)
    (fun χ _ => D.map_diagSemilinear_weightSpace δ a χ) c hc Q
    (fun y => by simp only [hsβ]; exact hβQ y)
  have key : ∀ c' : ℝ, (D.filtration l c').map
      ((g⁻¹ * (c * β g) : ModGL D.tag K) : Module.End K (RootModule D.tag K)) =
        D.filtration l c' := by
    intro c'
    set X := D.filtration l c'
    have h1 := hcov' g hg l hl1 hgl c'
    rw [← hF g hg l hl1 hgl c'] at h1
    have hXs : X.map s.toLinearMap = X := D.map_diagSemilinear_filtration δ a l c'
    have hXs' : X.map s.symm.toLinearMap = X := (Submodule.map_symm_eq_iff s).2 hXs
    have h2 : (X.map (g : Module.End K (RootModule D.tag K))).map s.toLinearMap =
        X.map ((β g : ModGL D.tag K) : Module.End K (RootModule D.tag K)) := by
      rw [← hsβ g, coe_semilinearConjUnit, semilinearConj, Submodule.map_comp, Submodule.map_comp,
        hXs']
    rw [h2, D.map_map_units_val] at h1
    rw [← D.map_map_units_val, ← h1, D.map_map_units_val, inv_mul_cancel, Units.val_one,
      Module.End.one_eq_id, Submodule.map_id]
  have hmemG : g⁻¹ * (c * β g) ∈ D.group := mul_mem (inv_mem hg) (mul_mem hc ((hβG g).2 hg))
  have hP : g⁻¹ * (c * β g) ∈ D.parabolic (D.face l) := by
    have hset := D.setOf_stab_eq_map_conj_parabolic hl (one_mem D.group) (F := D.filtration l)
      (fun c' => by rw [Units.val_one, Module.End.one_eq_id, Submodule.map_id])
    have hmem : (g⁻¹ * (c * β g) : ModGL D.tag K) ∈ {x : ModGL D.tag K | x ∈ D.group ∧
        ∀ c' : ℝ, (D.filtration l c').map (x : Module.End K (RootModule D.tag K)) =
          D.filtration l c'} := ⟨hmemG, key⟩
    rw [hset] at hmem
    obtain ⟨y, hy, hyx⟩ := hmem
    have hy' : y = g⁻¹ * (c * β g) := by
      rw [← hyx]
      simp
    rw [← hy']
    exact hy
  have hβmul : ∀ y z, β (y * z) = β y * β z := fun y z => by
    simp only [hβ, map_mul]
    group
  have hβinv : ∀ y, β y⁻¹ = (β y)⁻¹ := fun y => by
    simp only [hβ, map_inv]
    group
  have hconj := (Subgroup.mem_normalizer_iff.1 (hR _ hP) (β x)).1 (hβR x hx)
  refine ⟨g⁻¹ * (c * β g) * β x * (g⁻¹ * (c * β g))⁻¹, hconj, ?_⟩
  simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  change _ = c * β (g * x * g⁻¹) * c⁻¹
  rw [hβmul, hβmul, hβinv]
  group

end RootWeightDatum

section Membership

variable {K : Type} [Field K]

theorem apply_mem_iff_of_map_eq {G : Type*} [Group G] {f : G →* G} (hf : Function.Injective f)
    {H : Subgroup G} (hH : H.map f = H) (x : G) : f x ∈ H ↔ x ∈ H := by
  constructor
  · intro h
    rw [← hH] at h
    obtain ⟨y, hy, hyx⟩ := h
    rwa [← hf hyx]
  · intro h
    rw [← hH]
    exact ⟨x, h, rfl⟩

theorem diag_entrywise_mem_iff {τ : Tag} {H : Subgroup (ModGL τ K)} (δ : K ≃+* K)
    (a : Fin τ.rank → Kˣ) (h1 : H.map (Units.map (entrywiseHom δ.toRingHom)) = H)
    (h2 : H.map (MulAut.conj (rootDiagUnit τ a)).toMonoidHom = H) (x : ModGL τ K) :
    rootDiagUnit τ a * Units.map (entrywiseHom δ.toRingHom) x * (rootDiagUnit τ a)⁻¹ ∈ H ↔
      x ∈ H := by
  set f : MulAut (ModGL τ K) := MulAut.conj (rootDiagUnit τ a) * exactEntrywiseAut τ δ
  have hf : f.toMonoidHom = (MulAut.conj (rootDiagUnit τ a)).toMonoidHom.comp
      (Units.map (entrywiseHom δ.toRingHom)) := MonoidHom.ext fun y => rfl
  have hH : H.map f.toMonoidHom = H := by
    rw [hf, ← Subgroup.map_map, h1, h2]
  exact apply_mem_iff_of_map_eq f.injective hH x

end Membership

end CFSG.LieType.Chevalley

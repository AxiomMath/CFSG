module

public import CFSG.LocalAnalysis.ComponentInitial.SymplecticFlagExtension

public noncomputable section

namespace CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag

open Module Submodule
open LinearMap (BilinForm)

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  {B : LinearMap.BilinForm K V} {r : ℕ}

theorem exists_lagrangian_fixed_of_jointQuadratic (hB : B.IsAlt) (hnd : B.Nondegenerate)
    (hV : finrank K V = 2 * r) (E : Subgroup (TauCeti.BilinForm.isometryGroup B))
    (hE : ∀ a ∈ E, ∀ c ∈ E, ∀ v : V,
      (c : V ≃ₗ[K] V) ((a : V ≃ₗ[K] V) v - v) - ((a : V ≃ₗ[K] V) v - v) = 0) :
    ∃ W : Submodule K V, IsTotallyIsotropic B W ∧ finrank K W = r ∧
      ∀ a ∈ E, ∀ w ∈ W, (a : V ≃ₗ[K] V) w = w := by
  set I : Submodule K V :=
    span K {x : V | ∃ a ∈ E, ∃ v : V, (a : V ≃ₗ[K] V) v - v = x} with hI
  have hIiso : IsTotallyIsotropic B I := by
    rw [hI]
    rintro x hx y hy
    induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨a, ha, v, rfl⟩ := hx
      induction hy using Submodule.span_induction with
      | mem y hy =>
        obtain ⟨c, hc, w, rfl⟩ := hy
        have hiso : ∀ p q : V, B ((c : V ≃ₗ[K] V) p) ((c : V ≃ₗ[K] V) q) = B p q :=
          TauCeti.BilinForm.mem_isometryGroup_iff.1 c.2
        have hsym : ∀ p q : V,
            B p q = B ((c : V ≃ₗ[K] V).symm p) ((c : V ≃ₗ[K] V).symm q) := by
          intro p q
          rw [← hiso ((c : V ≃ₗ[K] V).symm p) ((c : V ≃ₗ[K] V).symm q)]
          simp
        have hfix : (c : V ≃ₗ[K] V) ((a : V ≃ₗ[K] V) v - v) =
            (a : V ≃ₗ[K] V) v - v :=
          sub_eq_zero.mp (hE a ha c hc v)
        have hfix' : (c : V ≃ₗ[K] V).symm ((a : V ≃ₗ[K] V) v - v) =
            (a : V ≃ₗ[K] V) v - v := by
          calc (c : V ≃ₗ[K] V).symm ((a : V ≃ₗ[K] V) v - v)
              = (c : V ≃ₗ[K] V).symm ((c : V ≃ₗ[K] V) ((a : V ≃ₗ[K] V) v - v)) := by
                rw [hfix]
            _ = (a : V ≃ₗ[K] V) v - v := LinearEquiv.symm_apply_apply _ _
        calc B ((a : V ≃ₗ[K] V) v - v) ((c : V ≃ₗ[K] V) w - w)
            = B ((c : V ≃ₗ[K] V).symm ((a : V ≃ₗ[K] V) v - v))
                ((c : V ≃ₗ[K] V).symm ((c : V ≃ₗ[K] V) w - w)) :=
              hsym _ _
          _ = B ((a : V ≃ₗ[K] V) v - v) (w - (c : V ≃ₗ[K] V).symm w) := by
              rw [hfix']
              congr 1
              rw [map_sub]
              rw [LinearEquiv.symm_apply_apply]
          _ = B ((a : V ≃ₗ[K] V) v - v) w -
                B ((a : V ≃ₗ[K] V) v - v) ((c : V ≃ₗ[K] V).symm w) := by
              rw [map_sub]
          _ = B ((a : V ≃ₗ[K] V) v - v) w - B ((a : V ≃ₗ[K] V) v - v) w := by
              rw [hsym ((a : V ≃ₗ[K] V) v - v) w]
              rw [hfix']
          _ = 0 := sub_self _
      | zero => simp
      | add y z _ _ hy hz => rw [map_add, hy, hz, add_zero]
      | smul t y _ hy => rw [map_smul, hy, smul_zero]
    | zero => simp
    | add x z _ _ hx hz => rw [map_add, LinearMap.add_apply, hx, hz, zero_add]
    | smul t x _ hx => rw [map_smul, LinearMap.smul_apply, hx, smul_zero]
  obtain ⟨b, hb, hbI⟩ := exists_completeIsotropicFlag hB hnd hV hIiso
  let W : Submodule K V := span K (Set.range (b ∘ Sum.inl))
  have hW_eq : W = span K (b '' (Sum.inl '' (Set.univ : Set (Fin r)))) := by
    unfold W
    congr 1
    ext x
    constructor
    · rintro ⟨i, rfl⟩
      exact ⟨Sum.inl i, ⟨i, trivial, rfl⟩, rfl⟩
    · rintro ⟨y, ⟨i, -, rfl⟩, rfl⟩
      exact ⟨i, rfl⟩
  have hWiso : IsTotallyIsotropic B W := by
    rw [hW_eq]
    exact hb.isTotallyIsotropic Set.univ
  have hWdim : finrank K W = r := by
    rw [hW_eq]
    have hset : (Set.univ : Set (Fin r)) = {j : Fin r | (j : ℕ) < r} := by
      ext j
      simp
    rw [hset]
    exact finrank_span_inl_image b le_rfl
  have hIW : I ≤ W := by
    rw [hbI]
    apply span_mono
    rintro x ⟨i, hi, rfl⟩
    obtain ⟨j, -, rfl⟩ := hi
    exact ⟨j, rfl⟩
  refine ⟨W, hWiso, hWdim, ?_⟩
  intro a ha w hw
  have hfixW : ∀ a ∈ E, ∀ w ∈ W, (a : V ≃ₗ[K] V) w = w := by
    intro a ha w hw
    have hgen : ∀ v : V,
        ((((⟨a, ha⟩ : E)⁻¹ : E) : V ≃ₗ[K] V)) v - v ∈ I := by
      intro v
      rw [hI]
      exact Submodule.subset_span ⟨((⟨a, ha⟩ : E)⁻¹ : E), E.inv_mem ha, v, rfl⟩
    have hzero : ∀ v : V, B ((a : V ≃ₗ[K] V) w - w) v = 0 := by
      intro v
      have hgenv := hgen v
      have hcalc : B ((a : V ≃ₗ[K] V) w - w) v =
          B w ((((⟨a, ha⟩ : E)⁻¹ : E) : V ≃ₗ[K] V) v - v) := by
        rw [map_sub, LinearMap.sub_apply, map_sub]
        congr 1
        conv_lhs => rw [← LinearEquiv.apply_symm_apply (a : V ≃ₗ[K] V) v]
        rw [TauCeti.BilinForm.mem_isometryGroup_iff.1 a.2]
        rfl
      rw [hcalc]
      exact hWiso w hw _ (hIW hgenv)
    exact sub_eq_zero.mp (hnd.1 _ hzero)
  exact hfixW a ha w hw

theorem exists_isometry_map_eq_of_lagrangian (hB : B.IsAlt) (hnd : B.Nondegenerate)
    (hV : finrank K V = 2 * r) {W W' : Submodule K V}
    (hW : IsTotallyIsotropic B W) (hd : finrank K W = r)
    (hW' : IsTotallyIsotropic B W') (hd' : finrank K W' = r) :
    ∃ g : TauCeti.BilinForm.isometryGroup B,
      W.map ((g : V ≃ₗ[K] V) : V →ₗ[K] V) = W' := by
  obtain ⟨b, hb, hbW⟩ := exists_completeIsotropicFlag hB hnd hV hW
  obtain ⟨b', hb', hbW'⟩ := exists_completeIsotropicFlag hB hnd hV hW'
  have hWb : W = span K (Set.range (b ∘ Sum.inl)) := by
    rw [hbW, hd]
    have hset : {j : Fin r | (j : ℕ) < r} = Set.univ :=
      Set.eq_univ_of_forall fun j => j.2
    rw [hset, Set.image_univ, Set.range_comp]
  have hWb' : W' = span K (Set.range (b' ∘ Sum.inl)) := by
    rw [hbW', hd']
    have hset : {j : Fin r | (j : ℕ) < r} = Set.univ :=
      Set.eq_univ_of_forall fun j => j.2
    rw [hset, Set.image_univ, Set.range_comp]
  set g := b.isometryEquivOfToMatrixEq b' (hb.trans hb'.symm)
  have hgW : W.map ((g.toLinearEquiv : V ≃ₗ[K] V) : V →ₗ[K] V) = W' := by
    rw [hWb, hWb', Submodule.map_span, ← Set.range_comp]
    congr 2
    funext i
    exact b.isometryEquivOfToMatrixEq_apply_basis b' (hb.trans hb'.symm) (Sum.inl i)
  exact ⟨⟨g.toLinearEquiv, TauCeti.BilinForm.mem_isometryGroup_iff.mpr fun x y =>
    g.map_app y x⟩, hgW⟩

end CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag

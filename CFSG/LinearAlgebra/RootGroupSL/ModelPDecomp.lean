module

public import CFSG.LinearAlgebra.RootGroupSL.ModelBasic

public section

namespace CFSG.LinearAlgebra.RootGroupSL

open CFSG.Open

variable {k E VJ V₀ : Type} [Field k] [Field E] [Algebra k E]
  [AddCommGroup VJ] [Module k VJ] [Module E VJ] [IsScalarTower k E VJ]
  [AddCommGroup V₀] [Module k V₀]
  [Module.Finite k E] [Module.Finite E VJ] [Module.Finite k VJ] [Module.Finite k V₀]



@[expose] noncomputable def modelBOfP1 (g : SpecialLinearGroup k (VJ × V₀))
    (hg : g ∈ modelP1 k VJ V₀) : SpecialLinearGroup k VJ := by
  let B0 : VJ →ₗ[k] VJ :=
    (LinearMap.fst k VJ V₀).comp
      ((SpecialLinearGroup.toLinearEquiv g).toLinearMap.comp (LinearMap.inl k VJ V₀))
  have hB0_inj : Function.Injective B0 := by
    intro v v' hv
    have hker : B0 (v - v') = 0 := by rw [map_sub, hv, sub_self]
    have h1 : g (v - v', 0) = (0, 0) := Prod.ext hker (hg.1 (v - v'))
    have h2 : g (0, 0) = (0, 0) := map_zero (SpecialLinearGroup.toLinearEquiv g)
    have h3 : (v - v', (0 : V₀)) = ((0 : VJ), (0 : V₀)) :=
      (SpecialLinearGroup.toLinearEquiv g).injective (by
        simpa only [SpecialLinearGroup.toLinearEquiv_apply] using h1.trans h2.symm)
    exact sub_eq_zero.mp (congrArg Prod.fst h3)
  let B : VJ ≃ₗ[k] VJ := LinearEquiv.ofInjectiveEndo B0 hB0_inj
  refine ⟨B, ?_⟩
  let φ : V₀ →ₗ[k] VJ :=
    (LinearMap.fst k VJ V₀).comp
      ((SpecialLinearGroup.toLinearEquiv g).toLinearMap.comp (LinearMap.inr k VJ V₀))
  have hgv : ∀ v : VJ, g (v, 0) = (B0 v, 0) := fun v => Prod.ext rfl (hg.1 v)
  have hg0 : ∀ w : V₀, g (0, w) = (φ w, w) := fun w => Prod.ext rfl (hg.2 w)
  have hdecomp' : ∀ (v : VJ) (w : V₀), g (v, w) = (B v + φ w, w) := by
    intro v w
    have hsplit : (v, w) = (v, 0) + (0, w) := by ext <;> simp
    calc g (v, w) = g ((v, 0) + (0, w)) := by rw [hsplit]
      _ = g (v, 0) + g (0, w) :=
          map_add (SpecialLinearGroup.toLinearEquiv g) (v, 0) (0, w)
      _ = (B0 v, 0) + (φ w, w) := by rw [hgv v, hg0 w]
      _ = (B v + φ w, w) := by
          refine Prod.ext ?_ (by simp)
          simp [B, LinearEquiv.coe_ofInjectiveEndo]
  have hdetg : LinearEquiv.det (SpecialLinearGroup.toLinearEquiv g) = 1 := by
    rw [SpecialLinearGroup.toLinearEquiv_eq_coe]
    exact SpecialLinearGroup.det_coe g
  have hphidet : LinearEquiv.det (SpecialLinearGroup.toLinearEquiv (modelA1Elt φ)) = 1 := by
    rw [SpecialLinearGroup.toLinearEquiv_eq_coe]
    exact SpecialLinearGroup.det_coe (modelA1Elt φ)
  have heq : SpecialLinearGroup.toLinearEquiv g =
      (modelA1Elt φ).toLinearEquiv *
        (LinearEquiv.prodCongr B (LinearEquiv.refl k V₀)) := by
    apply LinearEquiv.ext
    intro p
    obtain ⟨v, w⟩ := p
    change (SpecialLinearGroup.toLinearEquiv g) (v, w) =
      (SpecialLinearGroup.toLinearEquiv (modelA1Elt φ))
        ((LinearEquiv.prodCongr B (LinearEquiv.refl k V₀)) (v, w))
    rw [LinearEquiv.prodCongr_apply, SpecialLinearGroup.toLinearEquiv_apply,
      SpecialLinearGroup.toLinearEquiv_apply]
    change g (v, w) = (B v + φ w, w)
    exact hdecomp' v w
  have hdetprod : LinearEquiv.det
      (LinearEquiv.prodCongr B (LinearEquiv.refl k V₀)) = LinearEquiv.det B := by
    apply Units.ext
    rw [LinearEquiv.coe_det, LinearEquiv.coe_prodCongr, LinearMap.det_prodMap]
    simp
  have h := congrArg LinearEquiv.det heq
  rw [map_mul, hdetg, hphidet, one_mul, hdetprod] at h
  exact h.symm

lemma modelBOfP1_apply (g : SpecialLinearGroup k (VJ × V₀))
    (hg : g ∈ modelP1 k VJ V₀) (v : VJ) :
    (modelBOfP1 g hg) v = (g (v, 0)).1 :=
  rfl

lemma exists_decomp_modelP1 (g : SpecialLinearGroup k (VJ × V₀))
    (hg : g ∈ modelP1 k VJ V₀) :
    ∃ φ : V₀ →ₗ[k] VJ, modelA1Elt φ * blockSLk k V₀ (modelBOfP1 g hg) = g := by
  let φ : V₀ →ₗ[k] VJ :=
    (LinearMap.fst k VJ V₀).comp
      ((SpecialLinearGroup.toLinearEquiv g).toLinearMap.comp (LinearMap.inr k VJ V₀))
  refine ⟨φ, ?_⟩
  apply SpecialLinearGroup.ext
  intro p
  obtain ⟨v, w⟩ := p
  change modelA1Elt φ (blockSLk k V₀ (modelBOfP1 g hg) (v, w)) = g (v, w)
  rw [blockSLk_apply, modelA1Elt_apply]
  have hdecomp : g (v, w) = ((modelBOfP1 g hg) v + φ w, w) := by
    have hsplit : (v, w) = (v, 0) + (0, w) := by ext <;> simp
    calc g (v, w) = g ((v, 0) + (0, w)) := by rw [hsplit]
      _ = g (v, 0) + g (0, w) :=
          map_add (SpecialLinearGroup.toLinearEquiv g) (v, 0) (0, w)
      _ = ((modelBOfP1 g hg) v, 0) + (φ w, w) := by
          rw [show g (v, 0) = ((modelBOfP1 g hg) v, 0) from
                Prod.ext (modelBOfP1_apply g hg v).symm (hg.1 v),
              show g (0, w) = (φ w, w) from Prod.ext rfl (hg.2 w)]
      _ = ((modelBOfP1 g hg) v + φ w, w) := by
          refine Prod.ext ?_ (by simp)
          rfl
  rw [hdecomp]

@[expose] noncomputable def modelBOfP2 (g : SpecialLinearGroup k (VJ × V₀))
    (hg : g ∈ modelP2 k VJ V₀) : SpecialLinearGroup k VJ := by
  let B0 : VJ →ₗ[k] VJ :=
    (LinearMap.fst k VJ V₀).comp
      ((SpecialLinearGroup.toLinearEquiv g).toLinearMap.comp (LinearMap.inl k VJ V₀))
  let ψ0 : VJ →ₗ[k] V₀ :=
    (LinearMap.snd k VJ V₀).comp
      ((SpecialLinearGroup.toLinearEquiv g).toLinearMap.comp (LinearMap.inl k VJ V₀))
  have hB0_inj : Function.Injective B0 := by
    intro v v' hv
    have hker : B0 (v - v') = 0 := by rw [map_sub, hv, sub_self]
    have h1 : g (v - v', 0) = (0, ψ0 (v - v')) := Prod.ext hker rfl
    have h2 : g (0, ψ0 (v - v')) = (0, ψ0 (v - v')) := hg _
    have h3 : (v - v', (0 : V₀)) = ((0 : VJ), ψ0 (v - v')) :=
      (SpecialLinearGroup.toLinearEquiv g).injective (by
        simpa only [SpecialLinearGroup.toLinearEquiv_apply] using h1.trans h2.symm)
    exact sub_eq_zero.mp (congrArg Prod.fst h3)
  let B : VJ ≃ₗ[k] VJ := LinearEquiv.ofInjectiveEndo B0 hB0_inj
  refine ⟨B, ?_⟩
  let ψ : VJ →ₗ[k] V₀ := ψ0.comp B.symm.toLinearMap
  have hgv : ∀ v : VJ, g (v, 0) = (B0 v, ψ0 v) := fun v => Prod.ext rfl rfl
  have hdecomp' : ∀ (v : VJ) (w : V₀), g (v, w) = (B v, ψ0 v + w) := by
    intro v w
    have hsplit : (v, w) = (v, 0) + (0, w) := by ext <;> simp
    calc g (v, w) = g ((v, 0) + (0, w)) := by rw [hsplit]
      _ = g (v, 0) + g (0, w) :=
          map_add (SpecialLinearGroup.toLinearEquiv g) (v, 0) (0, w)
      _ = (B0 v, ψ0 v) + (0, w) := by rw [hgv v, hg w]
      _ = (B v, ψ0 v + w) := by
          refine Prod.ext ?_ rfl
          simp [B, LinearEquiv.coe_ofInjectiveEndo]
  have hpsi : ∀ v : VJ, ψ (B v) = ψ0 v := by
    intro v
    simp [ψ]
  have hdetg : LinearEquiv.det (SpecialLinearGroup.toLinearEquiv g) = 1 := by
    rw [SpecialLinearGroup.toLinearEquiv_eq_coe]
    exact SpecialLinearGroup.det_coe g
  have hphidet : LinearEquiv.det (SpecialLinearGroup.toLinearEquiv (modelA2Elt ψ)) = 1 := by
    rw [SpecialLinearGroup.toLinearEquiv_eq_coe]
    exact SpecialLinearGroup.det_coe (modelA2Elt ψ)
  have heq : SpecialLinearGroup.toLinearEquiv g =
      (modelA2Elt ψ).toLinearEquiv *
        (LinearEquiv.prodCongr B (LinearEquiv.refl k V₀)) := by
    apply LinearEquiv.ext
    intro p
    obtain ⟨v, w⟩ := p
    change (SpecialLinearGroup.toLinearEquiv g) (v, w) =
      (SpecialLinearGroup.toLinearEquiv (modelA2Elt ψ))
        ((LinearEquiv.prodCongr B (LinearEquiv.refl k V₀)) (v, w))
    rw [LinearEquiv.prodCongr_apply, SpecialLinearGroup.toLinearEquiv_apply,
      SpecialLinearGroup.toLinearEquiv_apply]
    change g (v, w) = (B v, w + ψ (B v))
    rw [hdecomp' v w]
    refine Prod.ext rfl ?_
    calc ψ0 v + w = w + ψ0 v := add_comm _ _
      _ = w + ψ (B v) := congrArg (fun x => w + x) (hpsi v).symm
  have hdetprod : LinearEquiv.det
      (LinearEquiv.prodCongr B (LinearEquiv.refl k V₀)) = LinearEquiv.det B := by
    apply Units.ext
    rw [LinearEquiv.coe_det, LinearEquiv.coe_prodCongr, LinearMap.det_prodMap]
    simp
  have h := congrArg LinearEquiv.det heq
  rw [map_mul, hdetg, hphidet, one_mul, hdetprod] at h
  exact h.symm

lemma modelBOfP2_apply (g : SpecialLinearGroup k (VJ × V₀))
    (hg : g ∈ modelP2 k VJ V₀) (v : VJ) :
    (modelBOfP2 g hg) v = (g (v, 0)).1 :=
  rfl

lemma exists_decomp_modelP2 (g : SpecialLinearGroup k (VJ × V₀))
    (hg : g ∈ modelP2 k VJ V₀) :
    ∃ ψ : VJ →ₗ[k] V₀, modelA2Elt ψ * blockSLk k V₀ (modelBOfP2 g hg) = g := by
  let ψ0 : VJ →ₗ[k] V₀ :=
    (LinearMap.snd k VJ V₀).comp
      ((SpecialLinearGroup.toLinearEquiv g).toLinearMap.comp (LinearMap.inl k VJ V₀))
  let ψ : VJ →ₗ[k] V₀ :=
    ψ0.comp (SpecialLinearGroup.toLinearEquiv (modelBOfP2 g hg)).symm.toLinearMap
  refine ⟨ψ, ?_⟩
  apply SpecialLinearGroup.ext
  intro p
  obtain ⟨v, w⟩ := p
  change modelA2Elt ψ (blockSLk k V₀ (modelBOfP2 g hg) (v, w)) = g (v, w)
  rw [blockSLk_apply, modelA2Elt_apply]
  have hdecomp : g (v, w) = ((modelBOfP2 g hg) v, ψ0 v + w) := by
    have hsplit : (v, w) = (v, 0) + (0, w) := by ext <;> simp
    calc g (v, w) = g ((v, 0) + (0, w)) := by rw [hsplit]
      _ = g (v, 0) + g (0, w) :=
          map_add (SpecialLinearGroup.toLinearEquiv g) (v, 0) (0, w)
      _ = ((modelBOfP2 g hg) v, ψ0 v) + (0, w) := by
          rw [show g (v, 0) = ((modelBOfP2 g hg) v, ψ0 v) from
                Prod.ext (modelBOfP2_apply g hg v).symm rfl,
              hg w]
      _ = ((modelBOfP2 g hg) v, ψ0 v + w) := by
          refine Prod.ext ?_ rfl
          simp
  have hpsi : ψ ((modelBOfP2 g hg) v) = ψ0 v := by simp [ψ]
  rw [hdecomp]
  refine Prod.ext rfl ?_
  calc w + ψ (modelBOfP2 g hg v) = w + ψ0 v := by rw [hpsi]
    _ = ψ0 v + w := add_comm _ _

private lemma snd_fixed_fst_apply {g : SpecialLinearGroup k (VJ × V₀)}
    (hg : ∀ w, g (0, w) = (0, w)) (p : VJ × V₀) :
    (g p).1 = (g (p.1, 0)).1 := by
  obtain ⟨x, y⟩ := p
  show (g (x, y)).1 = (g (x, 0)).1
  have hadd : (g ((x, 0) + (0, y))).1 = (g (x, 0) + g (0, y)).1 :=
    congrArg Prod.fst (map_add (SpecialLinearGroup.toLinearEquiv g) (x, 0) (0, y))
  have hsplit : (x, y) = (x, 0) + (0, y) := by ext <;> simp
  rw [hsplit, hadd, hg y]
  simp

theorem modelA1_sup_modelK1 : modelA1 k VJ V₀ ⊔ modelK1 k VJ V₀ = modelP1 k VJ V₀ := by
  apply le_antisymm
  · exact sup_le modelA1_le_modelP1 modelK1_le_modelP1
  · intro g hg
    obtain ⟨φ, hφ⟩ := exists_decomp_modelP1 g hg
    rw [← hφ]
    exact Subgroup.mul_mem_sup ((mem_modelA1_iff _).mpr ⟨φ, rfl⟩)
      (by rw [modelK1_eq_range]; exact MonoidHom.mem_range.mpr ⟨_, rfl⟩)

theorem modelA2_sup_modelK1 : modelA2 k VJ V₀ ⊔ modelK1 k VJ V₀ = modelP2 k VJ V₀ := by
  apply le_antisymm
  · exact sup_le modelA2_le_modelP2 modelK1_le_modelP2
  · intro g hg
    obtain ⟨ψ, hψ⟩ := exists_decomp_modelP2 g hg
    rw [← hψ]
    exact Subgroup.mul_mem_sup ((mem_modelA2_iff _).mpr ⟨ψ, rfl⟩)
      (by rw [modelK1_eq_range]; exact MonoidHom.mem_range.mpr ⟨_, rfl⟩)

private noncomputable def resP1Fun (g : modelP1 k VJ V₀) : SpecialLinearGroup k VJ :=
  modelBOfP1 (g : SpecialLinearGroup k (VJ × V₀)) g.2

private lemma resP1Fun_apply (g : modelP1 k VJ V₀) (v : VJ) :
    (resP1Fun g) v = ((g : SpecialLinearGroup k (VJ × V₀)) (v, 0)).1 :=
  modelBOfP1_apply _ _ v

noncomputable def resP1 : modelP1 k VJ V₀ →* SpecialLinearGroup k VJ :=
  MonoidHom.mk' resP1Fun (by
    intro g h
    apply SpecialLinearGroup.ext
    intro v
    have hh : (h : SpecialLinearGroup k (VJ × V₀)) (v, 0) =
        (((h : SpecialLinearGroup k (VJ × V₀)) (v, 0)).1, 0) := by
      rw [← Prod.mk.eta (p := (h : SpecialLinearGroup k (VJ × V₀)) (v, 0)), h.2.1 v]
    calc (resP1Fun (g * h)) v
        = (((g * h : modelP1 k VJ V₀) : SpecialLinearGroup k (VJ × V₀)) (v, 0)).1 :=
          resP1Fun_apply (g * h) v
      _ = ((g : SpecialLinearGroup k (VJ × V₀))
            ((h : SpecialLinearGroup k (VJ × V₀)) (v, 0))).1 := rfl
      _ = ((g : SpecialLinearGroup k (VJ × V₀))
            (((h : SpecialLinearGroup k (VJ × V₀)) (v, 0)).1, 0)).1 := by rw [hh]
      _ = (resP1Fun g) (((h : SpecialLinearGroup k (VJ × V₀)) (v, 0)).1) :=
          (resP1Fun_apply g _).symm
      _ = (resP1Fun g) ((resP1Fun h) v) := by rw [resP1Fun_apply h v]
      _ = (resP1Fun g * resP1Fun h) v := rfl)

lemma resP1_apply (g : modelP1 k VJ V₀) (v : VJ) :
    (resP1 g) v = ((g : SpecialLinearGroup k (VJ × V₀)) (v, 0)).1 :=
  resP1Fun_apply g v

lemma resP1_surjective :
    Function.Surjective (resP1 (k := k) (VJ := VJ) (V₀ := V₀)) := by
  intro B
  refine ⟨⟨blockSLk k V₀ B, modelK1_le_modelP1 ?_⟩, ?_⟩
  · rw [modelK1_eq_range]
    exact MonoidHom.mem_range.mpr ⟨B, rfl⟩
  · apply SpecialLinearGroup.ext
    intro v
    rw [resP1_apply, blockSLk_apply]

lemma resP1_ker : resP1.ker = (modelA1 k VJ V₀).subgroupOf (modelP1 k VJ V₀) := by
  apply Subgroup.ext
  intro g
  rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
  constructor
  · intro h
    refine ⟨fun v => ?_, g.2.2⟩
    have hv : (resP1 g) v = v := by rw [h]; rfl
    rw [resP1_apply] at hv
    exact Prod.ext hv (g.2.1 v)
  · intro h
    apply SpecialLinearGroup.ext
    intro v
    rw [resP1_apply, h.1 v]
    rfl


private noncomputable def resP2Fun (g : modelP2 k VJ V₀) : SpecialLinearGroup k VJ :=
  modelBOfP2 (g : SpecialLinearGroup k (VJ × V₀)) g.2

private lemma resP2Fun_apply (g : modelP2 k VJ V₀) (v : VJ) :
    (resP2Fun g) v = ((g : SpecialLinearGroup k (VJ × V₀)) (v, 0)).1 :=
  modelBOfP2_apply _ _ v

noncomputable def resP2 : modelP2 k VJ V₀ →* SpecialLinearGroup k VJ :=
  MonoidHom.mk' resP2Fun (by
    intro g h
    apply SpecialLinearGroup.ext
    intro v
    calc (resP2Fun (g * h)) v
        = (((g * h : modelP2 k VJ V₀) : SpecialLinearGroup k (VJ × V₀)) (v, 0)).1 :=
          resP2Fun_apply (g * h) v
      _ = ((g : SpecialLinearGroup k (VJ × V₀))
            ((h : SpecialLinearGroup k (VJ × V₀)) (v, 0))).1 := rfl
      _ = ((g : SpecialLinearGroup k (VJ × V₀))
            (((h : SpecialLinearGroup k (VJ × V₀)) (v, 0)).1, 0)).1 :=
          snd_fixed_fst_apply g.2 _
      _ = (resP2Fun g) (((h : SpecialLinearGroup k (VJ × V₀)) (v, 0)).1) :=
          (resP2Fun_apply g _).symm
      _ = (resP2Fun g) ((resP2Fun h) v) := by rw [resP2Fun_apply h v]
      _ = (resP2Fun g * resP2Fun h) v := rfl)

lemma resP2_apply (g : modelP2 k VJ V₀) (v : VJ) :
    (resP2 g) v = ((g : SpecialLinearGroup k (VJ × V₀)) (v, 0)).1 :=
  resP2Fun_apply g v

lemma resP2_surjective :
    Function.Surjective (resP2 (k := k) (VJ := VJ) (V₀ := V₀)) := by
  intro B
  refine ⟨⟨blockSLk k V₀ B, modelK1_le_modelP2 ?_⟩, ?_⟩
  · rw [modelK1_eq_range]
    exact MonoidHom.mem_range.mpr ⟨B, rfl⟩
  · apply SpecialLinearGroup.ext
    intro v
    rw [resP2_apply, blockSLk_apply]

lemma resP2_ker : resP2.ker = (modelA2 k VJ V₀).subgroupOf (modelP2 k VJ V₀) := by
  apply Subgroup.ext
  intro g
  rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
  constructor
  · intro h
    refine ⟨g.2, fun v => ?_⟩
    have hv : (resP2 g) v = v := by rw [h]; rfl
    rwa [resP2_apply] at hv
  · intro h
    apply SpecialLinearGroup.ext
    intro v
    rw [resP2_apply, h.2 v]
    rfl

end CFSG.LinearAlgebra.RootGroupSL

module

public import CFSG.LinearAlgebra.RootGroupSL.DatumGroups
public import CFSG.Open.LocalVocabulary

public section

namespace CFSG.LinearAlgebra.RootGroupSL

private lemma sl_mul_apply {k V : Type*} [Field k] [AddCommGroup V] [Module k V]
    (g h : SpecialLinearGroup k V) (x : V) : (g * h) x = g (h x) := rfl

private lemma sl_inv_apply_apply {k V : Type*} [Field k] [AddCommGroup V] [Module k V]
    (g : SpecialLinearGroup k V) (x : V) : g⁻¹ (g x) = x := by
  have h : g⁻¹ * g = 1 := inv_mul_cancel g
  calc g⁻¹ (g x) = (g⁻¹ * g) x := rfl
    _ = (1 : SpecialLinearGroup k V) x := by rw [h]
    _ = x := rfl

private lemma sl_apply_inv_apply {k V : Type*} [Field k] [AddCommGroup V] [Module k V]
    (g : SpecialLinearGroup k V) (x : V) : g (g⁻¹ x) = x := by
  have h : g * g⁻¹ = 1 := mul_inv_cancel g
  calc g (g⁻¹ x) = (g * g⁻¹) x := rfl
    _ = (1 : SpecialLinearGroup k V) x := by rw [h]
    _ = x := rfl

private lemma sl_map_add {k V : Type*} [Field k] [AddCommGroup V] [Module k V]
    (g : SpecialLinearGroup k V) (a b : V) : g (a + b) = g a + g b :=
  map_add (g : V ≃ₗ[k] V) a b

private lemma apply_prod_eq {k VJ V₀ : Type*} [Field k] [AddCommGroup VJ] [Module k VJ]
    [AddCommGroup V₀] [Module k V₀] (g : SpecialLinearGroup k (VJ × V₀)) (a : VJ) (b : V₀) :
    g (a, b) = g (a, 0) + g (0, b) := by
  have h : (a, b) = (a, 0) + (0, b) := by ext <;> simp
  rw [h, sl_map_add]

private lemma det_one_add_of_sq_zero {k M : Type*} [Field k] [AddCommGroup M] [Module k M]
    [Module.Finite k M] (N : M →ₗ[k] M) (hN : N * N = 0) :
    LinearMap.det (1 + N) = 1 := by
  have hnil : IsNilpotent (-N) := by
    refine ⟨2, ?_⟩
    rw [pow_two, neg_mul_neg, hN]
  have hchar : (-N).charpoly = Polynomial.X ^ Module.finrank k M :=
    IsNilpotent.charpoly_eq_X_pow_finrank hnil
  have h := LinearMap.eval_charpoly (-N) (1 : k)
  rw [hchar] at h
  simp only [Polynomial.eval_pow, Polynomial.eval_X, one_pow, map_one, sub_neg_eq_add] at h
  exact h.symm

variable {k E VJ V₀ : Type} [Field k] [Field E] [Algebra k E]
  [AddCommGroup VJ] [Module k VJ] [Module E VJ] [IsScalarTower k E VJ]
  [AddCommGroup V₀] [Module k V₀]

variable (k) in
@[expose] def restrictSL [Module.Finite k E] [Module.Finite E VJ] [Module.Finite k VJ] :
    SpecialLinearGroup E VJ →* SpecialLinearGroup k VJ where
  toFun B := ⟨(B : VJ ≃ₗ[E] VJ).restrictScalars k, by
    apply Units.ext
    rw [LinearEquiv.coe_det, Units.val_one]
    have hB : LinearMap.det ((B : VJ ≃ₗ[E] VJ) : VJ →ₗ[E] VJ) = 1 := by
      rw [← LinearEquiv.coe_det, B.prop, Units.val_one]
    have hcast : LinearMap.det
        (((B : VJ ≃ₗ[E] VJ).restrictScalars k : VJ ≃ₗ[k] VJ) : VJ →ₗ[k] VJ) =
        LinearMap.det (((B : VJ ≃ₗ[E] VJ) : VJ →ₗ[E] VJ).restrictScalars k) := rfl
    rw [hcast, LinearMap.det_restrictScalars, hB]
    exact map_one (Algebra.norm k)⟩
  map_one' := by
    ext v
    rfl
  map_mul' B B' := by
    ext v
    rfl

variable (k) in
@[expose] def blockSLk (V₀ : Type) [AddCommGroup V₀] [Module k V₀] [Module.Finite k VJ]
    [Module.Finite k V₀] : SpecialLinearGroup k VJ →* SpecialLinearGroup k (VJ × V₀) where
  toFun B := ⟨LinearEquiv.prodCongr (B : VJ ≃ₗ[k] VJ) (LinearEquiv.refl k V₀), by
    have hB : LinearMap.det ((B : VJ ≃ₗ[k] VJ) : VJ →ₗ[k] VJ) = 1 := by
      rw [← LinearEquiv.coe_det, B.prop, Units.val_one]
    have hV : LinearMap.det
        ((LinearEquiv.refl k V₀ : V₀ ≃ₗ[k] V₀) : V₀ →ₗ[k] V₀) = 1 := by
      rw [← LinearEquiv.coe_det]
      simp
    apply Units.ext
    rw [LinearEquiv.coe_det, Units.val_one, LinearEquiv.coe_prodCongr,
      LinearMap.det_prodMap, hB, hV, one_mul]⟩
  map_one' := by
    ext p <;> simp
  map_mul' B B' := by
    ext p <;> simp

variable (k) in
@[expose] def blockSLE (V₀ : Type) [AddCommGroup V₀] [Module k V₀] [Module.Finite k E]
    [Module.Finite E VJ] [Module.Finite k VJ] [Module.Finite k V₀] :
    SpecialLinearGroup E VJ →* SpecialLinearGroup k (VJ × V₀) :=
  (blockSLk (VJ := VJ) k V₀).comp (restrictSL (E := E) (VJ := VJ) k)

variable [Module.Finite k E] [Module.Finite E VJ] [Module.Finite k VJ] [Module.Finite k V₀]

variable (k E VJ V₀) in
@[expose] def modelJ : Subgroup (SpecialLinearGroup k (VJ × V₀)) :=
  (blockSLE (E := E) (VJ := VJ) k V₀).range

variable (k VJ V₀) in
@[expose] def modelK1 : Subgroup (SpecialLinearGroup k (VJ × V₀)) where
  carrier := {g | (∀ v, (g (v, 0)).2 = 0) ∧ ∀ w, g (0, w) = (0, w)}
  mul_mem' := by
    rintro g h ⟨hg1, hg2⟩ ⟨hh1, hh2⟩
    refine ⟨fun v => ?_, fun w => ?_⟩
    · have hh : h (v, 0) = ((h (v, 0)).1, 0) := by
        rw [← Prod.mk.eta (p := h (v, 0)), hh1 v]
      rw [sl_mul_apply, hh, hg1]
    · rw [sl_mul_apply, hh2 w, hg2 w]
  one_mem' := ⟨fun v => rfl, fun w => rfl⟩
  inv_mem' := by
    rintro g ⟨hg1, hg2⟩
    refine ⟨fun v => ?_, fun w => ?_⟩
    · have hx := sl_apply_inv_apply g (v, 0)
      have hdec : g (g⁻¹ (v, 0)) =
          g ((g⁻¹ (v, 0)).1, 0) + (0, (g⁻¹ (v, 0)).2) := by
        calc g (g⁻¹ (v, 0))
            = g ((g⁻¹ (v, 0)).1, (g⁻¹ (v, 0)).2) := by rw [Prod.mk.eta]
            _ = g ((g⁻¹ (v, 0)).1, 0) + g (0, (g⁻¹ (v, 0)).2) :=
                apply_prod_eq g _ _
            _ = g ((g⁻¹ (v, 0)).1, 0) + (0, (g⁻¹ (v, 0)).2) := by
                rw [hg2 (g⁻¹ (v, 0)).2]
      rw [hdec] at hx
      have h2 := congrArg Prod.snd hx
      simpa [hg1] using h2
    · have h := sl_inv_apply_apply g (0, w)
      rwa [hg2 w] at h

variable (k VJ V₀) in
@[expose] def modelA1 : Subgroup (SpecialLinearGroup k (VJ × V₀)) where
  carrier := {g | (∀ v, g (v, 0) = (v, 0)) ∧ ∀ w, (g (0, w)).2 = w}
  mul_mem' := by
    rintro g h ⟨hg1, hg2⟩ ⟨hh1, hh2⟩
    refine ⟨fun v => ?_, fun w => ?_⟩
    · rw [sl_mul_apply, hh1 v, hg1 v]
    · have hh : h (0, w) = ((h (0, w)).1, w) := by
        rw [← Prod.mk.eta (p := h (0, w)), hh2 w]
      rw [sl_mul_apply, hh, apply_prod_eq g (h (0, w)).1 w]
      simp [hg1, hg2]
  one_mem' := ⟨fun v => rfl, fun w => rfl⟩
  inv_mem' := by
    rintro g ⟨hg1, hg2⟩
    refine ⟨fun v => ?_, fun w => ?_⟩
    · have h := sl_inv_apply_apply g (v, 0)
      rwa [hg1 v] at h
    · have hx := sl_apply_inv_apply g (0, w)
      have hdec : g (g⁻¹ (0, w)) =
          ((g⁻¹ (0, w)).1, 0) + g (0, (g⁻¹ (0, w)).2) := by
        calc g (g⁻¹ (0, w))
            = g ((g⁻¹ (0, w)).1, (g⁻¹ (0, w)).2) := by rw [Prod.mk.eta]
            _ = g ((g⁻¹ (0, w)).1, 0) + g (0, (g⁻¹ (0, w)).2) :=
                apply_prod_eq g _ _
            _ = ((g⁻¹ (0, w)).1, 0) + g (0, (g⁻¹ (0, w)).2) := by
                rw [hg1 (g⁻¹ (0, w)).1]
      rw [hdec] at hx
      have h2 := congrArg Prod.snd hx
      simpa [hg2] using h2

variable (k VJ V₀) in
@[expose] def modelA2 : Subgroup (SpecialLinearGroup k (VJ × V₀)) where
  carrier := {g | (∀ w, g (0, w) = (0, w)) ∧ ∀ v, (g (v, 0)).1 = v}
  mul_mem' := by
    rintro g h ⟨hg1, hg2⟩ ⟨hh1, hh2⟩
    refine ⟨fun w => ?_, fun v => ?_⟩
    · rw [sl_mul_apply, hh1 w, hg1 w]
    · have hh : h (v, 0) = (v, (h (v, 0)).2) := by
        rw [← Prod.mk.eta (p := h (v, 0)), hh2 v]
      rw [sl_mul_apply, hh, apply_prod_eq g v (h (v, 0)).2, hg1 (h (v, 0)).2]
      simp [hg2 v]
  one_mem' := ⟨fun w => rfl, fun v => rfl⟩
  inv_mem' := by
    rintro g ⟨hg1, hg2⟩
    refine ⟨fun w => ?_, fun v => ?_⟩
    · have h := sl_inv_apply_apply g (0, w)
      rwa [hg1 w] at h
    · have hx := sl_apply_inv_apply g (v, 0)
      have hdec : g (g⁻¹ (v, 0)) =
          g ((g⁻¹ (v, 0)).1, 0) + (0, (g⁻¹ (v, 0)).2) := by
        calc g (g⁻¹ (v, 0))
            = g ((g⁻¹ (v, 0)).1, (g⁻¹ (v, 0)).2) := by rw [Prod.mk.eta]
            _ = g ((g⁻¹ (v, 0)).1, 0) + g (0, (g⁻¹ (v, 0)).2) :=
                apply_prod_eq g _ _
            _ = g ((g⁻¹ (v, 0)).1, 0) + (0, (g⁻¹ (v, 0)).2) := by
                rw [hg1 (g⁻¹ (v, 0)).2]
      rw [hdec] at hx
      have h2 := congrArg Prod.fst hx
      simpa [hg2] using h2

variable (k VJ V₀) in
@[expose] def modelP1 : Subgroup (SpecialLinearGroup k (VJ × V₀)) where
  carrier := {g | (∀ v, (g (v, 0)).2 = 0) ∧ ∀ w, (g (0, w)).2 = w}
  mul_mem' := by
    rintro g h ⟨hg1, hg2⟩ ⟨hh1, hh2⟩
    refine ⟨fun v => ?_, fun w => ?_⟩
    · have hh : h (v, 0) = ((h (v, 0)).1, 0) := by
        rw [← Prod.mk.eta (p := h (v, 0)), hh1 v]
      rw [sl_mul_apply, hh, hg1]
    · have hh : h (0, w) = ((h (0, w)).1, w) := by
        rw [← Prod.mk.eta (p := h (0, w)), hh2 w]
      rw [sl_mul_apply, hh, apply_prod_eq g (h (0, w)).1 w]
      simp [hg1, hg2]
  one_mem' := ⟨fun v => rfl, fun w => rfl⟩
  inv_mem' := by
    rintro g ⟨hg1, hg2⟩
    refine ⟨fun v => ?_, fun w => ?_⟩
    · have hx := sl_apply_inv_apply g (v, 0)
      have hdec : g (g⁻¹ (v, 0)) =
          g ((g⁻¹ (v, 0)).1, 0) + g (0, (g⁻¹ (v, 0)).2) := by
        calc g (g⁻¹ (v, 0))
            = g ((g⁻¹ (v, 0)).1, (g⁻¹ (v, 0)).2) := by rw [Prod.mk.eta]
            _ = g ((g⁻¹ (v, 0)).1, 0) + g (0, (g⁻¹ (v, 0)).2) :=
                apply_prod_eq g _ _
      rw [hdec] at hx
      have h2 := congrArg Prod.snd hx
      simpa [hg1, hg2] using h2
    · have hx := sl_apply_inv_apply g (0, w)
      have hdec : g (g⁻¹ (0, w)) =
          g ((g⁻¹ (0, w)).1, 0) + g (0, (g⁻¹ (0, w)).2) := by
        calc g (g⁻¹ (0, w))
            = g ((g⁻¹ (0, w)).1, (g⁻¹ (0, w)).2) := by rw [Prod.mk.eta]
            _ = g ((g⁻¹ (0, w)).1, 0) + g (0, (g⁻¹ (0, w)).2) :=
                apply_prod_eq g _ _
      rw [hdec] at hx
      have h2 := congrArg Prod.snd hx
      simpa [hg1, hg2] using h2

variable (k VJ V₀) in
@[expose] def modelP2 : Subgroup (SpecialLinearGroup k (VJ × V₀)) where
  carrier := {g | ∀ w, g (0, w) = (0, w)}
  mul_mem' := by
    rintro g h hg hh w
    rw [sl_mul_apply, hh w, hg w]
  one_mem' := fun w => rfl
  inv_mem' := by
    rintro g hg w
    have h := sl_inv_apply_apply g (0, w)
    rwa [hg w] at h

@[expose] def modelA1Elt (φ : V₀ →ₗ[k] VJ) : SpecialLinearGroup k (VJ × V₀) :=
  ⟨{ toFun := fun p => (p.1 + φ p.2, p.2)
     invFun := fun p => (p.1 - φ p.2, p.2)
     map_add' := by
       rintro ⟨v, w⟩ ⟨v', w'⟩
       refine Prod.ext ?_ rfl
       show v + v' + φ (w + w') = v + φ w + (v' + φ w')
       rw [map_add]
       abel
     map_smul' := by
       intro c p
       refine Prod.ext ?_ rfl
       simp [smul_add]
     left_inv := by
       intro p
       refine Prod.ext ?_ rfl
       show p.1 + φ p.2 - φ p.2 = p.1
       rw [add_sub_cancel_right]
     right_inv := by
       intro p
       refine Prod.ext ?_ rfl
       show p.1 - φ p.2 + φ p.2 = p.1
       rw [sub_add_cancel] }, by
    apply Units.ext
    rw [LinearEquiv.coe_det, Units.val_one]
    let N : (VJ × V₀) →ₗ[k] (VJ × V₀) :=
      { toFun := fun p => (φ p.2, 0)
        map_add' := by intro p q; ext <;> simp
        map_smul' := by intro c p; ext <;> simp }
    have hN : N * N = 0 := by
      apply LinearMap.ext
      intro p
      exact Prod.ext (by simp [N]) (by simp [N])
    refine (congrArg LinearMap.det ?_).trans (det_one_add_of_sq_zero N hN)
    apply LinearMap.ext
    intro p
    exact Prod.ext (by simp [N]) (by simp [N])⟩

@[expose] def modelA2Elt (ψ : VJ →ₗ[k] V₀) : SpecialLinearGroup k (VJ × V₀) :=
  ⟨{ toFun := fun p => (p.1, p.2 + ψ p.1)
     invFun := fun p => (p.1, p.2 - ψ p.1)
     map_add' := by
       rintro ⟨v, w⟩ ⟨v', w'⟩
       refine Prod.ext rfl ?_
       show (w + w') + ψ (v + v') = (w + ψ v) + (w' + ψ v')
       rw [map_add]
       abel
     map_smul' := by
       intro c p
       refine Prod.ext rfl ?_
       simp [smul_add]
     left_inv := by
       intro p
       refine Prod.ext rfl ?_
       show p.2 + ψ p.1 - ψ p.1 = p.2
       rw [add_sub_cancel_right]
     right_inv := by
       intro p
       refine Prod.ext rfl ?_
       show p.2 - ψ p.1 + ψ p.1 = p.2
       rw [sub_add_cancel] }, by
    apply Units.ext
    rw [LinearEquiv.coe_det, Units.val_one]
    let N : (VJ × V₀) →ₗ[k] (VJ × V₀) :=
      { toFun := fun p => (0, ψ p.1)
        map_add' := by intro p q; ext <;> simp
        map_smul' := by intro c p; ext <;> simp }
    have hN : N * N = 0 := by
      apply LinearMap.ext
      intro p
      exact Prod.ext (by simp [N]) (by simp [N])
    refine (congrArg LinearMap.det ?_).trans (det_one_add_of_sq_zero N hN)
    apply LinearMap.ext
    intro p
    exact Prod.ext (by simp [N]) (by simp [N])⟩

variable (k V₀) in
@[expose] def modelIota (e₀ : VJ) : E →ₗ[k] (VJ × V₀) :=
  LinearMap.inl k VJ V₀ ∘ₗ ((LinearMap.toSpanSingleton E VJ e₀).restrictScalars k)

variable (k V₀) in
@[expose] def modelPi (l₀ : VJ →ₗ[E] E) : (VJ × V₀) →ₗ[k] E :=
  l₀.restrictScalars k ∘ₗ LinearMap.fst k VJ V₀

@[expose] def diagE (s : Eˣ) : (VJ × V₀) ≃ₗ[k] (VJ × V₀) where
  toFun p := ((s : E) • p.1, p.2)
  invFun p := (((s⁻¹ : Eˣ) : E) • p.1, p.2)
  map_add' := by
    intro p q
    refine Prod.ext ?_ rfl
    simp [smul_add]
  map_smul' := by
    intro c p
    refine Prod.ext ?_ rfl
    exact (smul_comm c (s : E) p.1).symm
  left_inv := by
    intro p
    refine Prod.ext ?_ rfl
    show ((s⁻¹ : Eˣ) : E) • ((s : E) • p.1) = p.1
    rw [smul_smul, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_smul]
  right_inv := by
    intro p
    refine Prod.ext ?_ rfl
    show (s : E) • (((s⁻¹ : Eˣ) : E) • p.1) = p.1
    rw [smul_smul, ← Units.val_mul, mul_inv_cancel, Units.val_one, one_smul]

@[expose] def diagY (y : V₀ ≃ₗ[k] V₀) : (VJ × V₀) ≃ₗ[k] (VJ × V₀) :=
  LinearEquiv.prodCongr (LinearEquiv.refl k VJ) y

variable (k E VJ V₀) in
@[expose] def diagEHom : Eˣ →* ((VJ × V₀) ≃ₗ[k] (VJ × V₀)) where
  toFun := diagE
  map_one' := by
    ext p <;> simp [diagE]
  map_mul' s s' := by
    ext p <;> simp [diagE, Units.val_mul, smul_smul]

variable (k VJ V₀) in
@[expose] def diagYHom : (V₀ ≃ₗ[k] V₀) →* ((VJ × V₀) ≃ₗ[k] (VJ × V₀)) where
  toFun := diagY
  map_one' := by
    ext p <;> simp [diagY]
  map_mul' y y' := by
    ext p <;> simp [diagY]

end CFSG.LinearAlgebra.RootGroupSL
